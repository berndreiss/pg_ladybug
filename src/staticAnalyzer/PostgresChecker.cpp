//== PostgresChecker.cpp ------------------------------*- C++ -*--==//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines PostgresChecker, which is a ...
//
//===----------------------------------------------------------------------===//

#include "clang/StaticAnalyzer/Frontend/CheckerRegistry.h"
#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ExprEngine.h"
#include <clang/AST/Decl.h>
#include <clang/AST/Expr.h>
#include <clang/Analysis/PathDiagnostic.h>
#include <clang/Analysis/ProgramPoint.h>
#include <clang/Basic/LLVM.h>
#include <clang/Basic/SourceLocation.h>
#include <clang/Basic/SourceManager.h>
#include <clang/StaticAnalyzer/Core/BugReporter/BugReporter.h>
#include <clang/StaticAnalyzer/Core/PathSensitive/ExplodedGraph.h>
#include <clang/StaticAnalyzer/Core/PathSensitive/MemRegion.h>
#include <clang/StaticAnalyzer/Core/PathSensitive/ProgramState_Fwd.h>
#include <clang/StaticAnalyzer/Core/PathSensitive/SVals.h>
#include <clang/StaticAnalyzer/Core/PathSensitive/SymExpr.h>
#include <llvm/ADT/StringMap.h>
#include <llvm/Object/ObjectFile.h>
#include <llvm/Support/raw_ostream.h>
#include <memory>
#include <string>

using namespace clang;
using namespace ento;

struct DependencyInfo;
enum Category {Strict, Dependent, Arbitrary};

namespace{
class PostgresChecker :
    public Checker<check::PreCall, check::PostCall, check::Location> {
  mutable std::unique_ptr<BugType> BT_Free_Strict;
  mutable std::unique_ptr<BugType> BT_Free_Dependent;
  mutable std::unique_ptr<BugType> BT_Free_Arbitrary;

public:
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
  void checkLocation(SVal l, bool isLoad, const Stmt *S, CheckerContext &C) const;
  bool checkUseAfterFree(SymbolRef Sym, CheckerContext &C, const Stmt * S) const;
private:
  void HandleFree(const CallEvent &Call, CheckerContext &C, Category Cat) const;
  void HandleStrictFree(const CallEvent &Call, CheckerContext &C) const;
  void HandleDependentFree(const CallEvent &Call, CheckerContext &C, DependencyInfo DI) const;
  void HandleArbitraryFree(const CallEvent &Call, CheckerContext &C, std::string Str) const;
  void HandleUseAfterFree(CheckerContext &C, SourceRange Range,
                          SymbolRef Sym, Category Cat) const;
  void HandleDoubleFree(CheckerContext &C, SourceRange Range, bool Released,
                        SymbolRef Sym, SymbolRef PrevSym, Category Cat) const;
  void emitReport(SymbolRef Sym, BugType *BT, CheckerContext &C, std::string message) const;

};
} // end of anonymous namespace
namespace {
class RefState {
  enum Kind {
    // Reference to released/freed memory.
    Released,
    // Possilbe reference to released/freed memory.
    PossiblyReleased,
    // The responsibility for freeing resources has transferred from
    // this reference. A relinquished symbol should not be freed.
    // TODO HOW TO HANDLE THIS?
    Relinquished,
    // We are no longer guaranteed to have observed all manipulations
    // of this pointer/memory. For example, it could have been
    // passed as a parameter to an opaque function.
    // TODO HOW TO HANDLE THIS?
    Escaped
  };

  const Stmt *S;

  Kind K;

  ExplodedNode *EN;

  const FunctionDecl *FD;

  RefState(Kind k, const Stmt *s, ExplodedNode *EN, const FunctionDecl *FD)
      : S(s), K(k), EN(EN), FD(FD) {}

public:
  bool isReleased() const { return K == Released; }
  bool isPossiblyReleased() const { return K == PossiblyReleased; }
  bool isRelinquished() const { return K == Relinquished; }
  bool isEscaped() const { return K == Escaped; }
  const Stmt *getStmt() const { return S; }
  const FunctionDecl *getFunction() const { return FD; }
  ExplodedNode *getNode() const { return EN; }

  bool operator==(const RefState &X) const {
    return K == X.K && S == X.S;
  }

  static RefState getReleased(const Stmt *s, ExplodedNode *EN, const FunctionDecl *FD) {
    return RefState(Released, s, EN, FD);
  }
  static RefState getPossiblyReleased(const Stmt *s, ExplodedNode *EN, const FunctionDecl *FD) {
    return RefState(PossiblyReleased, s, EN, FD);
  }
  static RefState getRelinquished(const Stmt *s, ExplodedNode *EN, const FunctionDecl *FD) {
    return RefState(Relinquished, s, EN, FD);
  }
  static RefState getEscaped(const RefState *RS, ExplodedNode *EN, const FunctionDecl *FD) {
    return RefState(Escaped, RS->getStmt(), EN, FD);
  }

  
  void Profile(llvm::FoldingSetNodeID &ID) const {
    ID.AddInteger(K);
    ID.AddPointer(S);
    ID.AddPointer(EN);
    ID.AddPointer(FD);
  }

  LLVM_DUMP_METHOD void dump(raw_ostream &OS) const {
    switch (K) {
#define CASE(ID) case ID: OS << #ID; break;
    CASE(Released)
    CASE(PossiblyReleased)
    CASE(Relinquished)
    CASE(Escaped)
    }
  }

  LLVM_DUMP_METHOD void dump() const { dump(llvm::errs()); }

};
} // end of anonymous namespace

REGISTER_MAP_WITH_PROGRAMSTATE(RegionState, SymbolRef, RefState)

static bool isReleased(SymbolRef Sym, CheckerContext &C);

struct DependencyInfo{
  std::string freeType;
  std::string argName;
  std::function<bool(void *)> isFreeing;

  DependencyInfo(const std::string& ft, const std::string& an, std::function<bool(void *)> f)
    : freeType(ft), argName(an), isFreeing(f) {}
};

llvm::StringMap<std::string> StrictMap{
  {{"pfree"}, {"void *"}}
};

llvm::StringMap<DependencyInfo> DendentMap{
  {"dependent", DependencyInfo("char *", "a", [](void *x){return *static_cast<int*>(x) > 5;})}};

llvm::StringMap<std::string> ArbitraryMap{
  {"arbitrary", "Some info"}
};

void PostgresChecker::HandleUseAfterFree(CheckerContext &C, SourceRange Range,
                          SymbolRef Sym, Category Cat) const{

  BugType *BT;
  std::string message;
  switch(Cat){
    case (Strict):
      message = "Attempt to use released memory";
      if (!BT_Free_Strict)
        BT_Free_Strict.reset(new BugType(this, message));
      BT = BT_Free_Strict.get();
      
    break;
    case (Dependent):
    break;
    case (Arbitrary):
    break;

  }

  emitReport(Sym, BT, C, message);
}

  void PostgresChecker::HandleDoubleFree(CheckerContext &C, SourceRange Range, bool Released,
                        SymbolRef Sym, SymbolRef PrevSym, Category Cat) const{

  BugType *BT;
  std::string message;
  switch(Cat){
    case (Strict):
      message = "Attempt to free released memory";
      if (!BT_Free_Strict)
        BT_Free_Strict.reset(new BugType(this, message));
      BT = BT_Free_Strict.get();
      
    break;
    case (Dependent):
    break;
    case (Arbitrary):
    break;

  }

  emitReport(Sym, BT, C, message);
}

void PostgresChecker::checkPreCall(const CallEvent &Call, CheckerContext &C) const {

  
  const FunctionDecl *FD = dyn_cast_or_null<FunctionDecl>(Call.getDecl());
  if (!FD)
    return;

  if (FD->getNameAsString() == "pfree")
    return;


  for (unsigned I = 0, E = Call.getNumArgs(); I != E; ++I) {
    SVal ArgSVal = Call.getArgSVal(I);
    if (isa<Loc>(ArgSVal)) {
      SymbolRef Sym = ArgSVal.getAsSymbol();
      if (!Sym)
        continue;
      if (checkUseAfterFree(Sym, C, Call.getArgExpr(I)))
        const auto *CE = dyn_cast_or_null<CallExpr>(Call.getOriginExpr());
    }
  }

}

void PostgresChecker::HandleStrictFree(const CallEvent &Call, CheckerContext &C) const{
  HandleFree(Call, C, Strict);
}
void PostgresChecker::HandleDependentFree(const CallEvent &Call, CheckerContext &C, DependencyInfo DI) const{
  HandleFree(Call, C, Dependent);
}
void PostgresChecker::HandleArbitraryFree(const CallEvent &Call, CheckerContext &C, std::string Str) const{
  HandleFree(Call, C, Arbitrary);
}
void PostgresChecker::HandleFree(const CallEvent &Call, CheckerContext &C, Category Cat) const{

  ProgramStateRef State = C.getState();
  
   if (!State)
    return;

  SVal ArgVal =  C.getSVal(Call.getArgExpr(0));
  if (!isa<DefinedOrUnknownSVal>(ArgVal))
    return;

  DefinedOrUnknownSVal location = ArgVal.castAs<DefinedOrUnknownSVal>();
  if (!isa<Loc>(location))
    return;
  // The explicit NULL case, no operation is performed.
  ProgramStateRef notNullState, nullState;
  std::tie(notNullState, nullState) = State->assume(location);
  if (nullState && !notNullState)
    return;

  // Unknown values could easily be okay
  // Undefined values are handled elsewhere
  if (ArgVal.isUnknownOrUndef())
    return;
   const MemRegion *R = ArgVal.getAsRegion();
  const Expr *ParentExpr = Call.getOriginExpr();

  if (!R)
    return;
  R = R->StripCasts();

  //DO WE NEED THIS?
    // Blocks might show up as heap data, but should not be free()d
  //if (isa<BlockDataRegion>(R)) {
  //HandleNonHeapDealloc(C, ArgVal, ArgExpr->getSourceRange(), ParentExpr,
      //                   Family);
    //return nullptr;
  //}
  
  //DO WE NEED THIS?
   //const MemSpaceRegion *MS = R->getMemorySpace();

  // Parameters, locals, statics, globals, and memory returned by
  // __builtin_alloca() shouldn't be freed.
  //if (!isa<UnknownSpaceRegion, HeapSpaceRegion>(MS)) {
    // Regions returned by malloc() are represented by SymbolicRegion objects
    // within HeapSpaceRegion. Of course, free() can work on memory allocated
    // outside the current function, so UnknownSpaceRegion is also a
    // possibility here.

    //if (isa<AllocaRegion>(R))
      //HandleFreeAlloca(C, ArgVal, ArgExpr->getSourceRange());
    //else
      //HandleNonHeapDealloc(C, ArgVal, ArgExpr->getSourceRange(), ParentExpr,
                           //Family);

    //return nullptr;
  //}

  

  const SymbolicRegion *SrBase = dyn_cast<SymbolicRegion>(R->getBaseRegion());
  // Various cases could lead to non-symbol values here.
  // For now, ignore them.
  if (!SrBase)
    return;

  SymbolRef SymBase = SrBase->getSymbol();

  const RefState *RsBase = State->get<RegionState>(SymBase);
  SymbolRef PreviousRetStatusSymbol = nullptr;


  if (RsBase){
    // Check for double free
    if (RsBase->isReleased() || RsBase->isRelinquished()){
        HandleDoubleFree(C, ParentExpr->getSourceRange(), RsBase->isReleased(), SymBase, PreviousRetStatusSymbol, Strict);
      return;
    }
  }
  ExplodedNode * EN = C.generateNonFatalErrorNode();

  const FunctionDecl *FD = dyn_cast_or_null<FunctionDecl>(Call.getDecl());

  State = State->set<RegionState>(SymBase, RefState::getReleased(ParentExpr, EN, FD));

  C.addTransition(State);
}

void PostgresChecker::checkPostCall(const CallEvent &Call,
                                  CheckerContext &C) const {
  if (C.wasInlined)
    return;
  if (!Call.getOriginExpr())
    return;

  ProgramStateRef State = C.getState();

  const FunctionDecl *FD = dyn_cast_or_null<FunctionDecl>(Call.getDecl());
  if (!FD)
    return;

  if (FD->getName() == "pfree"){
    HandleFree(Call, C, Strict);
    return;
  }
}



bool PostgresChecker::checkUseAfterFree(SymbolRef Sym, CheckerContext &C, const Stmt * S) const{
  if (isReleased(Sym, C)) {
    HandleUseAfterFree(C, S->getSourceRange(), Sym, Strict);
    return true;
  }
  return false;
}

static bool isReleased(SymbolRef Sym, CheckerContext &C) {
  assert(Sym);
  const RefState *RS = C.getState()->get<RegionState>(Sym);
  if (!RS)
    return false;
  return (RS && RS->isReleased());
}

// Check if the location is a freed symbolic region.
void PostgresChecker::checkLocation(SVal l, bool isLoad, const Stmt *S,
                                  CheckerContext &C) const {

  if (l.getAs<Loc>()){
    const MemRegion *MR = l.getAsRegion();
    if (MR){
      if (const VarRegion *VR = dyn_cast<VarRegion>(MR->getBaseRegion())){
        const VarDecl *VD = VR->getDecl();
      const SymbolicRegion *SrBase = dyn_cast<SymbolicRegion>(MR->getBaseRegion());
      if (SrBase){
         SymbolRef SymBase = SrBase->getSymbol();

      }
  }
    }
  }
  SymbolRef Sym = l.getLocSymbolInBase();
  if (Sym){
    checkUseAfterFree(Sym, C, S);
  }
}


void PostgresChecker::emitReport(SymbolRef Sym, BugType *BT, CheckerContext &C, std::string message) const{
  ExplodedNode *N = C.generateNonFatalErrorNode(C.getState(), this);
  //ExplodedNode *N = C.generateErrorNode(C.getState(), this);
  if (!N)
    return;
  auto R = std::make_unique<PathSensitiveBugReport>(*BT, message, N);
  const RefState *RS = C.getState()->get<RegionState>(Sym);

  if (!RS)
    return;
  PathDiagnosticLocation PDLoc = PathDiagnosticLocation::createBegin(
    C.getState()->get<RegionState>(Sym)->getStmt(),
    C.getSourceManager(),
    C.getLocationContext()
  ); 
  const FunctionDecl *FD = RS->getFunction();
  R->addNote("Freeing function" + (FD ? (": " + FD->getNameAsString()) : ""), PDLoc);
  C.emitReport(std::move(R));
  
}

namespace clang {
namespace ento {
// Register plugin!
void registerPostgresChecker(CheckerManager &mgr) {
  mgr.registerChecker<PostgresChecker>();
}//namespace postgres

bool shouldRegisterPostgresChecker(const CheckerManager &mgr) {
  return true;
}
extern "C" void clang_registerCheckers(CheckerRegistry &registry) {
  registry.addChecker<PostgresChecker>(
      "postgres.PostgresChecker",
      "Checks for use-after-free and double-free in PostgreSQL",
      "");
}
extern "C"
const char clang_analyzerAPIVersionString[] = CLANG_ANALYZER_API_VERSION_STRING;

} // namespace ento
} // namespace clang

