//Realloc -> 0 might free memory
//std::tie(StateNull, StateNonNull) = needs to be incorporated for the following test case:
//
//void reallocSizeZero2(void) {
  //char *p = palloc(12);
  //char *r = repalloc(p, 0);
  //if (!r) {
    //pfree(p); // expected-warning {{Attempt to free released memory}}
  //} else {
    //pfree(r);
  //}
  //pfree(p); // expected-warning {{Attempt to free released memory}}
//}

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
#include <clang/AST/Stmt.h>
#include <clang/Analysis/PathDiagnostic.h>
#include <clang/Analysis/ProgramPoint.h>
#include <clang/Basic/LLVM.h>
#include <clang/Basic/SourceLocation.h>
#include <clang/Basic/SourceManager.h>
#include <clang/StaticAnalyzer/Core/BugReporter/BugReporter.h>
#include <clang/StaticAnalyzer/Core/PathSensitive/ConstraintManager.h>
#include <clang/StaticAnalyzer/Core/PathSensitive/ExplodedGraph.h>
#include <clang/StaticAnalyzer/Core/PathSensitive/MemRegion.h>
#include <clang/StaticAnalyzer/Core/PathSensitive/ProgramState_Fwd.h>
#include <clang/StaticAnalyzer/Core/PathSensitive/SVals.h>
#include <clang/StaticAnalyzer/Core/PathSensitive/SymExpr.h>
#include <llvm/ADT/APSInt.h>
#include <llvm/ADT/StringMap.h>
#include <llvm/Object/ObjectFile.h>
#include <llvm/Support/Casting.h>
#include <llvm/Support/raw_ostream.h>
#include <memory>
#include <optional>
#include <string>


using namespace clang;
using namespace ento;

struct DependencyInfo;
enum Category {Strict, Dependent, Arbitrary};
enum Tristate {True, False, Undefined};

namespace{
class PostgresChecker :
    public Checker<check::PreCall, check::PostCall, check::Location, check::PreStmt<ReturnStmt>, check::EndFunction> {
  mutable std::unique_ptr<BugType> BT_Free_Strict;
  mutable std::unique_ptr<BugType> BT_Free_Arbitrary;

public:
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
  void checkLocation(SVal l, bool isLoad, const Stmt *S, CheckerContext &C) const;
  void checkPreStmt(const ReturnStmt *S, CheckerContext &C) const;
  void checkEndFunction(const ReturnStmt *S, CheckerContext &C) const;
  bool checkUseAfterFree(SymbolRef Sym, std::string varName, CheckerContext &C, const Stmt * S) const;
private:
  void HandleFree(const CallEvent &Call, CheckerContext &C, Category Cat) const;
  void HandleStrictFree(const CallEvent &Call, CheckerContext &C) const;
  void HandleDependentFree(const CallEvent &Call, CheckerContext &C, DependencyInfo DI) const;
  void HandleArbitraryFree(const CallEvent &Call, CheckerContext &C, std::string Str) const;
  void HandleUseAfterFree(CheckerContext &C, SourceRange Range, SymbolRef Sym,
                          std::string varName, Category Cat) const;
  void HandleDoubleFree(CheckerContext &C, SourceRange Range, SymbolRef Sym, std::string varName, Category FirstFreeCat, Category Cat) const;
  void emitReport(SymbolRef Sym, BugType *BT, CheckerContext &C, std::string message) const;
  void checkEscapeOnReturn(const ReturnStmt *S, CheckerContext &C) const;

};
} // end of anonymous namespace
namespace {
class RefState {
  enum Kind {
    // Reference to released/freed memory.
    Released,
    // Possible reference to released/freed memory.
    PossiblyReleased
  };

  const Stmt *S;
  Kind K;
  ExplodedNode *EN;
  const FunctionDecl *FD;
  std::string OriginalVarName;

  RefState(Kind k, const Stmt *s, ExplodedNode *EN, const FunctionDecl *FD, std::string varName)
      : S(s), K(k), EN(EN), FD(FD), OriginalVarName(varName) {}

public:
  const std::string& getVarName() const { return OriginalVarName; }
  bool isReleased() const { return K == Released; }
  bool isPossiblyReleased() const { return K == PossiblyReleased; }
  const Stmt *getStmt() const { return S; }
  const FunctionDecl *getFunction() const { return FD; }
  ExplodedNode *getNode() const { return EN; }

  bool operator==(const RefState &X) const {
    return K == X.K && S == X.S;
  }

  static RefState getReleased(const Stmt *s, ExplodedNode *EN, const FunctionDecl *FD, std::string varName = "") {
    return RefState(Released, s, EN, FD, varName);
  }
  static RefState getPossiblyReleased(const Stmt *s, ExplodedNode *EN, const FunctionDecl *FD, std::string varName = "") {
    return RefState(PossiblyReleased, s, EN, FD, varName);
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
    }
  }

  LLVM_DUMP_METHOD void dump() const { dump(llvm::errs()); }

};
} // end of anonymous namespace

REGISTER_MAP_WITH_PROGRAMSTATE(RegionStatePG, SymbolRef, RefState)

static bool isReleased(SymbolRef Sym, CheckerContext &C);

// This struct contains information about a dependent function.
struct DependencyInfo{
  // The position of the freed argument 
  int positionFreed;
  // The condition for making this function strict
  std::function<Tristate(CallEvent &, CheckerContext &)> isFreeing;
  // Defines whether the function becomes arbitrary when isFreeing is false
  bool isArbitrary = false;

  // Default constructor
  DependencyInfo() : positionFreed(0), isFreeing([](CallEvent &, CheckerContext &) { return False; }) {}

  DependencyInfo(int positionFreed, bool isArbitrary, std::function<Tristate(CallEvent &, CheckerContext &)> f)
    : positionFreed(positionFreed), isFreeing(f), isArbitrary(isArbitrary) {}
};

llvm::StringMap<int> CMemoryMap{
  {{"free"}, {0}},
  {{"realloc"}, {0}}, 
};

llvm::StringMap<int> StrictMap{
  {{"arabic_UTF_8_close_env"}, {0}},
{{"armenian_UTF_8_close_env"}, {0}},
{{"array_free_iterator"}, {0}},
{{"basque_ISO_8859_1_close_env"}, {0}},
{{"basque_UTF_8_close_env"}, {0}},
{{"binaryheap_free"}, {0}},
{{"BipartiteMatchFree"}, {0}},
{{"BlockRefTableFreeEntry"}, {0}},
{{"bloom_free"}, {0}},
{{"bms_free"}, {0}},
{{"brin_free_tuple"}, {0}},
{{"brinRevmapTerminate"}, {0}},
{{"BufFileClose"}, {0}},
{{"BumpDelete"}, {0}},
{{"catalan_ISO_8859_1_close_env"}, {0}},
{{"catalan_UTF_8_close_env"}, {0}},
{{"CatalogCloseIndexes"}, {0}},
{{"closedir"}, {0}},
{{"close_tsvector_parser"}, {0}},
{{"conditional_stack_destroy"}, {0}},
{{"core_yyfree"}, {0}},
{{"danish_ISO_8859_1_close_env"}, {0}},
{{"danish_UTF_8_close_env"}, {0}},
{{"DeCloneArchive"}, {0}},
{{"DestroyBlockRefTableReader"}, {0}},
{{"DestroyBlockRefTableWriter"}, {0}},
{{"DestroyParallelContext"}, {0}},
{{"destroyPQExpBuffer"}, {0}},
{{"destroyStringInfo"}, {0}},
{{"DestroyTupleQueueReader"}, {0}},
{{"disconnectDatabase"}, {0}},
{{"dsa_detach"}, {0}},
{{"dshash_destroy"}, {0}},
{{"dshash_detach"}, {0}},
{{"dsm_detach"}, {0}},
{{"dutch_ISO_8859_1_close_env"}, {0}},
{{"dutch_UTF_8_close_env"}, {0}},
{{"ecpg_do_epilogue"}, {0}},
{{"ecpg_free"}, {0}},
{{"ECPGfree_type"}, {0}},
{{"EndCompressFileHandle"}, {0}},
{{"EndCompressor"}, {1}},
{{"EndCopyFrom"}, {0}},
{{"EndCopyTo"}, {0}},
{{"end_tup_output"}, {0}},
{{"english_ISO_8859_1_close_env"}, {0}},
{{"english_UTF_8_close_env"}, {0}},
{{"ExecDropSingleTupleTableSlot"}, {0}},
{{"ExecHashTableDestroy"}, {0}},
{{"ExecParallelCleanup"}, {0}},
{{"finnish_ISO_8859_1_close_env"}, {0}},
{{"finnish_UTF_8_close_env"}, {0}},
{{"FreeAccessStrategy"}, {0}},
{{"free_attrmap"}, {0}},
{{"FreeBulkInsertState"}, {0}},
{{"free_chromo"}, {1}},
{{"free_city_table"}, {1}},
{{"free_conversion_map"}, {0}},
{{"free_edge_table"}, {1}},
{{"FreeErrorData"}, {0}},
{{"FreeExprContext"}, {0}},
{{"FreeFakeRelcacheEntry"}, {0}},
{{"freeGinBtreeStack"}, {0}},
{{"free_object_addresses"}, {0}},
{{"free_parsestate"}, {0}},
{{"free_pool"}, {1}},
{{"FreeQueryDesc"}, {0}},
{{"FreeSubscription"}, {0}},
{{"FreeTriggerDesc"}, {0}},
{{"FreeTupleDesc"}, {0}},
{{"FreeWaitEventSet"}, {0}},
{{"FreeWaitEventSetAfterFork"}, {0}},
{{"french_ISO_8859_1_close_env"}, {0}},
{{"french_UTF_8_close_env"}, {0}},
{{"GenerationDelete"}, {0}},
{{"GenericXLogAbort"}, {0}},
{{"GenericXLogFinish"}, {0}},
{{"german_ISO_8859_1_close_env"}, {0}},
{{"german_UTF_8_close_env"}, {0}},
{{"ginInsertValue"}, {1}},
{{"greek_UTF_8_close_env"}, {0}},
{{"guc_free"}, {0}},
{{"heap_free_minimal_tuple"}, {0}},
{{"heap_freetuple"}, {0}},
{{"hindi_UTF_8_close_env"}, {0}},
{{"_h_spooldestroy"}, {0}},
{{"hungarian_ISO_8859_2_close_env"}, {0}},
{{"hungarian_UTF_8_close_env"}, {0}},
{{"index_endscan"}, {0}},
{{"IndexScanEnd"}, {0}},
{{"indonesian_ISO_8859_1_close_env"}, {0}},
{{"indonesian_UTF_8_close_env"}, {0}},
{{"inv_close"}, {0}},
{{"irish_ISO_8859_1_close_env"}, {0}},
{{"irish_UTF_8_close_env"}, {0}},
{{"italian_ISO_8859_1_close_env"}, {0}},
{{"italian_UTF_8_close_env"}, {0}},
{{"jit_release_context"}, {0}},
{{"json_parse_manifest_incremental_shutdown"}, {0}},
{{"jsonpath_yyfree"}, {0}},
{{"list_free"}, {0}},
{{"list_free_deep"}, {0}},
{{"lithuanian_UTF_8_close_env"}, {0}},
{{"LogicalTapeClose"}, {0}},
{{"LogicalTapeSetClose"}, {0}},
{{"mbuf_free"}, {0}},
{{"nepali_UTF_8_close_env"}, {0}},
{{"norwegian_ISO_8859_1_close_env"}, {0}},
{{"norwegian_UTF_8_close_env"}, {0}},
{{"output_deallocate_prepare_statement"}, {0}},
{{"output_prepare_statement"}, {0}},
{{"output_simple_statement"}, {0}},
{{"output_statement"}, {0}},
{{"PageRestoreTempPage"}, {0}},
{{"pairingheap_free"}, {0}},
{{"parallel_vacuum_end"}, {0}},
{{"pfree"}, {0}},
{{"pgfnames_cleanup"}, {0}},
{{"pg_free"}, {0}},
{{"pgp_cfb_free"}, {0}},
{{"pgp_free"}, {0}},
{{"pgp_key_free"}, {0}},
{{"pgp_mpi_free"}, {0}},
{{"PGTYPESchar_free"}, {0}},
{{"PGTYPESdate_free"}, {0}},
{{"PGTYPESdecimal_free"}, {0}},
{{"PGTYPESinterval_free"}, {0}},
{{"PGTYPESnumeric_free"}, {0}},
{{"pg_tzenumerate_end"}, {0}},
{{"pg_xml_done"}, {0}},
{{"PortalDrop"}, {0}},
{{"porter_ISO_8859_1_close_env"}, {0}},
{{"porter_UTF_8_close_env"}, {0}},
{{"portuguese_ISO_8859_1_close_env"}, {0}},
{{"portuguese_UTF_8_close_env"}, {0}},
{{"PQconninfoFree"}, {0}},
{{"PQfinish"}, {0}},
{{"PQfreeCancel"}, {0}},
{{"PQfreemem"}, {0}},
{{"PQfreeNotify"}, {0}},
{{"psql_scan_destroy"}, {0}},
{{"pullf_free"}, {0}},
{{"pushf_free"}, {0}},
{{"pushf_free_all"}, {0}},
{{"QTNFree"}, {0}},
{{"read_stream_end"}, {0}},
{{"ReorderBufferReturnChange"}, {1}},
{{"ReorderBufferReturnRelids"}, {1}},
{{"ReorderBufferReturnTupleBuf"}, {0}},
{{"ResourceOwnerDelete"}, {0}},
{{"restorePsetInfo"}, {1}},
{{"romanian_ISO_8859_2_close_env"}, {0}},
{{"romanian_UTF_8_close_env"}, {0}},
{{"russian_KOI8_R_close_env"}, {0}},
{{"russian_UTF_8_close_env"}, {0}},
{{"serbian_UTF_8_close_env"}, {0}},
{{"shm_mq_detach"}, {0}},
{{"SlabDelete"}, {0}},
{{"SN_close_env"}, {0}},
{{"spanish_ISO_8859_1_close_env"}, {0}},
{{"spanish_UTF_8_close_env"}, {0}},
{{"SPI_cursor_close"}, {0}},
{{"SPI_freetuple"}, {0}},
{{"SPI_pfree"}, {0}},
{{"swedish_ISO_8859_1_close_env"}, {0}},
{{"swedish_UTF_8_close_env"}, {0}},
{{"systable_endscan"}, {0}},
{{"systable_endscan_ordered"}, {0}},
{{"tamil_UTF_8_close_env"}, {0}},
{{"tbm_end_iterate"}, {0}},
{{"tbm_end_shared_iterate"}, {0}},
{{"tbm_free"}, {0}},
{{"TidStoreDestroy"}, {0}},
{{"TidStoreDetach"}, {0}},
{{"TidStoreEndIterate"}, {0}},
{{"toast_close_indexes"}, {0}},
{{"tuplestore_end"}, {0}},
{{"turkish_UTF_8_close_env"}, {0}},
{{"updateAclDependencies"}, {5}},
{{"updateAclDependencies"}, {7}},
{{"updateInitAclDependencies"}, {4}},
{{"updateInitAclDependencies"}, {6}},
{{"vac_close_indexes"}, {1}},
{{"XLogPrefetcherFree"}, {0}},
{{"XLogReaderFree"}, {0}},
{{"yiddish_UTF_8_close_env"}, {0}},
};


SVal getFieldSVal(CheckerContext &C, SVal val, std::string fieldName){

  ProgramStateRef state = C.getState();
  SValBuilder &SVB = C.getSValBuilder();
  const MemRegion *baseRegion = val.getAsRegion(); // usually a SymbolicRegion or TypedValueRegion

  if (baseRegion == nullptr)
    return UndefinedVal();
  // Usually cast to TypedValueRegion to get the struct type
  const TypedValueRegion *typedRegion = dyn_cast<TypedValueRegion>(baseRegion);
  if (!typedRegion) 
    return UndefinedVal();

  // Get the FieldDecl for tdrefcount
  QualType structType = typedRegion->getValueType();
  const RecordType *recordType = structType->getAsStructureType();
  if (!recordType) 
    return UndefinedVal();

  const RecordDecl *recordDecl = recordType->getDecl();

  for (const FieldDecl *field : recordDecl->fields()) {
    if (field->getNameAsString() == fieldName) {
      const FieldRegion *fieldRegion = C.getSValBuilder().getRegionManager().getFieldRegion(field, typedRegion);
      return state->getSVal(fieldRegion);
    }
  }

  return UndefinedVal();
}
template<typename Comparator>
Tristate checkConcreteInt(SVal SValToCheck, Comparator comparator){
          if (std::optional<nonloc::ConcreteInt> intVal = SValToCheck.getAs<nonloc::ConcreteInt>()) {
            const llvm::APSInt &val = intVal->getValue();
            if (comparator(val))
              return True;
            else
              return False;
          } else {
            return Undefined;
          }
  }

// look for the global OOM_result variable
const VarDecl* getOOMResultDecl(ASTContext &Ctx) {
  TranslationUnitDecl *TU = Ctx.getTranslationUnitDecl();
    
  for (auto *Decl : TU->decls()) 
    if (auto *VD = dyn_cast<VarDecl>(Decl)) 
      if (VD->getName() == "OOM_result") 
        return VD;
    return nullptr;
}

// helper function for debugging SVals
void printSVal(const SVal &sval) {
    if (auto concreteInt = sval.getAs<nonloc::ConcreteInt>()) {
        llvm::errs() << "ConcreteInt: " << concreteInt->getValue() << "\n";
    } else if (auto symbol = sval.getAs<nonloc::SymbolVal>()) {
        llvm::errs() << "SymbolVal: ";
        symbol->getSymbol()->dump();
    } else if (auto loc = sval.getAs<Loc>()) {
        llvm::errs() << "Location: ";
        loc->dump();
    } else if (sval.isUndef()) {
        llvm::errs() << "Undefined\n";
    } else if (sval.isUnknown()) {
        llvm::errs() << "Unknown\n";
    } else {
        llvm::errs() << "Other SVal type\n";
        sval.dump();
    }
}

// map holding all dependent functions -> returns the DependencyInfo
llvm::StringMap<DependencyInfo> DependentMap{
  {"bms_int_members", DependencyInfo(0, true, [](CallEvent &Call, CheckerContext &C){
    if (Call.getNumArgs() < 2) return Undefined;
    SVal val = Call.getArgSVal(1);
    if (val.isUnknownOrUndef()) return Undefined;
    if (val.isZeroConstant()) return True;
    return False;
  })},
  {"bms_replace_members", DependencyInfo(0, true, [](CallEvent &Call, CheckerContext &C){
    if (Call.getNumArgs() < 2) return Undefined;
    SVal val = Call.getArgSVal(1);
    if (val.isUnknownOrUndef()) return Undefined;
    if (val.isZeroConstant()) return True;
    return False;
  })},
  {"DecrTupleDescRefCount", DependencyInfo(0, false, [](CallEvent &Call, CheckerContext &C){
    return False;
    if (Call.getNumArgs() < 1) return Undefined;
    SVal tupdesc = Call.getArgSVal(0);
    SVal fieldVal = getFieldSVal(C, tupdesc, "tdrefcount");
    return checkConcreteInt(fieldVal, [](const llvm::APSInt &a){return a == 1;});
  })},
  {"dump_variables", DependencyInfo(0, false, [](CallEvent &Call, CheckerContext &C){
    if (Call.getNumArgs() < 2) return Undefined;
    SVal mode = Call.getArgSVal(1);
    if (mode.isUnknownOrUndef())
      return Undefined;
    return checkConcreteInt(mode, [](const llvm::APSInt &a){return a !=0;});
  })},
  {"ExecForceStoreMinimalTuple", DependencyInfo(0, false, [](CallEvent &Call, CheckerContext &C){
    if (Call.getNumArgs() < 3) return Undefined;
    SVal shouldFree = Call.getArgSVal(2);
    if (shouldFree.isUnknownOrUndef()) return Undefined;
    Tristate notFreeing = checkConcreteInt(shouldFree, [](const llvm::APSInt &a){return a == 0;});
    if (notFreeing == True) return False;
    return Undefined;
  })},
  {"ExecForceStoreHeapTuple", DependencyInfo(0, false, [](CallEvent &Call, CheckerContext &C){
    if (Call.getNumArgs() < 3) return Undefined;
    SVal shouldFree = Call.getArgSVal(2);
    if (shouldFree.isUnknownOrUndef()) return Undefined;
    Tristate notFreeing = checkConcreteInt(shouldFree, [](const llvm::APSInt &a){return a == 0;});
    if (notFreeing == True) return False;
    return Undefined;
  })},
  {"ExecResetTupleTable", DependencyInfo(0, false, [](CallEvent &Call, CheckerContext &C){
    if (Call.getNumArgs() < 2) return Undefined;
    SVal shouldFree = Call.getArgSVal(1);
    if (shouldFree.isUnknownOrUndef()) return Undefined;
    return checkConcreteInt(shouldFree, [](const llvm::APSInt &a){return a != 0;});
  })},
  {"freeJsonLexContext", DependencyInfo(0, false, [](CallEvent &Call, CheckerContext &C){
    if (Call.getNumArgs() < 1) return Undefined;
    SVal lexContext = Call.getArgSVal(0);
    if (lexContext.isUnknownOrUndef()) return Undefined;
    SVal flags = getFieldSVal(C, lexContext, "flags");
    if (flags.isUnknownOrUndef()) return Undefined;
    return checkConcreteInt(flags, [](const llvm::APSInt &a){return a[0];});
  })},
  //list functions
  //ParallelBackupEnd
  {"pgfdw_report_error", DependencyInfo(1, false, [](CallEvent &Call, CheckerContext &C){
    if (Call.getNumArgs() < 4) return Undefined;
    SVal clear = Call.getArgSVal(3);
    if (clear.isUnknownOrUndef()) return Undefined;
    return checkConcreteInt(clear, [](const llvm::APSInt &a){return a != 0;});
  })},
  {"PQclear", DependencyInfo(0, false, [](CallEvent &Call, CheckerContext &C){
    if (Call.getNumArgs() != 1) return Undefined;
    SVal res = Call.getArgSVal(0);
    if (res.isUnknownOrUndef())
      return Undefined;
    ProgramStateRef State = C.getState();
    if (auto Loc = res.getAs<loc::MemRegionVal>()) {
        const MemRegion *Region = Loc->getRegion();
        // check if this is the OOM_result global variable
        if (auto *VR = dyn_cast<VarRegion>(Region)) 
            if (VR->getDecl()->getName() == "OOM_result") 
                return False;
        if (Region->getKindStr() == "SymbolicRegion")// actual value is not known
          return Undefined;
        return True; // we are confident we freed something
    }
    return Undefined; // we don't know what we are dealing with
  })},
  // SnapBuildSnapDecRefCount
  // UnregisterSnapshotFromOwner
  // UnregisterSnapshot
};

// mapping holding arbitrary functions -> returns the argument being freed/reallocated
llvm::StringMap<int> ArbitraryMap{
{{"add_partial_path"}, {1}},
{{"add_path"}, {1}},
{{"bms_add_member"}, {0}},
{{"bms_add_members"}, {0}},
{{"bms_add_range"}, {0}},
{{"bms_del_member"}, {0}},
{{"bms_del_members"}, {0}},
{{"bms_join"}, {0}},
{{"bms_join"}, {1}},
{{"_bt_doinsert"}, {1}},
{{"CheckAttributeType"}, {3}},
{{"ecpg_check_PQresult"}, {0}},
{{"findsubquery"}, {0}},
{{"FreeDir"}, {0}},
{{"index_close"}, {0}},
{{"InsertPgAttributeTuples"}, {4}},
{{"list_delete"}, {0}},
{{"list_delete_int"}, {0}},
{{"list_delete_oid"}, {0}},
{{"list_delete_ptr"}, {0}},
{{"ParallelSlotsAdoptConn"}, {1}},
{{"pa_xact_finish"}, {0}},
{{"relation_close"}, {0}},
{{"RelationClose"}, {0}},
{{"relation_is_updatable"}, {1}},
{{"relation_is_updatable"}, {3}},
{{"ReleaseCatCacheList"}, {0}},
{{"ReorderBufferQueueChange"}, {3}},
{{"rewrite_heap_tuple"}, {1}},
{{"rewrite_heap_tuple"}, {2}},
{{"sequence_close"}, {0}},
{{"table_close"}, {0}},
{{"TableCommandResultHandler"}, {0}},
};

std::string getNameFromExpression(const Expr * Expr){
  if (Expr) {
    if (const DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(Expr)) {
        if (const ValueDecl *VD = DRE->getDecl()) {
            return VD->getNameAsString();
        }
    }
    else if (const CastExpr *CE = dyn_cast<CastExpr>(Expr)) {
        return getNameFromExpression(CE->getSubExpr());
    }
  }
  return "";
}

void PostgresChecker::HandleUseAfterFree(CheckerContext &C, SourceRange Range,
                          SymbolRef Sym, std::string varName, Category Cat) const{

  BugType *BT;
  std::string message;
  switch(Cat){
    case (Strict):
      message = "Attempt to use released memory";
      if (!BT_Free_Strict)
        BT_Free_Strict.reset(new BugType(this, message));
      BT = BT_Free_Strict.get();
    break;
      //TODO REMOVE??
    //case (Dependent):
    //break;
    case (Arbitrary):
      message = "Attempt to use potentially released memory";
      if (!BT_Free_Arbitrary)
        BT_Free_Arbitrary.reset(new BugType(this, message));
      BT = BT_Free_Arbitrary.get();
    break;
  }
  if (!varName.empty())
    message = message + ": " + varName;
  emitReport(Sym, BT, C, message);
}

void PostgresChecker::HandleDoubleFree(CheckerContext &C, SourceRange Range, SymbolRef Sym, std::string varName, Category FirstFreeCat, Category Cat) const{

  BugType *BT;
  std::string message;
  switch(Cat){
    case (Strict):
      if (FirstFreeCat == Arbitrary)
        message = "Attempt to free potentially released memory";
      else
        message = "Attempt to free released memory";
      if (!BT_Free_Strict)
        BT_Free_Strict.reset(new BugType(this, message));
      BT = BT_Free_Strict.get();
    break;
    case (Dependent):
    break;
    case (Arbitrary):
      if (FirstFreeCat == Arbitrary)
        message = "Possible attempt to free potentially released memory";
      else
        message = "Possible attempt to free released memory";
      if (!BT_Free_Arbitrary)
        BT_Free_Arbitrary.reset(new BugType(this, message));
      BT = BT_Free_Arbitrary.get();
    break;

  }
  if (!varName.empty())
    message = message + ": " + varName;
  emitReport(Sym, BT, C, message);
}

void PostgresChecker::checkPreCall(const CallEvent &Call, CheckerContext &C) const {

  const FunctionDecl *FD = dyn_cast_or_null<FunctionDecl>(Call.getDecl());

  if (!FD)
    return;
  if (FD->hasBody() && FD->getNameAsString() != "free") 
    return;
  if (StrictMap.contains(FD->getNameAsString()) || DependentMap.contains(FD->getNameAsString()) || ArbitraryMap.contains(FD->getNameAsString()) || CMemoryMap.contains(FD->getNameAsString())){

  if (!Call.getOriginExpr())
    return;

  ProgramStateRef State = C.getState();

  //Handle C type functions
  if (CMemoryMap.contains(FD->getName())){
    //TODO handle
    return;
  }
  //Handle strict functions
  if (StrictMap.contains(FD->getName())){
    HandleFree(Call, C, Strict);
    return;
  }
  //Handle dependent functions -> these too will either be resolved to strict or arbitrary cases or do nothing
  if (DependentMap.contains(FD->getName())){
    HandleFree(Call, C, Dependent);
    return;
  }
  //Handle arbitrary functions
  if (ArbitraryMap.contains(FD->getName())){
      HandleFree(Call, C, Arbitrary);
    return;
  }
    return;
  }
  for (unsigned I = 0, E = Call.getNumArgs(); I != E; ++I) {
    SVal ArgSVal = Call.getArgSVal(I);
    if (isa<Loc>(ArgSVal)) {
      SymbolRef Sym = ArgSVal.getAsSymbol();
      if (!Sym)
        continue;
      if (checkUseAfterFree(Sym, getNameFromExpression(Call.getArgExpr(I)), C, Call.getArgExpr(I)))
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

  if (Call.getNumArgs() == 0)
        return;
  const FunctionDecl *FD = dyn_cast_or_null<FunctionDecl>(Call.getDecl());
  if (!FD)
    return;

  ProgramStateRef State = C.getState();
  
  if (!State)
    return;

  SVal ArgVal;
  const Expr *ArgExprFound;
  switch (Cat){
    case (Strict): {
      auto Position = StrictMap.lookup(FD->getName());
      if (Call.getNumArgs()<=Position)
        return;
      const Expr *ArgExpr = Call.getArgExpr(Position);
      if (!ArgExpr)
        return;
      ArgVal = C.getSVal(ArgExpr);
      ArgExprFound = ArgExpr;
      break;
    }
    case (Dependent): {
      auto It = DependentMap.find(FD->getNameAsString());
      if (It != DependentMap.end()) {
        DependencyInfo Info = It->second;
        if (Call.getNumArgs() <= Info.positionFreed)
          return;
          auto result = Info.isFreeing(const_cast<CallEvent &>(Call), C);
          if (result == True){
          //function is freeing
              Cat = Strict;
          } else if (result == False){
            //fall back option
            if (Info.isArbitrary){
              Cat = Arbitrary;
            //function does not free at all
            }
            else
             return;
        } else{
            Cat = Arbitrary;
          }
          const Expr *ArgExpr = Call.getArgExpr(Info.positionFreed);
          if (!ArgExpr)
            return;
          ArgVal = C.getSVal(ArgExpr);
        ArgExprFound = ArgExpr;
        break;
      }
    }
    case (Arbitrary): {
      auto Position = ArbitraryMap.lookup(FD->getName());
      if (Call.getNumArgs()<=Position)
        return;
      const Expr *ArgExpr = Call.getArgExpr(Position);
      if (!ArgExpr)
        return;
      ArgVal = C.getSVal(ArgExpr);
      ArgExprFound = ArgExpr;
      break; // doing this for safety reasons in case enum gets expanded
    }
  }

  if (ArgVal.isUnknownOrUndef())
    return;
   const MemRegion *R = ArgVal.getAsRegion();
  if (!R)
    return;
  const Expr *ParentExpr = Call.getOriginExpr();
  if (!ParentExpr)
    return;

  R = R->StripCasts();

  const SymbolicRegion *SrBase = dyn_cast<SymbolicRegion>(R->getBaseRegion());
  if (!SrBase)
    return;

  SymbolRef SymBase = SrBase->getSymbol();

  const RefState *RsBase = State->get<RegionStatePG>(SymBase);

  if (RsBase){
    // Check for double free
      Category CatFirst = RsBase->isReleased() ? Strict : Arbitrary;
      HandleDoubleFree(C, ParentExpr->getSourceRange(), SymBase, getNameFromExpression(ArgExprFound), CatFirst, Cat);
  }

  // Generate an error node with information about the free location
  // one could argue that for strict functions a fatal error node 
  // should be created, for now sticking to non fatal as MallocChecker
    // also does not treat use-after-free etc. as non fatal
  ExplodedNode * EN = C.generateNonFatalErrorNode();

  if (!EN)
    return;

  std::string VarName = getNameFromExpression(ArgExprFound);

  // Depending on the category of the freeing function set a released or possibly released state
  switch (Cat){
    case Strict:
      State = State->set<RegionStatePG>(SymBase, RefState::getReleased(ParentExpr, EN, FD, VarName));
      break;
    case Dependent:
      break;// We should never get here
    case Arbitrary:
      State = State->set<RegionStatePG>(SymBase, RefState::getPossiblyReleased(ParentExpr, EN, FD, VarName));
      break;
    default:
      return;
  }

  C.addTransition(State);
}

void PostgresChecker::checkPostCall(const CallEvent &Call,
                                  CheckerContext &C) const {
}

void PostgresChecker::checkPreStmt(const ReturnStmt *S,
                                 CheckerContext &C) const {
  checkEscapeOnReturn(S, C);
}

// In the CFG, automatic destructors come after the return statement.
// This callback checks for returning memory that is freed by automatic
// destructors, as those cannot be reached in checkPreStmt().
void PostgresChecker::checkEndFunction(const ReturnStmt *S,
                                     CheckerContext &C) const {
  checkEscapeOnReturn(S, C);
}

void PostgresChecker::checkEscapeOnReturn(const ReturnStmt *S,
                                        CheckerContext &C) const {
  if (!S)
    return;
  const Expr *E = S->getRetValue();
  if (!E)
    return;
  ProgramStateRef State = C.getState();
  SVal RetVal = C.getSVal(E);
  SymbolRef Sym = RetVal.getAsSymbol();
  if (!Sym)
    if (const MemRegion *MR = RetVal.getAsRegion())
      if (isa<FieldRegion, ElementRegion>(MR))
        if (const SymbolicRegion *BMR =
              dyn_cast<SymbolicRegion>(MR->getBaseRegion()))
          Sym = BMR->getSymbol();
  if (Sym)
    checkUseAfterFree(Sym, getNameFromExpression(E), C, E);
}

bool PostgresChecker::checkUseAfterFree(SymbolRef Sym, std::string varName, CheckerContext &C, const Stmt * S) const{
  const RefState *RS = C.getState()->get<RegionStatePG>(Sym);
  if (!RS)
    return false;
  if (RS && RS->isReleased()) {
    HandleUseAfterFree(C, S->getSourceRange(), Sym, varName, Strict);
    return true;
  }
  if (RS && RS->isPossiblyReleased()) {
    HandleUseAfterFree(C, S->getSourceRange(), Sym, varName, Arbitrary);
    return true;
  }
  return false;
}

// check whether the location accessed is a freed symbolic region.
void PostgresChecker::checkLocation(SVal l, bool isLoad, const Stmt *S,
                                  CheckerContext &C) const {

  SymbolRef Sym = l.getLocSymbolInBase();
  if (Sym){
    std::string varName = "";
    if (auto loc = l.getAs<Loc>()) {
    if (const MemRegion *region = loc->getAsRegion()) {
        if (const VarRegion *varRegion = dyn_cast<VarRegion>(region)) {
            const VarDecl *varDecl = varRegion->getDecl();
            varName = varDecl->getNameAsString();
        }
    }
}
    checkUseAfterFree(Sym, varName, C, S);
  }
}


void PostgresChecker::emitReport(SymbolRef Sym, BugType *BT, CheckerContext &C, std::string message) const{
  if (!BT)
    return;
  ExplodedNode *N = C.generateNonFatalErrorNode(C.getState(), this);
  if (!N) 
    return;
  auto R = std::make_unique<PathSensitiveBugReport>(*BT, message, N);
  const RefState *RS = C.getState()->get<RegionStatePG>(Sym);

  if (!RS || !RS->getStmt() || !RS->getFunction())
    return;
  PathDiagnosticLocation PDLoc = PathDiagnosticLocation::createBegin(
    RS->getStmt(),
    C.getSourceManager(),
    C.getLocationContext()
  ); 
  const FunctionDecl *FD = RS->getFunction();
  std::string addition = RS->getVarName().empty() ? "" : (" (" + RS->getVarName() + ")");
  R->addNote("Freeing function" + (FD ? (": " + FD->getNameAsString() + addition) : "<unknown>"), PDLoc);
  C.emitReport(std::move(R));
}

namespace clang {
namespace ento {
void registerPostgresChecker(CheckerManager &mgr) {
  mgr.registerChecker<PostgresChecker>();
}

bool shouldRegisterPostgresChecker(const CheckerManager &mgr) {
  return true;
}
//extern "C" void clang_registerCheckers(CheckerRegistry &registry) {
  //registry.addChecker<PostgresChecker>(
      //"postgres.PostgresChecker",
      //"Checks for use-after-free and double-free in PostgreSQL",
      //"");
//}
//extern "C"
//const char clang_analyzerAPIVersionString[] = CLANG_ANALYZER_API_VERSION_STRING;

} // namespace ento
} // namespace clang

