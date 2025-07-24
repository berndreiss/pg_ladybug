// // Handle	pfree(*pubname);!!!
//== PostgresChecker.cpp ------------------------------*- C++ -*--==//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines PostgresChecker, a checker for memory management related 
// issues when using the PostgreSQL API. It includes checks for use-after-free
// and double-free.
//
// It divides PostgreSQL functions that handle memory into five categories:
//   
//   1. Strict functions: 
//       These functions will always free memory and, therefore, are treated
//       like traditional free functions.
//   2. Dependent functions: 
//       These functions will free memory depending on another parameter.
//       This could, for example, be a boolean 'shouldFree' being passed to the 
//       function, deciding whether another parameter is freed.
//   3. Arbitrary functions:
//       Like dependent functions, the freeing of the parameter is dependent on
//       certain circumstances, which, however, cannot be checked statically.
//   4. Reassigning functions: 
//       Functions like realloc.
//   5. Functions returnign boolean:
//       Functions that always return true or false when a parameter is freed.
//
// The first three categories partition the set of all memory manamgent related
// PostgreSQL functions. For these the checker implements logic similar to the 
// MallocChecker. Categories 4 and 5 are pattern based and only serve to provide 
// better feedback to the developer.
//
//===----------------------------------------------------------------------===//

#include "clang/StaticAnalyzer/Frontend/CheckerRegistry.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include <llvm/Support/raw_ostream.h>

using namespace clang;
using namespace ento;

class PGRefState;
struct DependencyInfo;
enum Category {Strict, Dependent, Arbitrary};
enum Tristate {True, False, Undefined};

namespace{
class PostgresChecker :
    public Checker<check::PreCall, check::Location, check::PreStmt<ReturnStmt>> {
  mutable std::unique_ptr<BugType> BT_Free_Strict;
  mutable std::unique_ptr<BugType> BT_Free_Arbitrary;

public:
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
  void checkLocation(SVal l, bool isLoad, const Stmt *S, 
                     CheckerContext &C) const;
  void checkPreStmt(const ReturnStmt *S, CheckerContext &C) const;
  bool checkUseAfterFree(SymbolRef Sym, std::string varName, 
                         CheckerContext &C, const Stmt * S) const;
private:
  void HandleFree(const CallEvent &Call, CheckerContext &C, 
                        Category Cat) const;
  void HandleUseAfterFree(CheckerContext &C, SourceRange Range, const 
                          PGRefState *RS, std::string varName, 
                          Category Cat) const;
  void HandleDoubleFree(CheckerContext &C, SourceRange Range, 
                        const PGRefState *RS, std::string varName, 
                        Category FirstFreeCat, Category Cat) const;
  void emitReport(const PGRefState *RS, BugType *BT, CheckerContext &C, 
                  std::string message) const;
};
} // end of anonymous namespace

// Map that tracks PGRefStates for symbol references. Entries are defined in the 
// state of the CheckContext and can be accessed on all successive paths.
REGISTER_MAP_WITH_PROGRAMSTATE(RegionStatePG, SymbolRef, PGRefState)

// Storing the state at the function call.
class PGRefState {
  // Keep track of whether the call was strict or arbitrary.
  enum Kind {
    // Reference to released/freed memory.
    Released,
    // Possible reference to released/freed memory.
    PossiblyReleased
  };

  const Stmt *S;
  Kind K;
  const FunctionDecl *FD;
  std::string OriginalVarName;

  PGRefState(Kind k, const Stmt *s, const FunctionDecl *fd, std::string varName)
      : S(s), K(k), FD(fd), OriginalVarName(varName) {}

public:
  const std::string& getVarName() const { return OriginalVarName; }
  bool isReleased() const { return K == Released; }
  bool isPossiblyReleased() const { return K == PossiblyReleased; }
  const Stmt *getStmt() const { return S; }
  const FunctionDecl *getFunction() const { return FD; }

  bool operator==(const PGRefState &X) const {
    return K == X.K && S == X.S && FD == X.FD 
           && OriginalVarName == OriginalVarName;
  }

  static PGRefState getReleased(const Stmt *s, const FunctionDecl *fd, 
                                std::string varName = "") {
    return PGRefState(Released, s, fd, varName);
  }
  static PGRefState getPossiblyReleased(const Stmt *s, 
                                        const FunctionDecl *fd, 
                                        std::string varName = "") {
    return PGRefState(PossiblyReleased, s, fd, varName);
  }
  
  void Profile(llvm::FoldingSetNodeID &ID) const {
    ID.AddInteger(K);
    ID.AddPointer(S);
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

// This map defines standard C memory management functions. We look out for them
// to not get in the way of the MallocChecker.
llvm::StringMap<int> CMemoryMap{
 {{"free"}, {0}},
 {{"realloc"}, {0}}, 
};

// Map representing strict functions: the function names are mapped to the index 
// of the parameter being freed.
llvm::StringMap<unsigned int> StrictMap{
  // C function
  {{"free"}, {0}},
  // PostgreSQL-specific functions
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

// DEFINE HELPER STRUCTURES AND FUNCTIONS FOR THE DEPENDENT MAP

// This struct contains information about a dependent function.
struct DependencyInfo{
  // The position of the freed argument 
  unsigned int positionFreed;
  // The condition for making this function strict
  std::function<Tristate(CallEvent &, CheckerContext &)> isFreeing;
  // Defines whether the function becomes arbitrary when isFreeing is false
  bool isArbitrary = false;

  // Default constructor
  DependencyInfo() : positionFreed(0), isFreeing([](CallEvent &, 
                     CheckerContext &) { return False; }) {}

  DependencyInfo(int positionFreed, bool isArbitrary, 
                 std::function<Tristate(CallEvent &, CheckerContext &)> f)
    : positionFreed(positionFreed), isFreeing(f), isArbitrary(isArbitrary) {}
};

// Method to retrieve a field of a structure represented by the symbolic value 
// via its field name. 
SVal getFieldSVal(CheckerContext &C, SVal val, std::string fieldName){

  ProgramStateRef state = C.getState();
  const MemRegion *baseRegion = val.getAsRegion(); 
  if (baseRegion == nullptr)
    return UndefinedVal();
  // cast to TypedValueRegion to get the struct type
  const TypedValueRegion *typedRegion = dyn_cast<TypedValueRegion>(baseRegion);
  if (!typedRegion) 
    return UndefinedVal();
  // retrieve the type to detec tag type objects like structs and retrieve the
  // declaration of the record
  QualType structType = typedRegion->getValueType();
  const RecordType *recordType = structType->getAsStructureType();
  if (!recordType) 
    return UndefinedVal();
  const RecordDecl *recordDecl = recordType->getDecl();
  if (!recordDecl)
    return UndefinedVal();

  // iterate over the field declarations in the record to find the field
  for (const FieldDecl *field : recordDecl->fields()) {
    // we found it, return the field as a symbolic value
    if (field->getName() == fieldName) {
      const FieldRegion *fieldRegion = C.getSValBuilder().getRegionManager()
                                        .getFieldRegion(field, typedRegion);
      return state->getSVal(fieldRegion);
    }
  }

  // field has not been found
  return UndefinedVal();
}

// Check whether a symbolic value represents a concrete integer and satisfies the
// the conditions defined by the comparator. The comparator should be defined as 
// follows: [](const llvm::ASPInt &x){ condition -> e.g. return x==0; }
template<typename Comparator>
Tristate checkConcreteInt(SVal SValToCheck, Comparator comparator){
  // if the value is a concrete integer, compare it, return Undefined otherwise
  if (std::optional<nonloc::ConcreteInt> intVal = 
                                    SValToCheck.getAs<nonloc::ConcreteInt>()) {
    const llvm::APSInt &val = intVal->getValue();
    if (comparator(val))
      return True;
     else
      return False;
    } else {
      return Undefined;
  }
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

// Map holding all dependent functions: maps function names to DependencyInfo.
// The callback to isFreeing will always extract the parameter the free is 
// dependent on and determine the condition. When the condition can not be 
// determined, Undefined is returned. For clarity reasons beofre every entry a 
// briefly comment descrbes what we check for.
// To better understand what is happening here, it is highly recommended to look
// at the source code of the functions at https://github.com/postgres/postgres or
// https://doxygen.postgresql.org/.
llvm::StringMap<DependencyInfo> DependentMap{
  // 'b == NULL'
  {"bms_int_members", DependencyInfo(0, true, [](CallEvent &Call, 
                                                 CheckerContext &C){
    if (Call.getNumArgs() < 2) return Undefined;
    SVal val = Call.getArgSVal(1);
    if (val.isUnknownOrUndef()) return Undefined;
    if (val.isZeroConstant()) return True;
    return False;
  })},
  // 'b == NULL'
  {"bms_replace_members", DependencyInfo(0, true, [](CallEvent &Call, 
                                                     CheckerContext &C){
    if (Call.getNumArgs() < 2) return Undefined;
    SVal val = Call.getArgSVal(1);
    if (val.isUnknownOrUndef()) return Undefined;
    if (val.isZeroConstant()) return True;
    return False;
  })},
  // 'mode != 0'
  {"dump_variables", DependencyInfo(0, false, [](CallEvent &Call, 
                                                 CheckerContext &C){
    if (Call.getNumArgs() < 2) return Undefined;
    SVal mode = Call.getArgSVal(1);
    if (mode.isUnknownOrUndef())
      return Undefined;
    return checkConcreteInt(mode, [](const llvm::APSInt &a){return a != 0;});
  })},
  // 'shouldFree != 0'
  // never return True -> we can only tell, that the parameter is NOT freed
  // -> if we wanted to check this condition we would have to simulate the tuple
  // creation to check the tuple type, which is possible but not implemented yet
  {"ExecForceStoreMinimalTuple", DependencyInfo(0, false, [](CallEvent &Call, 
                                                             CheckerContext &C){
    if (Call.getNumArgs() < 3) return Undefined;
    SVal shouldFree = Call.getArgSVal(2);
    if (shouldFree.isUnknownOrUndef()) return Undefined;
    Tristate notFreeing = checkConcreteInt(shouldFree, [](const llvm::APSInt &a){
                                                                return a == 0;});
    if (notFreeing == True) return False;
    return Undefined;
  })},
  // 'shouldFree != 0'
  // never return True -> see note in last entry
  {"ExecForceStoreHeapTuple", DependencyInfo(0, false, [](CallEvent &Call, 
                                                          CheckerContext &C){
    if (Call.getNumArgs() < 3) return Undefined;
    SVal shouldFree = Call.getArgSVal(2);
    if (shouldFree.isUnknownOrUndef()) return Undefined;
    Tristate notFreeing = checkConcreteInt(shouldFree, [](const llvm::APSInt &a)
                                                                {return a == 0;});
    if (notFreeing == True) return False;
    return Undefined;
  })},
  // 'shouldFree != 0'
  {"ExecResetTupleTable", DependencyInfo(0, false, [](CallEvent &Call, 
                                                      CheckerContext &C){
    if (Call.getNumArgs() < 2) return Undefined;
    SVal shouldFree = Call.getArgSVal(1);
    if (shouldFree.isUnknownOrUndef()) return Undefined;
    return checkConcreteInt(shouldFree, [](const llvm::APSInt &a){return a != 0;});
  })},
  // 'flags[0] != 0'
  {"freeJsonLexContext", DependencyInfo(0, false, [](CallEvent &Call, 
                                                     CheckerContext &C){
    if (Call.getNumArgs() < 1) return Undefined;
    SVal lexContext = Call.getArgSVal(0);
    if (lexContext.isUnknownOrUndef()) return Undefined;
    SVal flags = getFieldSVal(C, lexContext, "flags");
    if (flags.isUnknownOrUndef()) return Undefined;
    return checkConcreteInt(flags, [](const llvm::APSInt &a){return a[0];});
  })},
  // 'clear != 0'
  {"pgfdw_report_error", DependencyInfo(1, false, [](CallEvent &Call, 
                                                     CheckerContext &C){
    if (Call.getNumArgs() < 4) return Undefined;
    SVal clear = Call.getArgSVal(3);
    if (clear.isUnknownOrUndef()) return Undefined;
    return checkConcreteInt(clear, [](const llvm::APSInt &a){return a != 0;});
  })},
  // '(const PGresult *) res != &OOM_result'
  {"PQclear", DependencyInfo(0, false, [](CallEvent &Call, CheckerContext &C){
    if (Call.getNumArgs() != 1) return Undefined;
    SVal res = Call.getArgSVal(0);
    if (res.isUnknownOrUndef()) return Undefined;
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
  // '*destsz == 0 || lex > *destsz'
  // We never return True since the function is reallocating!
  {"brin_copy_tuple", DependencyInfo(2, false, [](CallEvent &Call,
                                                  CheckerContext &C){
    if (Call.getNumArgs() < 4) return Undefined;
    // get the pointer to destsz
    SVal destszValPtr = Call.getArgSVal(3);
                                      ProgramStateRef State = C.getState();
    // dereference the pointer
    SVal destszVal = State->getSVal(destszValPtr.castAs<Loc>(), 
                                   C.getASTContext().getSizeType());
    if (destszVal.isUnknownOrUndef()) return Undefined;

    // check *destsz == 0
    auto checkDestszResult = checkConcreteInt(
                       destszVal, [](const llvm::APSInt &a){return a == 0;});

    if (checkDestszResult == True || checkDestszResult == Undefined) 
      return Undefined;

    // get len
    SVal lenVal = Call.getArgSVal(1);
    if (lenVal.isUnknownOrUndef()) return Undefined;

    // extract concrete integers and compare them
    std::optional<nonloc::ConcreteInt> lenConcrete = lenVal.getAs<nonloc::ConcreteInt>();
    std::optional<nonloc::ConcreteInt> destszConcrete = destszVal.getAs<nonloc::ConcreteInt>();
    const llvm::APSInt &lenAPS = lenConcrete->getValue();
    const llvm::APSInt &destszAPS = destszConcrete->getValue();
    int cmpResult = lenAPS.compareValues(lenAPS, destszAPS);

    // len > *destsz
    if (cmpResult > 0)
      return Undefined;
    // no reallocation detected
    return False;
  })},
  // WE IGNORE THE REST FOR NOW: the checker will not actually see the values, 
  // associated with the relevant fields, since they involve counting of 
  // characteristics like 'size' that is handled internally. We would have
  // to simulate this behaviour, which is possible but not implemented yet.
  // As is the inclusion of these functions leads to false positives.
  // 'tdrefcount == 1'
  {"DecrTupleDescRefCount", DependencyInfo(0, false, [](CallEvent &Call, 
                                                        CheckerContext &C){
    return False;
  })},
  // 'pstate->numWorkers == 1'
  {"ParallelBackupEnd,ParallelState", DependencyInfo(1, false, [](CallEvent &Call,
                                                               CheckerContext &C){
    return False;
  })},
  // 'snap->active_count == 1'
  {"SnapBuildSnapDecRefcount", DependencyInfo(0, false, [](CallEvent &Call, 
                                                        CheckerContext &C){
    return False;
  })},
  // 'snapshot->regd_count == 0 && snapshot->active_count == 0'
  {"UnregisterSnapshotFromOwner", DependencyInfo(0, false, [](CallEvent &Call, 
                                                        CheckerContext &C){
    return False;
  })},
  // 'snapshot->regd_count == 0 && snapshot->active_count == 0'
  {"UnregisterSnapshot", DependencyInfo(0, false, [](CallEvent &Call, 
                                                        CheckerContext &C){
    return False;
  })},
};

// Map for arbitrary functions: maps the function name to the index being 
// (potentially) freed
llvm::StringMap<unsigned int> ArbitraryMap{
  // C function
  {{"free"}, {0}},
  // PostgreSQL-specific functions
  {{"add_partial_path"}, {1}},
  {{"add_path"}, {1}},
  {{"bms_add_member"}, {0}},
  {{"bms_add_members"}, {0}},
  {{"bms_add_range"}, {0}},
  {{"bms_del_member"}, {0}},
  {{"bms_del_members"}, {0}},
  {{"bms_join"}, {0}},
  {{"bms_join"}, {1}},
  {{"bms_replace_members"}, {0}},
  {{"_bt_doinsert"}, {1}},
  {{"CheckAttributeType"}, {3}},
  {{"core_yyrealloc"}, {0}},
  {{"ecpg_check_PQresult"}, {0}},
  {{"ecpg_realloc"}, {0}},
  {{"findsubquery"}, {0}},
  {{"FreeDir"}, {0}},
  {{"gistjoinvector"}, {0}},
  {{"index_close"}, {0}},
  {{"InsertPgAttributeTuples"}, {4}},
  {{"_int_unique"}, {0}},
  {{"resize_intArrayType"}, {0}},
  {{"jsonpath_yyrealloc"}, {0}},
  {{"list_delete"}, {0}},
  {{"list_delete_cell"}, {0}},
  {{"list_delete_first"}, {0}},
  {{"list_delete_first_n"}, {0}},
  {{"list_delete_int"}, {0}},
  {{"list_delete_last"}, {0}},
  {{"list_delete_nth_cell"}, {0}},
  {{"list_delete_oid"}, {0}},
  {{"list_delete_ptr"}, {0}},
  {{"ParallelSlotsAdoptConn"}, {1}},
  {{"pa_xact_finish"}, {0}},
  {{"pg_realloc"}, {0}},
  {{"relation_close"}, {0}},
  {{"RelationClose"}, {0}},
  {{"relation_is_updatable"}, {1}},
  {{"relation_is_updatable"}, {3}},
  {{"ReleaseCatCacheList"}, {0}},
  {{"ReorderBufferQueueChange"}, {3}},
  {{"repalloc"}, {0}},
  {{"repalloc0"}, {0}},
  {{"rewrite_heap_tuple"}, {1}},
  {{"rewrite_heap_tuple"}, {2}},
  {{"sequence_close"}, {0}},
  {{"SPI_repalloc"}, {0}},
  {{"table_close"}, {0}},
  {{"TableCommandResultHandler"}, {0}},
  {{"yyrealloc"}, {0}},
};

// Set containing functions where the return value
// should be reassigned. 
llvm::StringSet<> ReassigningSet{
  {"bms_add_member"},
  {"bms_add_members"},
  {"bms_add_range"},
  {"bms_del_member"},
  {"bms_del_members"},
  {"bms_int_members"},
  {"bms_join"},
  {"bms_replace_members"},
  {"brin_copy_tuple"},
  {"findsubquery"},
  {"list_delete_cell"},
  {"list_delete_first"},
  {"list_delete_first_n"},
  {"list_delete_int"},
  {"list_delete_last"},
  {"list_delete"},
  {"list_delete_nth_cell"},
  {"list_delete_oid"},
  {"list_delete_ptr"},
};

// Set containing functions where the return value
// signifies whether the parameter has been freed.
// The SmallPtrSet is optimized for small sets.
llvm::StringSet<> BooleanSet{
  {"ecpg_check_PQresult"},
};

// Set of functions to be ignored for double-free
llvm::StringSet<> IgnoreDouble{
  {"PQfinish"},
};

// Map of functions to be ignored for use-after-free
llvm::StringMap<unsigned int> IgnoreUse{
  {"PQerrorMessage", 0},
};

// Map of functions to be ignored for use-after-free
llvm::StringSet<> IgnoreAlltogether{
  {"exit_nicely"},
};

// Helper function: retrieves the variable declaration from an expression and 
// returns the name.
std::string getNameFromExpression(const Expr * Expr){
  if (!Expr)  
    return "";
  if (const DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(Expr)) {
      if (const ValueDecl *VD = DRE->getDecl()) {
          return VD->getNameAsString();
      }
  }
  // recurse until there are no casts
  else if (const CastExpr *CE = dyn_cast<CastExpr>(Expr)) {
      return getNameFromExpression(CE->getSubExpr());
  }
  return "";
}

void PostgresChecker::HandleUseAfterFree(CheckerContext &C, SourceRange Range,
                                         const PGRefState *RS, 
                                         std::string varName, 
                                         Category Cat) const{

  BugType *BT;
  // the message to be emitted as a warning
  std::string message;
  switch(Cat){
    case (Strict):
      message = "Attempt to use released memory";
      if (!BT_Free_Strict)
        BT_Free_Strict.reset(new BugType(this, message));
      BT = BT_Free_Strict.get();
    break;
    // we should not be here, this could be handled better (maybe introduce 
    // another enum?)
    case (Dependent):
      return;
    case (Arbitrary):
      message = "Attempt to use potentially released memory";
      if (!BT_Free_Arbitrary)
        BT_Free_Arbitrary.reset(new BugType(this, message));
      BT = BT_Free_Arbitrary.get();
    break;
  }
  // add the variable to the message name if it exists
  if (!varName.empty())
    message = message + ": " + varName;
  emitReport(RS, BT, C, message);
}

void PostgresChecker::HandleDoubleFree(CheckerContext &C, SourceRange Range, 
                                       const PGRefState *RS, std::string varName, 
                                       Category FirstFreeCat, Category Cat) const{

  BugType *BT;
  // the message to be emitted as a warning
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
    // we should not be here, this could be handled better (maybe introduce 
    // another enum?)
    case (Dependent):
      return;
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
  // add the variable to the message name if it exists
  if (!varName.empty())
    message = message + ": " + varName;
  emitReport(RS, BT, C, message);
}

// If the function is freeing -> call HandleFree; otherwise, call 
// checkUseAfterFree
void PostgresChecker::checkPreCall(const CallEvent &Call, CheckerContext &C) const {

  const FunctionDecl *FD = dyn_cast_or_null<FunctionDecl>(Call.getDecl());
  if (!FD)
    return;
  // if the function has a body, we return. If there is a call to a freeing 
  // function inside we see it anyways
  if (FD->hasBody()) 
    return;

  if (IgnoreAlltogether.contains(FD->getNameAsString()))
    return;

  // look up the function name in the maps
  if (StrictMap.contains(FD->getName()) 
    || DependentMap.contains(FD->getName()) 
    || ArbitraryMap.contains(FD->getName())){

    // check whether we have access to a valid expression (and not, e.g., void)
    if (!Call.getOriginExpr())
      return;

    // handle strict functions
    if (StrictMap.contains(FD->getName())){
      HandleFree(Call, C, Strict);
      return;
    }
    // handle dependent functions
    if (DependentMap.contains(FD->getName())){
      HandleFree(Call, C, Dependent);
      return;
    }
    // handle arbitrary functions
    if (ArbitraryMap.contains(FD->getName())){
        HandleFree(Call, C, Arbitrary);
      return;
    }
    // this is pure paranoia
    return;
  }

  // we encountered a non-freeing function, for every parameter retrieve the 
  // symbolic value and, if it is a location, check for use-after-free
  for (unsigned I = 0, E = Call.getNumArgs(); I != E; ++I) {
    // ignore special cases
    if (IgnoreUse.contains(FD->getNameAsString()) && I == IgnoreUse.lookup(FD->getNameAsString()))
      continue;
    SVal ArgSVal = Call.getArgSVal(I);
    if (isa<Loc>(ArgSVal)) {
      SymbolRef Sym = ArgSVal.getAsSymbol();
      if (!Sym)
        continue;
      checkUseAfterFree(Sym, getNameFromExpression(Call.getArgExpr(I)), C, 
                        Call.getArgExpr(I));
    }
  }
}

void PostgresChecker::HandleFree(const CallEvent &Call, CheckerContext &C, 
                                 Category Cat) const{

  // no argument means nothing to check
  if (Call.getNumArgs() == 0)
        return;
  const FunctionDecl *FD = dyn_cast_or_null<FunctionDecl>(Call.getDecl());
  if (!FD)
    return;

  SVal ArgVal;
  // keep track of the expression we found to add the name of the variable to 
  // a potential warning
  const Expr *ArgExpr;
  switch (Cat){
    // strict function -> get the position of the argument and retrieve it
    case (Strict): {
      auto Position = StrictMap.lookup(FD->getName());
      if (Call.getNumArgs() <= Position)
        return;
      ArgExpr = Call.getArgExpr(Position);
      if (!ArgExpr)
        return;
      ArgVal = C.getSVal(ArgExpr);
      break;
    }
    // dependent functions:
    //   - retrieve the DependencyInfo
    //   - call Info.isFreeing(): if true, handle function as strict
    //   - if Undefined or not freeing and the Info.isArbitrary fallback option
    //     is set, treat the function as arbitrary
    //   - otherwise do nothing
    //   - if we do something, get position of the argument and retrieve it
    case (Dependent): {
      auto It = DependentMap.find(FD->getName());
      if (It != DependentMap.end()) {
        DependencyInfo Info = It->second;
        if (Call.getNumArgs() <= Info.positionFreed)
          return;
        auto result = Info.isFreeing(const_cast<CallEvent &>(Call), C);
        //function is freeing
        if (result == True){
          Cat = Strict;
        // function is not freeing
        } else if (result == False){
          //fall back to arbitrary?
          if (Info.isArbitrary)
            Cat = Arbitrary;
          //function does not free at all
          else
           return;
        // ifFreeing could not be determined
        } else
            Cat = Arbitrary;
        ArgExpr = Call.getArgExpr(Info.positionFreed);
        if (!ArgExpr)
          return;
        ArgVal = C.getSVal(ArgExpr);
        break;
      }
      // we did not retrieve anything
      return;
    }
    // arbitrary function -> get the position of the argument and retrieve it
    case (Arbitrary): {
      auto Position = ArbitraryMap.lookup(FD->getName());
      if (Call.getNumArgs() <= Position)
        return;
      ArgExpr = Call.getArgExpr(Position);
      if (!ArgExpr)
        return;
      ArgVal = C.getSVal(ArgExpr);
      break; // doing this for safety reasons in case enum gets expanded
    }
  }

  if (ArgVal.isUnknownOrUndef())
    return;
  const MemRegion *R = ArgVal.getAsRegion();
  if (!R)
    return;
  // get parent expression to have access to the source location
  const Expr *ParentExpr = Call.getOriginExpr();
  if (!ParentExpr)
    return;

  // remove casts and retrieve the base symbolic region
  R = R->StripCasts();
  const SymbolicRegion *SrBase = dyn_cast<SymbolicRegion>(R->getBaseRegion());
  if (!SrBase)
    return;

  ProgramStateRef State = C.getState();
  if (!State)
    return;
  // look up the symbol reference in the RegionStatePG map. If found, handle 
  // double-free
  SymbolRef SymBase = SrBase->getSymbol();
  const PGRefState *RsBase = State->get<RegionStatePG>(SymBase);
  if (RsBase){
    // if both the old and the new functions are C functions ignore
    // -> we don't want to get in the way of the MallocChecker
    if (CMemoryMap.contains(RsBase->getFunction()->getName()) 
      && CMemoryMap.contains(FD->getName()))
      return;
    // determine the quality of the double-free
    Category CatFirst = RsBase->isReleased() ? Strict : Arbitrary;
    if (!IgnoreDouble.contains(FD->getNameAsString()))
      HandleDoubleFree(C, ParentExpr->getSourceRange(), RsBase, 
                       getNameFromExpression(ArgExpr), CatFirst, Cat);
  }

  // the variable name to be used in a potential warning
  std::string VarName = getNameFromExpression(ArgExpr);

  // depending on the category of the freeing function set a released or possibly 
  // released state
  switch (Cat){
    case Strict:
      State = State->set<RegionStatePG>(SymBase, PGRefState::getReleased(
                                                        ParentExpr, FD, VarName));
      break;
    case Dependent:
      return;// We should never get here (could this be handled better?)
    case Arbitrary:
      State = State->set<RegionStatePG>(SymBase, PGRefState::getPossiblyReleased(
                                                        ParentExpr, FD, VarName));
      break;
    default:
      return;
  }

  // add the state to the checker context
  C.addTransition(State);
}

// Check whether the location accessed is a freed symbolic region.
void PostgresChecker::checkLocation(SVal l, bool isLoad, const Stmt *S,
                                  CheckerContext &C) const {
  SymbolRef Sym = l.getLocSymbolInBase();
  if (Sym){
    std::string varName = "";
    // try to extract the variable name from the variable declaration
    if (auto loc = l.getAs<Loc>()) {
      if (const MemRegion *region = loc->getAsRegion()) {
        if (const VarRegion *varRegion = dyn_cast<VarRegion>(region)) {
            const VarDecl *varDecl = varRegion->getDecl();
            varName = varDecl->getName();
        }
      }
    }
    checkUseAfterFree(Sym, varName, C, S);
  }
}

// Check for use-after-free for return value.
void PostgresChecker::checkPreStmt(const ReturnStmt *S, CheckerContext &C) const {
  if (!S)
    return;
  const Expr *E = S->getRetValue();
  if (!E)
    return;
  SVal RetVal = C.getSVal(E);
  SymbolRef Sym = RetVal.getAsSymbol();
  // we might deal with composite objects -> look at the region, if it is a field 
  // or array element, retrieve the base region and extract the symbol
  if (!Sym)
    if (const MemRegion *MR = RetVal.getAsRegion())
      if (isa<FieldRegion, ElementRegion>(MR))
        if (const SymbolicRegion *BMR =
              dyn_cast<SymbolicRegion>(MR->getBaseRegion()))
          Sym = BMR->getSymbol();
  if (Sym)
    checkUseAfterFree(Sym, getNameFromExpression(E), C, E);
}

// Check whether the memory region the symbolic reference is pointing to has been
// freed -> look into the RegionStatePG map and handle strict and arbitrary cases
bool PostgresChecker::checkUseAfterFree(SymbolRef Sym, std::string varName, 
                                        CheckerContext &C, const Stmt * S) const{
  const PGRefState *RS = C.getState()->get<RegionStatePG>(Sym);
  // no use-after-free
  if (!RS)
    return false;
  if (RS && RS->isReleased()) {
    HandleUseAfterFree(C, S->getSourceRange(), RS, varName, Strict);
    return true;
  }
  if (RS && RS->isPossiblyReleased()) {
    HandleUseAfterFree(C, S->getSourceRange(), RS, varName, Arbitrary);
    return true;
  }
  return false;
}

// Emit a basic bug report with message
void PostgresChecker::emitReport(const PGRefState *RS, BugType *BT, 
                                 CheckerContext &C, std::string message) const{
  if (!BT)
    return;
  // One could also argue, that we should use a fatal error node here for strict
  // functions and a non-fatal one for arbitrary ones. Since MallocChecker uses
  // non-fatal for 'strict' cases, we follow suite.
  ExplodedNode *EN = C.generateNonFatalErrorNode(C.getState(), this);
  if (!EN) 
    return;

  // get location information for the current site and create the report
  PathDiagnosticLocation PDLoc = PathDiagnosticLocation::create(
    EN->getLocation(),  
    C.getSourceManager()
  );
  auto R = std::make_unique<BasicBugReport>(*BT, message,PDLoc);

  // if, for some reason, the PGRefState is invalid, emit a report without 
  // information about the free site
  if (!RS || !RS->getStmt() || !RS->getFunction()){
    C.emitReport(std::move(R));
    return;
  }

  // get location information for the free site
  PathDiagnosticLocation PDLocOriginal = PathDiagnosticLocation::createBegin(
    RS->getStmt(),
    C.getSourceManager(),
    C.getLocationContext()
  ); 
  const FunctionDecl *FD = RS->getFunction();

  // if the variable name exists add (varName) to the message
  std::string addition = RS->getVarName().empty() ? "" : 
                         (" (" + RS->getVarName() + ")");

  // add warning note for reassigning functions
  if (ReassigningSet.contains(FD->getNameAsString())){
    R->addNote(("The return value should probably be reassigned" + addition), PDLocOriginal);
    // add warning note for functions returning a boolean
  } else if (BooleanSet.contains(FD->getNameAsString())){
    R->addNote(("The return value should probably be checked"), PDLocOriginal);
    // add a note about the free site to the report
  } else {
    R->addNote("Freeing function" + (FD ? (": " + FD->getNameAsString() + addition) 
                                   : "<unknown>"), PDLocOriginal);
  }

  C.emitReport(std::move(R));
}

namespace clang {
namespace ento {
// Register the checker as an extern .so file:
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

