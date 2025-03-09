#ifndef INC_SOLVER_H
#define INC_SOLVER_H

#include <vector>
#include <queue>
#include <string>
#include <iostream>
#include <limits.h>

#include "PBConstraint.h"
#include "Cardinality.h"
#include "WConstraint.h"
#include "Strategy.h"
#include "MaxHeap.h"
#include "Model.h"
#include "OccurListVector.h"
#include "Clause.h"
#include "Reason.h"
#include "Statistics.h"

#include <sys/time.h>
#include <sys/resource.h>
#include <sys/types.h>
#include <unistd.h>
#include <cinttypes>
#include <iomanip>
#include <bits/stdc++.h>

using namespace std;

class Solver {
 public:
  typedef enum {
    INFEASIBLE,
    NO_SOLUTION_FOUND,
    SOME_SOLUTION_FOUND,
    OPTIMUM_FOUND
  } StatusSolver;


 private:
  int numVars;
  bool conflict;
  uint conflictsLimit;
  uint decisionsLimit;
  static const int CONFLICT_CLAUSE      = 1;
  static const int CONFLICT_PB          = 2;
  static const int CONFLICT_BIN_CLAUSE  = 3;
  static const int CONFLICT_CARD  = 4;
  
  int typeConflict;
  int constraintConflictNum;
  int cardinalityConflictNum;
  int clauseConflictNum;
  Clause clauseConflict;
  pair<int,int> binClauseConflict;
  
  
  long long nconfl_to_reduce = 2000;
  long long nconfl_to_restart = 0;
  

  // ---------------------------------------------------
  struct ConstraintCleanup {
    WConstraint wc;
    bool isInit;
    int activity;
    int LBD;
    ConstraintCleanup(const WConstraint& c, bool i, int a, int lbd):wc(c),isInit(i),activity(a),LBD(lbd){}
  };
  
  class WatchListElem {
  public:
    int clauseId;
    int cachedLit;
    WatchListElem(){}
    WatchListElem (int id, int lit): clauseId(id), cachedLit(lit) {}
    friend ostream& operator << (ostream& os, const WatchListElem& m) {
      os << "(clNum " << m.clauseId << ",cachedLit " << m.cachedLit << ")";
      return os;
    }
  };
  
  class PBWatchElem {
  public:
    int ctrId;
    int coef;
    int idx;
    PBWatchElem(){}
    PBWatchElem (int ctrNum, int c, int idx):ctrId(ctrNum), coef(c), idx(idx) {}
  };
  

  vector<Clause> clauses;
  
  vector<vector<WatchListElem> > positiveWatchLists;
  vector<vector<WatchListElem> > negativeWatchLists;
  
  vector<vector<int> > positiveBinClauses;
  vector<vector<int> > negativeBinClauses;

  vector<vector<pair<int, int>>> positiveCardLists; // <cardId, idx>
  vector<vector<pair<int, int>>> negativeCardLists;
  
  vector<vector<PBWatchElem> > positivePBWatches;
  vector<vector<PBWatchElem> > negativePBWatches;
  
  vector<OccurList> positiveOccurLists;
  vector<OccurList> negativeOccurLists;
  
  
  // If constraint propagates or is conflicting then necessarily propCounter is < 0
  // propCounter is: sum of all coefficient of non-false literals (how much the lhs could be)
  //                  minus the rhs
  //                  minus an upperbound of the largest coefficient of an unassigned literal
  //                           (computing it precisely is too expensive)
  vector<PBConstraint> constraintsPB;
  vector<Cardinality> cardinalities;
  vector<bool> useCounter;
  vector<long long> sumOfWatches;
  int median;
  int trueVarAtDLZero;
  int falseVarAtDLZero;
  vector<int> originalVar2NewLit;//var in the input file --> current literal   // rui: varString --> var --> lit(the sign depends on the coef of varString)
  vector<int> oldVar2NewLit; // this is used when apply newly found SCCs
  
 public:
  Statistics stats;
  
 private:
  Strategy strat;
  Model model;
  MaxHeap maxHeap;
  double scoreBonus;
  vector<int> bestPolarityForVarInObjective; // 1 --> pos, 0 --> neg, -1 --> none
  vector<pair<int,int> > originalObjective, objective; // <coeff,lit>
  long long int addedConstantToObjective; // obj function is: objective + addedConstantToObjective
  vector<string> varNames;
  map<string,int> stringVar2Num; // original string to original varNum
  bool minimizing;
  string inputfile;
  ofstream* einfo;
  vector<uint> objectiveFunctions;  // store the idx of objective PBConstraint in constraintsPB
  vector<bool> lastSolution;
  vector<int> initialInputSolution; // for heuristic
  StatusSolver status;
  bool SATConflictAnalysis;
  int conflictAnalysisMethod;
  
  int id; // used to share units/binaries
  bool infoToShare;
  bool writeInfo;
  bool readInfo;
  bool usedDecreasingCoeff; // this flag is useful only for watched propagation. (-watch 1), to disable it, use (-watch 1  -sort 0)
  int timeLimit;
  double watchPercent;
  bool useCardinality;
  int obj_num;
  int next_obj_rhs;
  bool propagate_by_priority = true;
  bool BT0;
  bool multiObj;
  
  vector<pair<int,int> > binsToShare;
 public:
  
  Solver(int nVars, clock_t beginTime, bool optMinimizing, string filename);
  inline void  setId (int n) {id = n;}
  inline void  setDecisionLimit(uint nDecs) {decisionsLimit = nDecs;}
  inline void  setConflictLimit(uint nConfs) {conflictsLimit = nConfs;}
  inline void  setExecuteInfoFileStream(ofstream* infoStream) {einfo = infoStream;}
  inline void  setWriteInfo(bool w) {writeInfo = w;}
  inline void  setReadInfo(bool r) {readInfo = r;}
  inline void  setWatchPercent(double p) {watchPercent = p;}
  inline double getWatchPercent() {return watchPercent;}
  inline void  setUseCardinality(bool use) {useCardinality = use;}
  inline bool  getUseCardinality() {return useCardinality;}
  inline void  setBT0(bool up) {BT0 = up;}
  inline void  setMultipleObj(bool multi) {multiObj = multi;}
  inline void  setPropagatebyPriority(bool prior) {propagate_by_priority = prior;}
  
  inline bool  useDecreasingCoeff() {return usedDecreasingCoeff;}
  inline void  setUseDecreasingCoeff(bool useDecCoeff) {usedDecreasingCoeff = useDecCoeff;}
  
  inline bool  wslkIsConsistentWithWatchedLits(int ctrId);
  inline long long   realWslk(PBConstraint& c);
  void printWatchInfo(const PBConstraint& c);
  void printWatchInfo(const int ctrId);
  
  void         solve(int tlimit);
  
  StatusSolver currentStatus ( );
  
  inline void  readStrategy(const string& fileStrategy) {strat.read(fileStrategy);}
  inline void  readDecision(const string& filePolarity) {strat.readDecisionStrategy(filePolarity,stringVar2Num);}
  void  readInitialSolution(const string& fileName);
  void  readExecuteInfoFile(const string& executeInfoFile);
  void checkInitialInputSolutionNeeded();
  inline void  setConflictAnalysisMethod(int caType)    {conflictAnalysisMethod = caType;}
  
  void         addAndPropagatePBConstraint (WConstraint & c, const bool isInitial, int activity, const int LBD, bool isObj = false);
  
  inline void  addVarName( int varNum, const string& varName ) {
    varNames[varNum]=varName;
    stringVar2Num[varName] = varNum;
  }
  inline void  addObjectiveMonomial( int coef, int varNum ) { 
    if (coef == 0) return;
    assert(varNum > 0);
    bestPolarityForVarInObjective[varNum] = (coef < 0); // If coeff < 0, best polarity is true
    originalObjective.push_back( pair<int,int>(coef,varNum) );
  }
  void         printStats() const;
  void setSATConflictAnalysis (bool b) { SATConflictAnalysis = b;}

  double real_time () { return absolute_real_time () - stats.time.real;}
  double process_time () { return absolute_process_time () - stats.time.process;}
  
 private:

  // Mapping between lit and positive integer (useful for indexing vectors)
  // 1 --> 1, -1 --> 2, 2 --> 3, -2 --> 4
  int lit2id(int lit) { return lit > 0 ? 2*lit - 1 : 2*(-lit); }
  int id2lit(int id)  { return id%2    ? id/2 + 1  : -id/2 ;   }
  int maxLitId ( )    { return 2*stats.numOfVars;}
  int minLitId ( )    { return 1;}
  
  inline bool timeout() {
    if ( timeLimit and process_time() >=  timeLimit) {
      cout << endl << endl << "Time limit exceeded." << endl;
      if (stats.numOfSolutionsFound == 0) status = NO_SOLUTION_FOUND;
      else                                status = SOME_SOLUTION_FOUND;
      return true;
    }
    return false;
  }
  
  inline bool decisionLimitHit() {
    if(stats.numOfDecisions >= decisionsLimit) {
      cout << endl << endl << "Decisions limit exceeded!" << endl;
      if (stats.numOfSolutionsFound == 0) status = NO_SOLUTION_FOUND;
      else                                status = SOME_SOLUTION_FOUND;
      return true;
    }
    return false;
  }
  
  inline bool conflictLimitHit() {
    if(stats.numOfDecisions >= decisionsLimit) {
      cout << endl << endl << "Conflicts limit exceeded!" << endl;
      if (stats.numOfSolutionsFound == 0) status = NO_SOLUTION_FOUND;
      else                                status = SOME_SOLUTION_FOUND;
      return true;
    }
    return false;
  }

  // Constraint-related procedures
  inline bool constraintIsFalse         ( const WConstraint & c ) const { return ( maxSumOfConstraintMinusRhs(c) < 0 );  }
  bool constraintIsTrue          ( const WConstraint & c ) const;
  bool constraintIsContradiction (const WConstraint & c) const;
  
  long long maxSumOfConstraintMinusRhs          (const WConstraint & c) const;
  long long simulateMaxSumOfConstraintMinusRhs          (const WConstraint & c, int h) const;
  long long maxSumOfConstraintMinusRhsPropagated(const WConstraint & c) const;
  

  // Rounding problem
  void fix1RoundingProblem(int lit, int coef, WConstraint & c) const;
  void fixRoundingProblem(int confLit, int coef, WConstraint & c) const;
  void ffixRoundingProblem(int x, WConstraint & c) const;
  void fixRoundingProblemSAT(int l, WConstraint & c) const;
  void simulateFixRoundingProblemSAT(int l, WConstraint & c, int h) const;  
  
  // Conflict analysis and learning
  void backjumpMultipleOptions ( const WConstraint& wc );
  template<class T> bool applyCut( int var, const WConstraint & c1, const WConstraint & c2, WConstraint & cut, bool& clash, bool& isInconsistentCut );
  bool applyCut( int var, const WConstraint & c1, const WConstraint & c2, WConstraint & cut, bool& clash, bool& isInconsistentCut );
  void read_lemma( );
  double simulateSMTBasedConflictAnalysisAndBackjump(const WConstraint& falsifiedConstraint, WConstraint& toLearn, int& LBD, int& levelToBJ, bool& asserting );
  void SATBasedConflictAnalysisAndBackjump();
  double simulateSATBasedConflictAnalysisAndBackjump ( WConstraint& toLearn, int& LBD, int& levelToBJ, bool& asserting);
  void BDDBasedConflictAnalysisAndBackjump(const WConstraint& falsifiedConstraint);
  bool simulateBDDBasedConflictAnalysisAndBackjump(const WConstraint& falsifiedConstraint, WConstraint& toLearn, int& LBD, int& levelToBJ, bool& asserting);
  WConstraint instantiateConstraint (WConstraint& c) const;
  void conflictAnalysis();
  
  void lemmaShortening(vector<int>& lemma);
  void lemmaShortening (WConstraint& lemma);
  void lemmaShorteningAuxFunction(int lit, vector<bool>& isMarked, vector<int>& lemma, int& lastMarkedInLemma, bool filterOutDLZero);
  void SMTBasedConflictAnalysisAndBackjump (const WConstraint& falsifiedConstraint);
  int lowestDLAtWhichConstraintPropagates( const WConstraint & c) const;
  int simulateLowestDLAtWhichConstraintPropagates( const WConstraint & c, int h) const;
  int lowestDLAtWhichClausePropagates( const WConstraint & c) const;
  int simulateLowestDLAtWhichClausePropagates( const WConstraint & c, int h) const;  
  int  computeLBD (const WConstraint& c) const;
  int  computeLBD (const vector<int>& c) const;
  void backjumpToDL(int dl);
  inline void backjumpToDL1(int dl);
  inline void backjumpToDL2(int dl);
  void increaseScoresOfVars (const WConstraint& constraint);
  
  // Propagation
  bool propagate();
  bool propagate_by_uniquePtr();
  void checkAllConstraintsPropagated();
  void checkPropagatedPBs ( PBConstraint& c, int ctrId );
  void checkPropagatedCards ( Cardinality& c, int ctrId );
  long long currentWatchedSNFMMaxCoef (int ctrNum);
  
  void addPBConstraintWatchedDL0 (PBConstraint& c);
  void addPBConstraintWatchedDLGreaterThan0 (PBConstraint& c);
  void addPBConstraintCounter (const PBConstraint& c);
  void propagateInitialConstraintWatch (const int ctrId);
  void propagateInitialConstraintCounter (const int ctrId);
  void propagatePBCtrCounter (const int ctrId, const long long wslk);
  void checkObjectiveIsConflictingOrPropagating ( const int ctrId);
  bool propagatePBCtrWatch   (const int ctrId, long long SNF, int litIdx, int coef);
  void addAndPropagateCardinality (WConstraint & c, const bool isInitial, int activity, const int LBD);
  bool propagateCardinalityCtr (const int cardId, int idx);
  void watchMoreLitsInPB (const int ctrNum);
  
  void removeUnits(WConstraint& c);
  int minWatches (const WConstraint & c);
  void minNumWatchesCleanup (const WConstraint & c, long long& wslk, int& numWatches);
  
  void cleanPBWatchListOfPropLit();
  void updateStatusConflictAtDLZero ( ); // we have a conflict at dl zero and we want to compute the status
  void visitOccurList(int lit);
  void visitPBWatches(int lit);
  void visitPBWatchesLazily(int lit);
  void visitPBCounterLists(int lit);
  void visitPBWatchesUniquePtr(int lit);
  void visitPBCounterListsUniquePtr(int lit);
  void visitPBWatchesUniquePtrLazily(int lit);
  void visitCardList (int lit);
  void visitWatchList(int lit);
  void visitBinClause(int lit);
  void visitImplicitBinClause(int lit);
  void visitImplicitWatchedPBBinClause(int lit);
  void deletectrIdFromPBWatchLists (int lit, int ctrId);
  void deletectrIdFromImplicitWatchedPBBinClauses (int lit, int ctrId);
  vector<int> implicitBinSuccessorsOf(int lit); // l such that lit --> l is an implicit clause
  
  // Managing clause/PB database
  void removeDuplicatesAndNegativesFromObjective(WConstraint& auxConstraint);
  void addClause ( const Clause & c);
  void addBinaryClause ( int lit1, int lit2);
  bool existsBinaryClause(int lit1, int lit2);
  void addPBConstraint(PBConstraint & c);
  long long initPBWatchedLits(PBConstraint& pc);
  void addInitialWatchedPBConstraint(PBConstraint & c);
  void discoverImplicitBinClauses(int ctrId, WConstraint& ic);
  void discoverImplicitBinClauses2(int ctrId, WConstraint& ic);
  void discoverImplicitWatchedPBBinClauses(int ctrId, WConstraint& ic);
  void discoverImplicitWatchedPBBinClauses2(int ctrId, WConstraint& ic);
  void doCleanup();
  double luby(double y, int i);
  void cleanupPBConstraints (vector<ConstraintCleanup>& pbs, vector<ConstraintCleanup>& cards, vector<ConstraintCleanup>& cls, vector<pair<int,int> >& binClauses, vector<bool>& ctrIsRemoved, uint newestObjectiveFunction);
  void cleanupCardinalities (vector<ConstraintCleanup>& cards, vector<ConstraintCleanup>& cls, vector<pair<int,int> >& binClauses, vector<bool>& ctrIsRemoved);
  void cleanupClauses (vector<ConstraintCleanup>& cls, vector<pair<int,int> >& binClauses, vector<bool>& ctrIsRemoved);
  void cleanupBinaryClauses ( vector<pair<int,int> >& binClauses);
  void buildOccurLists ( );
  void buildOccurListsAndPBWatches ( );
  void buildCardLists ( );
  void buildWatchLists ( );
  void buildBinaryClauses (const vector<pair<int,int> >& binClauses);
  void writeOccurLists ( );
  void writeWatchLists ( );
  void writeCardinalityNotFalseInfo (Cardinality& c);
  void writeConstraint (PBConstraint& c);
  
  // Probing
  void probing();


  // Unit detection based on binary clauses
  void detectUnits ( );
  void propagateForUnitDetection (vector<int>& timesPropagated, vector<int>& propLits);


  // Detection of equivalent literals
  void detectEquivalentLiterals ( );
  void replaceEquivsInPBConstraints (vector<ConstraintCleanup>& pbs, vector<ConstraintCleanup>& cls, vector<pair<int,int> >& bins, int newestObjectiveFunction, vector<int>& units);
  inline int oldLit2NewLit (int old) { assert((old > 0 and oldVar2NewLit[old] != trueVarAtDLZero and oldVar2NewLit[old] != falseVarAtDLZero) or (old < 0 and oldVar2NewLit[-old] != trueVarAtDLZero and oldVar2NewLit[-old] != falseVarAtDLZero)); return (old > 0 ?  oldVar2NewLit[old]: -oldVar2NewLit[-old]);}
  inline bool isUndefInReplace (int oldLit) {return (oldVar2NewLit[abs(oldLit)] != trueVarAtDLZero and
                 oldVar2NewLit[abs(oldLit)] != falseVarAtDLZero);}
  inline bool isTrueInReplace  (int oldLit) {return
      (oldLit > 0 and oldVar2NewLit[oldLit] == trueVarAtDLZero) or
      (oldLit < 0 and oldVar2NewLit[-oldLit] == falseVarAtDLZero);
  }

  inline bool isFalseInReplace  (int oldLit) {return
      (oldLit > 0 and oldVar2NewLit[oldLit] == falseVarAtDLZero) or
      (oldLit < 0 and oldVar2NewLit[-oldLit] == trueVarAtDLZero);
  }
    
  // Heuristic
  void computeBestPolarityForVarInObjectiveFunction ( );
  inline void increaseActivityScoreOfVar(int var) { 
    bool overFlow = maxHeap.increaseValueBy( var, strat.increaseFactorInDecision(var));
    if ( overFlow ) { cout << "O" << flush; strat.scoreBonus = strat.INITIAL_SCORE_BONUS; maxHeap.reset(); }
  }
  int getNextDecisionVar();
  void takeDecisionForVar(int decVar);

  // Model
  inline void setTrueDueToDecision( int lit ) { 
    model.setTrueDueToDecision(lit); assert(not conflict); 
  }
    
  inline void setTrueDueToReason( int lit, const Reason& r) {
    //if (model.currentDecisionLevel() == 0) infoToShare = true; 
    model.setTrueDueToReason(lit,r);
  }
  
  inline int popAndUnassign1();
  inline int popAndUnassign2();
  int popAndUnassign();

  // Parallel (share information)
  void writeSharedInformation( );
  void readExternalInfo ( );
  void addBinaryClauseToShare(int lit1, int lit2);
  
  //THE FOLLOWING IS FOR DEBUGGING ONLY: ===========================================

  inline bool clauseIsFalse (const Clause& cl) const {
    for (auto& lit:cl)
      if (not model.isFalseLit(lit)) return false;
    return true;
  }

  inline bool clauseIsTrue (const Clause& cl) const {
    for (auto& lit:cl)
      if (model.isTrueLit(lit)) return true;
    return false;
  }

  inline bool clauseHasTwoUnassignedWatches (const Clause& cl) const {
    return model.isUndefLit(cl.getIthLiteral(0)) 
      and model.isUndefLit(cl.getIthLiteral(1)); 
  }
  
  inline bool clausePropagates (const Clause& cl) const {
    int nUnassigned = 0;
    for (auto& lit:cl) {
      if (model.isTrueLit(lit)) return false;
      else if (model.isUndefLit(lit)) ++nUnassigned;
    }
    return nUnassigned == 1;    
  }

  inline void checkClausesPropagated ( ) const {
    for (uint i = 0; i < clauses.size(); ++i) {
      if (not clauseIsTrue(clauses[i]) and not clauseHasTwoUnassignedWatches(clauses[i])) {
  cout << "Clause " << clauses[i] << " not properly watched" << endl;
  printConstraint(WConstraint(clauses[i]));
  assert(false);
      }
      if (clauseIsFalse(clauses[i]) or clausePropagates(clauses[i])) {
  cout << "Clause " << clauses[i] << " not propagated" << endl;
  printConstraint(WConstraint(clauses[i]));
  assert(false);
      }
    }
  }

  inline void printConstraintsPB() const { // for debugging only
    cout << "Pseudo-Boolean Constraints: " << endl;
    for (uint i=0; i<constraintsPB.size(); i++) 
      cout << i << ": " << constraintsPB[i] << endl;    
  }

  inline void printConstraint (const PBConstraint& c) const {
    printConstraint(WConstraint(c));
  }

  inline void printConstraint (const WConstraint& c) const {
    for (int i = 0; i < c.getSize(); ++i) {
      int lit = c.getIthLiteral(i);
      int coef = c.getIthCoefficient(i);
      cout << coef << "*" << (lit<0?"-":"") << "x" << abs(lit);
      if (model.isUndefLit(lit)) cout << "U ";
      else if (model.isTrueLit(lit)) cout << "T" << model.getDLOfLit(lit) << " ";
      else cout << "F" << model.getDLOfLit(-lit) << " ";
    }
    if (c.getSize() == 0) cout << 0;
    cout << " >= " << c.getConstant()  << endl;
  }

  inline bool constraintPropagatesOrConflicts( const PBConstraint &c ) const {
    return constraintPropagatesOrConflicts(WConstraint(c));
  }

  inline bool constraintPropagatesOrConflicts( const WConstraint &c ) const {
    return(  maxSumOfConstraintMinusRhs(c) - maxUnassCoefOfConstraint(c) < 0 );
  }

  int maxUnassCoefOfConstraint(const WConstraint & c) const;
  void artificialDecision(int lit);
  
  public:
  
  uint64_t maximum_resident_set_size () {
    struct rusage u;
    if (getrusage (RUSAGE_SELF, &u)) return 0;
    return ((uint64_t) u.ru_maxrss) << 10;
  }

  uint64_t current_resident_set_size () {
    char path[40];
    sprintf (path, "/proc/%" PRId64 "/statm", (int64_t) getpid ());
    FILE * file = fopen (path, "r");
    if (!file) return 0;
    uint64_t dummy, rss;
    int scanned = fscanf (file, "%" PRIu64 " %" PRIu64 "", &dummy, &rss);
    fclose (file);
    return scanned == 2 ? rss * sysconf (_SC_PAGESIZE) : 0;
  }
  
  double absolute_real_time () {
  struct timeval tv;
  if (gettimeofday (&tv, 0)) return 0;
  return 1e-6 * tv.tv_usec + tv.tv_sec;
}

double absolute_process_time () {
  double res;
  struct rusage u;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;  // user time
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec; // + system time
  return res;
}

  };
  
#endif /* INC_SOLVER_H */
