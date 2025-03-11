#include <fstream>
#include <stack>
#include <unordered_set>
#include <unistd.h>
//#include <gmp.h>
//#include <gmpxx.h>

#include "Solver.h"
#include "Functions.h"

using namespace std;

Solver::Solver(int nVars, clock_t beginTime, bool optMinimizing, string filename) : 
  numVars(nVars), 
  conflict(false),
  conflictsLimit(INT_MAX),
  decisionsLimit(INT_MAX),
  positiveWatchLists(nVars+1),
  negativeWatchLists(nVars+1),
  positiveBinClauses(nVars+1),
  negativeBinClauses(nVars+1),
  positiveCardLists(nVars+1),
  negativeCardLists(nVars+1),
  positivePBWatches(nVars+1),
  negativePBWatches(nVars+1),
  positiveOccurLists(nVars+1),
  negativeOccurLists(nVars+1),
  trueVarAtDLZero(nVars+1),
  falseVarAtDLZero(nVars+2),
  originalVar2NewLit(nVars+1),
  stats(beginTime,nVars),
  strat(stats,nVars), 
  model(nVars), 
  maxHeap(nVars),
  lastSolution(nVars+1,false),
  status(NO_SOLUTION_FOUND),
  infoToShare(false),
  writeInfo(false),
  readInfo(false),
  usedDecreasingCoeff(true),
  timeLimit(0),
  watchPercent(0),
  useCardinality(true),
  obj_num(-1),
  next_obj_rhs(0),
  update_rhs(true),
  update_pb_rhs(true),
  update_card_rhs(true),
  sync_rhs(true),
  BT0(true),
  propagate_by_priority(true),
  multiObj(false)
{
  bestPolarityForVarInObjective = vector<int> (nVars+1,-1);
  addedConstantToObjective = 0;
  varNames = vector<string> (nVars+1);
  minimizing = optMinimizing;
  inputfile = filename;
  conflictAnalysisMethod = 1; // default is SAT
  for (int v = 1; v <= nVars; ++v) originalVar2NewLit[v] = v;
  stats.time.real = absolute_real_time ();
  stats.time.process = absolute_process_time ();
}

void Solver::checkInitialInputSolutionNeeded() {
  for (int v = 1; v <= numVars; ++v) {
    vector<DecPolarity>& pols = strat.decisionPolarities[v];
    for (auto& p:pols)
      if ( p == INITIAL_SOLUTION and initialInputSolution.size() == 0) {
        cout << "ERROR: Some polarity depends on initialSolution but this has not been read" << endl;
        exit(1);
      }
  }
}

void Solver::writeOccurLists ( ){
  for (int v = 1;  v <= numVars; ++v) {
    cout << "Pos[" << v << "]:=";
    for (auto& e:positiveOccurLists[v]) {
      cout << "(" << e.ctrId << "," << e.coefficient << ") ";
      assert(e.ctrId < int(constraintsPB.size()));
    }
    cout << endl;
    cout << "Neg[" << v << "]:=";
    for (auto& e:negativeOccurLists[v]) {
      cout << "(" << e.ctrId << "," << e.coefficient << ") ";
      assert(e.ctrId < int(constraintsPB.size()));     
    }
    cout << endl;
  }
}

void Solver::writeWatchLists ( ){
  for (int v = 1;  v <= numVars; ++v) {
    cout << "PosWatch[" << v << "]" << endl;
    for (auto& e : positiveWatchLists[v]) cout << e << endl;
    cout << endl;

    cout << "NegWatch[" << v << "]";
    for (auto& e : negativeWatchLists[v]) cout << e << endl;
    cout << endl;
  }
  cout << endl;
}

void Solver::writeCardinalityNotFalseInfo (Cardinality& c) {
  for(int i = 0; i < c.getSize(); ++i) {
    int lit = c.getIthLiteral(i);
    cout << lit << "["<< i << "," << !model.isFalseLit(lit) << ",l" << (model.isUndefLit(lit)?(-1):model.getDLOfLit(lit)) << "] ";
  }
  cout << "  >= " << c.getDegree() << " [ " << c.getIndependentRHSNum() << "/" << c.getIndependentRHSDen() 
  << " + " << c.getObjectiveRHSNum() << "/" << c.getObjectiveRHSDen() << ", isInitial " << c.isInitial() 
  << ", LBD " << c.getLBD() << ", size " << c.getSize() << " ]" << endl;
}

void Solver::writeCardinality (Cardinality& c) {
  for(int i = 0; i < c.getSize(); ++i) {
    int lit = c.getIthLiteral(i);
    cout << lit << "["<< model.strValLit(lit);  // T/F/U
    cout << ",l" << (model.isUndefLit(lit)?(-1):model.getDLOfLit(lit));
    cout << "] ";
  }
  cout << "  >= " << c.getDegree() << " [ " << c.getIndependentRHSNum() << "/" << c.getIndependentRHSDen() 
  << " + " << c.getObjectiveRHSNum() << "/" << c.getObjectiveRHSDen() << ", isInitial " << c.isInitial() 
  << ", size " << c.getSize() << " ]" << endl;
}

void Solver::writeConstraint (PBConstraint& c) {
  for(int i = 0; i < c.getSize(); ++i) {
    int lit  = c.getIthLiteral(i);
    int coef = c.getIthCoefficient(i);
    cout << coef << "*x"<< lit << "["<< model.strValLit(lit);  // T/F/U
    cout << ",l" << (model.isUndefLit(lit)?(-1):model.getDLOfLit(lit));
    cout << "] ";
  }
  cout << "  >= " << c.getConstant() << " [ " << c.getIndependentRHSNum() << "/" << c.getIndependentRHSDen() 
  << " + " << c.getObjectiveRHSNum() << "/" << c.getObjectiveRHSDen() << ", isInitial " << c.isInitial() 
  << ", size " << c.getSize() << " ]" << endl;
}

void Solver::writeConstraint (WConstraint& c) {
  for(int i = 0; i < c.getSize(); ++i) {
    int lit = c.getIthLiteral(i);
    int coef = c.getIthCoefficient(i);
    cout << coef << "*x"<< lit << "["<< model.strValLit(lit);  // T/F/U
    //cout << ",l" << (model.isUndefLit(lit)?(-1):model.getDLOfLit(lit));
    cout << "] ";
  }
  cout << "  >= " << c.getConstant() << " [ " << c.getIndependentRHSNum() << "/" << c.getIndependentRHSDen() 
  << " + " << c.getObjectiveRHSNum() << "/" << c.getObjectiveRHSDen()
  << ", size " << c.getSize() << " ]" << endl;
}

void  Solver::readInitialSolution(const string& fileName) {
  cout << "Reading initial solution file " << fileName << endl;
  fstream in(fileName.c_str(), fstream::in);
  if (not in) {cout << "Initial solution file " << fileName << " not recognized" << endl;exit(1);}

  string var;
  int value;
  string aux;
  initialInputSolution.resize(numVars+1);

  while (in >> var >> aux >> value >> aux) {
    int varNum = stringVar2Num[var];
    assert(varNum > 0);
    assert(varNum < int(initialInputSolution.size()));
    initialInputSolution[varNum] = value;
  }
}

Solver::StatusSolver Solver::currentStatus ( ){
  return status;
}

void Solver::computeBestPolarityForVarInObjectiveFunction ( ) {
  bestPolarityForVarInObjective = vector<int>(stats.numOfVars+1,-1);
  for (auto& coeffLit:objective) {
    int coeff = coeffLit.first;
    int lit   = coeffLit.second;
    if      (coeff > 0 and lit > 0) bestPolarityForVarInObjective[lit]  = 0;
    else if (coeff > 0 and lit < 0) bestPolarityForVarInObjective[-lit] = 1;
    else if (coeff < 0 and lit > 0) bestPolarityForVarInObjective[lit]  = 1;
    else                            bestPolarityForVarInObjective[-lit] = 0;
  }
}

void Solver::removeDuplicatesAndNegativesFromObjective (WConstraint& auxConstraint) {
  // First remove negative coeffs
  for (auto& p:originalObjective) {
    assert(p.first);
    if (p.first > 0) {
      objective.push_back(p);
      addedConstantToCost += p.first; 
    }
    else {
      objective.emplace_back(-p.first,-p.second);
      addedConstantToObjective += p.first;
    }
  }
  if (abs(addedConstantToObjective) >= INT_MAX) cout << "LARGE addedConstantToObjective = " << addedConstantToObjective << ", obj constant will be " << int(-addedConstantToObjective) << endl;
  
  WConstraint wc(objective,-addedConstantToObjective,{-addedConstantToObjective,1},{0,1}, false); // {0,1}, {0,1} will never be used for this wc
  wc.sortByIncreasingVariable();
  wc.removeDuplicates();
  wc.sortByDecreasingCoefficient(); // no need to sort again for new obj constraints
  
  addedConstantToObjective = -wc.getConstant();  // in case it will be changed when removing duplicates
  
  objective.clear();
  
  // remove units in objective
  for (int i = 0; i < wc.getSize(); ++i) {
    int lit  = wc.getIthLiteral(i);
    int coef = wc.getIthCoefficient(i);
    assert(coef > 0);
    if (model.isUndefLit(lit))      objective.emplace_back(coef, lit);
    else if (model.isTrueLit(lit))  addedConstantToObjective += coef;
    else                            removedUnitCoefFromObjective += coef;
  }
  
  next_obj_rhs = 0;
  stats.RhsLB = -1;
  stats.RhsUB = 0;
  for ( pair<int,int>& p : objective) stats.RhsUB += p.first; // assume all lits are true
  assert(addedConstantToCost == addedConstantToObjective + stats.RhsUB + removedUnitCoefFromObjective);
  stats.costLB = addedConstantToObjective;
  stats.costUB = addedConstantToObjective + stats.RhsUB;  // -infinite
  stats.RhsLB = addedConstantToCost - stats.costUB;
  
  cout << "objective ctr is cardinalyty? " << (wc.getIthCoefficient(0) == 1) << " ,addedConstantToObjective " << addedConstantToObjective << " ,addedConstantToCost " << addedConstantToCost << " ,stats.RHS LB " << stats.RhsLB << " ,UB = " << stats.RhsUB << " ,cost LB " << stats.costLB << " ,cost UB " << stats.costUB << " ,numLits in obj " << objective.size() << ", " << removedUnitCoefFromObjective << endl;
  
  computeBestPolarityForVarInObjectiveFunction();
  
  stats.lastSubtractConstant = 0;
  vector<int> coeffs, lits;
  long long int rhs = addedConstantToObjective + 1;  // directly increase by 1 here
  for ( pair<int,int>& p : objective) {
    int coe   = -p.first; assert(coe < 0);
    int lit   = p.second;
    int coef  = abs(coe);
    if (coe < 0) { rhs+=coef; lit = -lit; }
    coeffs.push_back(coef);
    lits.push_back(lit);
  }
  assert(rhs >= 0);
  if (rhs < 0 or abs(rhs) > INT_MAX) {cout << "Initializing objective: Too LARGE new obj rhs = " << rhs << endl; exit(0);}
  
  auxConstraint = WConstraint(coeffs,lits,rhs,{0,1},{1,1}, false); // symbolic rhs is (1/1)*obj
}

void Solver::backjumpToDL(int dl) {
  assert( model.currentDecisionLevel()>=dl and dl>=0 );
  ++stats.numOfBackjump;
  
  if (propagate_by_priority) 
    while ( model.currentDecisionLevel() > dl) popAndUnassign1();
  else
    while ( model.currentDecisionLevel() > dl) popAndUnassign2();
}

int Solver::popAndUnassign() {
  if (propagate_by_priority) return popAndUnassign1();
  else                       return popAndUnassign2();
}

int Solver::popAndUnassign1 () {
  int lit = model.getLitAtTop();
  int var = abs(lit);
  
  if (model.isLitPropagatedPB(lit)) {
    for (OccurListElem& e: (lit > 0? negativeOccurLists[var]:positiveOccurLists[var]))
      sumOfWatches[e.ctrId] += e.coefficient;
  }
  if (model.isLitPropagatedPBWatch(lit)) { // the sumOfWatches has already been updated when visiting the occurlist
    for (PBWatchElem& e: (lit > 0? negativePBWatches[var]:positivePBWatches[var]))
      sumOfWatches[e.ctrId] += e.coef;
  }
  
  model.popAndUnassign();
  maxHeap.insertElement(var);  

  return lit;
}

// for unique ptr
int Solver::popAndUnassign2 () {
  int lit = model.getLitAtTop();
  int var = abs(lit);
  
  if (model.isLitPropagatedPB(lit)) { // the sumOfWatches has already been updated when visiting the occurlist
    for (OccurListElem& e: (lit > 0? negativeOccurLists[var]:positiveOccurLists[var]))
      sumOfWatches[e.ctrId] += e.coefficient;
  
    for (PBWatchElem& e: (lit > 0? negativePBWatches[var]:positivePBWatches[var]))
      sumOfWatches[e.ctrId] += e.coef;
  }
  
  model.popAndUnassign();
  maxHeap.insertElement(var);  

  return lit;
}

void Solver::updateStatusConflictAtDLZero ( ) {
  assert(model.currentDecisionLevel() == 0);
  assert(conflict);
  if (stats.numOfSolutionsFound == 0) {status = INFEASIBLE; return;}
  double cost = stats.costOfBestSolution;
  if (not minimizing) cost=-cost;
  printf("\nMIP - Integer optimal solution:  Objective =  %1.10e\n",cost);
  status = OPTIMUM_FOUND;
}

void Solver::conflictAnalysis ( ) {
  strat.increaseActivityScoreBonus();
  if (typeConflict == CONFLICT_PB) {
    constraintsPB[constraintConflictNum].increaseActivity(strat.ACTIVITY_BONUS_FOR_PBS);
    WConstraint wc = WConstraint(constraintsPB[constraintConflictNum]);
    wc.setShaved(shavedPBs[constraintConflictNum]);
    SMTBasedConflictAnalysisAndBackjump(wc);
    ++stats.numOfPBConstraintsInConflicts;
  }
  else if (typeConflict == CONFLICT_CARD) {
    cardinalities[cardinalityConflictNum].increaseActivity(strat.ACTIVITY_BONUS_FOR_CARDS);
    WConstraint wc = WConstraint(cardinalities[cardinalityConflictNum]);
    wc.setShaved(shavedCards[cardinalityConflictNum]);
    SMTBasedConflictAnalysisAndBackjump(wc);
    ++stats.numOfCardinalitiesInConflicts;
  }
  else if (typeConflict == CONFLICT_CLAUSE) {
    clauses[clauseConflictNum].increaseActivity(strat.ACTIVITY_BONUS_FOR_CLAUSES);
    WConstraint wc = WConstraint(clauses[clauseConflictNum]);
    SMTBasedConflictAnalysisAndBackjump(wc);
    ++stats.numOfClausesInConflicts;
  }
  else if (typeConflict == CONFLICT_BIN_CLAUSE){
    WConstraint wc = WConstraint( { {1,binClauseConflict.first}, {1,binClauseConflict.second} }, 1, {1,1},{0,1}, false);
    SMTBasedConflictAnalysisAndBackjump(wc);
    ++stats.numOfBinClausesInConflicts;
  }
  else assert(false);
}


double Solver::percImprovementRHS(long long int rhsLB, long long int rhsUB) {
  if (rhsLB == -1 or rhsLB == 0) return -1;
  return double(rhsUB - rhsLB)/rhsLB*100;
}

//double Solver::percImprovementCost(long long int costLB, long long int costUB, bool smallerUB) {
  //if(costLB == 0) return costUB*100;
  //if(costUB == 0) return abs(costLB)*100;
  //else if (costLB > 0 or costUB < 0) { // same sign (-6-(-8))/8 = 0.25, (-6-(-7))/7 =0.14, 
    //double impr = double(costUB - costLB)/abs(costLB)*100;
    //return impr;
  //}
  //else if (costLB < 0 && costUB > 0) { // same sign (-6-(-8))/8 = 0.25, (-6-(-7))/7 =0.14, 
    
    //double impr = 0;
    //if(smallerUB) impr = double(costUB - costLB)/abs(costLB)*100;
    //else          impr = double(costUB - costLB)/abs(costUB)*100;
    //return impr;
  //}
  //else {
    //cout << "costLB " << costLB << " , costUB " << costUB << ", stats.numSmallerMaxOptRhs " << stats.numSmallerMaxOptRhs << endl;
    //return double(costUB - costLB)/abs(costLB)*100;
  //}
//}
 
// UB should the solu, impr = abs(UB - LB)/abs(UB),  if(UB == 0) impr = abs(UB - LB)/abs(LB) = 100%
double Solver::percImprovementCost(long long int costLB, long long int costUB, bool smallerUB) {
  if(costLB == 0 and costUB == 0) return 0; //return costUB*100;
  else if (costLB == 0) return 100;
  if(costUB == 0) return 100; // return abs(costLB)*100;
  
  //return (costUB - costLB)/abs(costUB)*100;
  if (costUB < 0) { // same sign, ub:-1 ,lb:-8  7/8=0.875, otherwise 7/1=7  
    return double(costUB - costLB)/abs(costLB)*100;  // we can garantee impr < 0
  }
  else if (costLB > 0) { // same sign, (15-3)/15=0.8, (14-3)/14=0.78, (13-3)/13=0.76, (12-3)/12=0.75 
    return double(costUB - costLB)/abs(costUB)*100;  // we can garantee impr < 0
  }
  else if (costLB < 0 && costUB > 0) { 
    double impr = 0;
    // at each solution, UB decreases, LB keep same, impr is smaller, 
    // otherwise, (10-(-1))/10=1.1, (9-(-1))/9=1.111, (8-(-1))/8=1.125, (7-(-1))/7=1.14,  
    //         or (4-(-10))/4=3.5,  (3-(-10))/3=4.33 
    if(smallerUB) impr = double(costUB - costLB)/abs(costLB)*100; 
    
    // at each lemma, LB is increasing, distance is decrasing, UB keep same, impr will be smaller  
    else          impr = double(costUB - costLB)/abs(costUB)*100; 
    return impr;
  }
  else {
    cout << "costLB " << costLB << " , costUB " << costUB << ", stats.numSmallerMaxOptRhs " << stats.numSmallerMaxOptRhs << endl;
    assert(false);
    exit(0);
  }
}

long long int Solver::distanceCost(long long int costLB, long long int costUB) {
  return costUB - costLB;
}

void Solver::SMTBasedConflictAnalysisAndBackjump (const WConstraint& falsifiedConstraint) {
  WConstraint cuttingConstraint;
  WConstraint conflictingConstraint = falsifiedConstraint;
  conflictingConstraint.sortByIncreasingVariable();
  Reason cuttingConstraintReason;
  long long conflictingConstraintMaxSum = maxSumOfConstraintMinusRhs(conflictingConstraint);
  assert( conflictingConstraintMaxSum < 0);
  assert( model.currentDecisionLevel() > 0 );
  int confVar=0;
  int litInCuttingConstraint=0,     coefInCuttingConstraint=0;
  int litInConflictingConstraint=0, coefInConflictingConstraint=0;
  
  while ( true ) {    // while no backjump takes place
    cuttingConstraint.reset();
    assert(conflictingConstraintMaxSum < 0);
    
    while ( conflictingConstraintMaxSum < 0 ) {
      if ( model.currentDecisionLevel() == 0 ) { // 1599*.lp
        cout << "it's still conflicting after popping all literals in trail........" << endl; 
        return;
      }
      
      assert( conflictingConstraintMaxSum == maxSumOfConstraintMinusRhs(conflictingConstraint) );
      cuttingConstraintReason = model.getReasonAtTop();
      litInCuttingConstraint = model.getLitAtTop();
      assert(model.getReasonOfLit(litInCuttingConstraint) == cuttingConstraintReason);
      confVar = abs( litInCuttingConstraint );
      assert(conflictingConstraint.isOrderedByIncreasingVariable());

      pair<int,int> coefLitConflictingConstraint = conflictingConstraint.getCoefficientLiteralBinarySearch(confVar);
      coefInConflictingConstraint = coefLitConflictingConstraint.first;
      litInConflictingConstraint = coefLitConflictingConstraint.second;

      if ( coefInConflictingConstraint!=0 and model.isFalseLit(litInConflictingConstraint) )  {
        assert(litInConflictingConstraint == -litInCuttingConstraint);
        conflictingConstraintMaxSum += coefInConflictingConstraint;
      }
      popAndUnassign();
    }
    
    assert(maxSumOfConstraintMinusRhs(conflictingConstraint) >= 0);

    if (cuttingConstraintReason.isConstraint()) {
      PBConstraint& pb = constraintsPB[cuttingConstraintReason.getCtrId()];
      pb.increaseActivity(strat.ACTIVITY_BONUS_FOR_PBS);
      cuttingConstraint = WConstraint(pb);
      cuttingConstraint.setShaved(shavedPBs[cuttingConstraintReason.getCtrId()]);
      cuttingConstraint.sortByIncreasingVariable();
      ++stats.numOfPBConstraintsInConflicts;
    }
    else if (cuttingConstraintReason.isCardinality()) {
      Cardinality& card = cardinalities[cuttingConstraintReason.getCardinalityNum()];
      card.increaseActivity(strat.ACTIVITY_BONUS_FOR_CARDS);
      cuttingConstraint = WConstraint(card);
      cuttingConstraint.setShaved(shavedCards[cuttingConstraintReason.getCardinalityNum()]);
      cuttingConstraint.sortByIncreasingVariable();
      ++stats.numOfCardinalitiesInConflicts;
    }
    else if (cuttingConstraintReason.isClause()) {
      Clause& clause = clauses[cuttingConstraintReason.getClauseNum()];
      clause.increaseActivity(strat.ACTIVITY_BONUS_FOR_CLAUSES);
      cuttingConstraint = WConstraint(clause);
      cuttingConstraint.sortByIncreasingVariable();
      ++stats.numOfClausesInConflicts;
    }
    else if (cuttingConstraintReason.isBinClause()) {
      cuttingConstraint = WConstraint({ {1,litInCuttingConstraint}, {1,cuttingConstraintReason.getOtherBinLit()} },1, {1,1},{0,1}, false);
      cuttingConstraint.sortByIncreasingVariable();
      ++stats.numOfBinClausesInConflicts;
    }
    else { // not propagated all lits
      assert(cuttingConstraintReason.isUnitOrDecision());
      cout << "\nProblem at nConfs: " << stats.numOfConflicts << ", isUnitOrDecision? " << cuttingConstraintReason.isUnitOrDecision() << endl;
      cout << "lit in cutting constraint " << litInCuttingConstraint << ", level " << model.currentDecisionLevel() << endl << endl;
      cout << "cutting constraint " << cuttingConstraint << endl << endl;
      //cout << "conflictingConstraint " << conflictingConstraint << endl;
      cout << "reason " << cuttingConstraintReason << endl;
      exit(1);
      assert(false);
    }

    coefInCuttingConstraint = cuttingConstraint.getCoefficientBinarySearch(confVar);
    assert(coefInCuttingConstraint > 0); // found the litInCuttingConstraint in the cuttingConstraint
    assert(cuttingConstraint.getLiteralBinarySearch(confVar) == litInCuttingConstraint);
    assert(model.isUndefLit(litInCuttingConstraint));
    assert(maxSumOfConstraintMinusRhs(cuttingConstraint) < coefInCuttingConstraint); // should be propagating
    
    WConstraint cut;
    bool clash = false;
    bool overflow = false;
    bool isInconsistentCut = false;
    bool applyCutAgain = true;

    if (coefInCuttingConstraint > 1 and coefInConflictingConstraint > 1) {
      if (cuttingConstraint.getSize()  > conflictingConstraint.getSize()) {
        fixRoundingProblemSAT(litInCuttingConstraint,cuttingConstraint);
      }
      else {
        fixRoundingProblemSAT(litInConflictingConstraint, conflictingConstraint );
      }
    }
    else {
      overflow = applyCut( confVar, conflictingConstraint, cuttingConstraint, cut, clash, isInconsistentCut );
      
      if (cut.getSize() == 0 and cut.getConstant() == 1) { // inconsistent cut, 0 >= 1, overflow = false, no need to applyCut again
        assert(not overflow);
        isInconsistentCut = true;
      }
      
      if (overflow) {
        if (cuttingConstraint.getSize()  > conflictingConstraint.getSize()) {
          fixRoundingProblemSAT(litInCuttingConstraint,cuttingConstraint);
        }
        else {
          fixRoundingProblemSAT(litInConflictingConstraint, conflictingConstraint );
        }
      }
      else applyCutAgain = false;
    }

    assert(conflictingConstraint.isOrderedByIncreasingVariable());
    assert(cuttingConstraint.isOrderedByIncreasingVariable());
    assert(maxSumOfConstraintMinusRhs(conflictingConstraint) >= 0);

    if (applyCutAgain) overflow = applyCut( confVar, conflictingConstraint, cuttingConstraint, cut, clash, isInconsistentCut );
    
    assert(overflow or constraintIsFalse(cut)); 
    if ( overflow ) {
      fixRoundingProblemSAT( litInCuttingConstraint, cuttingConstraint );
      overflow = applyCut( confVar, conflictingConstraint, cuttingConstraint, cut, clash, isInconsistentCut );
      if (not overflow) increaseScoresOfVars(cuttingConstraint);
    }
    else increaseScoresOfVars(cuttingConstraint);

    assert(overflow or constraintIsFalse(cut));
    if ( overflow ) {
      fixRoundingProblemSAT(litInConflictingConstraint,conflictingConstraint);
      increaseScoresOfVars(cuttingConstraint);
      overflow = applyCut( confVar, conflictingConstraint, cuttingConstraint, cut, clash, isInconsistentCut);
    }

    assert( not overflow );            assert( constraintIsFalse(cut) );
    
    // ===================    end cut
    
    if (isInconsistentCut) {
      assert(conflict);
      backjumpToDL(0);
      return;
    }
    
    if (cut.getSize() == 0) {
      cout << "cut size 0, constant " << cut.getConstant() << ", set dl 0" << endl << flush; // is a tautology
      conflict= true;
      backjumpToDL(0);
      return;
    }
        
    conflictingConstraint = cut;
    
    bool isConflicting, isPropagating;
    int dlToBackjumpTo = clash?lowestDLAtWhichConstraintPropagates(conflictingConstraint, isConflicting, isPropagating):-1;
    
    assert(cut.getSize() > 1 or (cut.getSize() == 1 && dlToBackjumpTo == 0 && cut.getIthCoefficient(0) >= cut.getConstant()));
    
    if (dlToBackjumpTo != -1) {  // backjump!
      if (conflictingConstraint.isClause()) {  // if the conflicting is clause 
        assert(conflictingConstraint.getSize() > 0);
        vector<int> lemma;
        int posUIP = -1; int numUIP = 0; int maxDL = -1;
        
        for (int i = 0; i < conflictingConstraint.getSize(); ++i) {
          int lit = conflictingConstraint.getIthLiteral(i);
          assert(model.isFalseLit(lit));
          
          if (model.getDLOfLit(lit) == maxDL)     {posUIP = i; ++numUIP;}
          else if (model.getDLOfLit(lit) > maxDL) {posUIP = i; numUIP = 1; maxDL = model.getDLOfLit(lit);}
          lemma.push_back(lit);
        }
        
        assert(numUIP == 1);
        swap(lemma[0],lemma[posUIP]);
        lemmaShortening(lemma);
        int LBD = computeLBD(lemma);
        backjumpToDL(dlToBackjumpTo);
        conflict = false;
        
        if (lemma.size() == 1) {  // lemma is unit
          setTrueDueToReason(lemma[0],noReason());
        }
        else if (lemma.size() == 2) {  // lemma is binary clause
          addBinaryClause(lemma[0],lemma[1]);
          strat.reportLearnBinClause();
          setTrueDueToReason(lemma[0],Reason(lemma[1],Reason::BIN_CLAUSE));
        }
        else {  // lemma is clause
          Clause cl(lemma,false,strat.NEW_CONSTRAINT_ACTIVITY,LBD);
          addClause(cl);
          strat.reportLearnClause(lemma.size());         
          setTrueDueToReason(lemma[0],Reason(clauses.size()-1, Reason::CLAUSE));
        }
        return;
      }
      else {  // if the conflicting is a PBConstraint 
        assert( dlToBackjumpTo < model.currentDecisionLevel() );
          
        backjumpToDL(dlToBackjumpTo);
        assert( constraintIsConflictingOrPropagating( conflictingConstraint ) );
        
        conflictingConstraintMaxSum = maxSumOfConstraintMinusRhs(conflictingConstraint);
        assert(maxSumMinusRhs == conflictingConstraintMaxSum);
        
        if ( dlToBackjumpTo == 0 and conflictingConstraintMaxSum < 0 ) {cout << "The PB lemma is still conflict at dl 0" << endl; return;} // still conflict, and at dl0
        removeUnits(conflictingConstraint);
        assert(conflictingConstraintMaxSum == maxSumOfConstraintMinusRhs(conflictingConstraint));
        
        if (conflictingConstraintMaxSum < 0) {
          assert(isConflicting);
          continue;
        }
        assert(isPropagating);
        increaseScoresOfVars(conflictingConstraint);
        conflict = false;
        int LBD = computeLBD(conflictingConstraint);
        conflictingConstraint.sortByDecreasingCoefficient();
        
        // compute maxOptRhs here, because the pb lemmas might be shaved later in simplify()
        long long int maxOptRhs = optimumRHS(conflictingConstraint);
        if (maxOptRhs != -1) {
          if      (maxOptRhs > stats.RhsUB)  ++stats.numGreaterMaxOptRhs;
          else if (maxOptRhs == stats.RhsUB) ++stats.numEqualMaxOptRhs;
          else { 
            assert(maxOptRhs < stats.RhsUB);
            ++stats.numSmallerMaxOptRhs; 
            stats.RhsUB = maxOptRhs; // smaller
            long long int lb = addedConstantToCost - stats.RhsUB - removedUnitCoefFromObjective;
            assert(stats.costLB < lb);
            stats.costLB = lb; // greater
            
            if (writeInfo) *einfo << "   lem-" << stats.numSmallerMaxOptRhs << "   " << " :[ " << stats.costLB << " ,  " << stats.costUB << " ] " << "d " << distanceCost(stats.costLB, stats.costUB) << "  " << percImprovementCost(stats.costLB, stats.costUB, false) << "%" << "    rhs[ " << stats.RhsLB << " ,  " << stats.RhsUB << " ]  " << percImprovementRHS(stats.RhsLB, stats.RhsUB) << "%    " << process_time() << "  s" << endl;
            
            if (stats.RhsLB >= stats.RhsUB or next_obj_rhs > stats.RhsUB or stats.costLB == stats.costUB) { // not found yet
              cout << endl << "found RHS LB " << stats.RhsLB << " >= UB " << stats.RhsUB << " or next_rhs " << next_obj_rhs << " > UB " << stats.RhsUB << ", stop at this lemma" << ", nDecs: " << stats.numOfDecisions << " nConfs: " << stats.numOfConflicts << ", dl " << model.currentDecisionLevel() << ", costLB " << stats.costLB << " ,  costUB " << stats.costUB << endl;
              conflict = true;
              backjumpToDL(0);
              return;
            }
          }
        }
        
        if(useCardinality and conflictingConstraint.getIthCoefficient(0) == 1 ) {
          addAndPropagateCardinality(conflictingConstraint, false,strat.NEW_CONSTRAINT_ACTIVITY,LBD);
          strat.reportLearnCard(conflictingConstraint.getSize());
        }
        else {
          addAndPropagatePBConstraint(conflictingConstraint, false,strat.NEW_CONSTRAINT_ACTIVITY,LBD, false);
          strat.reportLearnPB(conflictingConstraint.getSize());
        }
        return;
      }
    } // END: backjump
    conflictingConstraintMaxSum = maxSumOfConstraintMinusRhs(conflictingConstraint);
  }
}

double Solver::luby(double y, int i) {
  // Find the finite subsequence that contains index 'i', and the
  // size of that subsequence:
  int size, seq;
  for (size = 1, seq = 0; size < i + 1; seq++, size = 2 * size + 1) {
  }
  while (size != i + 1) {
    size = (size - 1) >> 1;
    --seq;
    assert(size != 0);
    i = i % size;
  }
  return std::pow(y, seq);
}


inline long long Solver::optimumRHS(WConstraint& c) {
  if (c.getObjectiveRHSNum() == 0 or c.isShaved()) return -1;
  ++stats.numCheckedForMaxOptRhs;
  long long int maxLHS = 0;
  if (c.getIthCoefficient(0) == 1) maxLHS = c.getSize(); // cardinality
  else {
    for (int i = 0; i < c.getSize(); i++) {
      assert(!model.isUnit(c.getIthLiteral(i)));
      int coef = c.getIthCoefficient(i);
      maxLHS += coef;
    }
  }
  assert(maxLHS > 0);
  rational<long long> rhs_ind = static_cast<rational<long long>>(c.getIndependentRHS());
  rational<long long> rhs_obj = static_cast<rational<long long>>(c.getObjectiveRHS());
  
  rational<long long> opt = (1 + maxLHS - rhs_ind)/rhs_obj - 1;
  long long int maxOptRhs = ceil(rational_cast<double>(opt));
  assert(opt > 0 && maxOptRhs > 0);
  if (opt <= 0 or maxOptRhs <= 0) {cout << "error when computing maxOptRhs!" << endl; exit(0);}
  return maxOptRhs;
}

// original version
// ./pbsat -bt0 1 -wperc 0 ~/459-normalized-bogr_9.lp 
// ./pbsat ~/opb-478/91-*


// symbolic version
// ./pbsat -symb 1 -bt0 1 -wperc 0 ~/459-normalized-bogr_9.lp 
// ./pbsat ~/opb-478/91-*

// Original Counter propagation
void Solver::solve (int tlimit) {  
  bool feasibilityProblem = (originalObjective.size() == 0);
  timeLimit = tlimit;
  cout.setf(ios::fixed);
  cout.precision(2);
  cout << "solve.....watchPercent: " << getWatchPercent() << ", useCard? " << getUseCardinality() << endl;
  cout << "update_rhs ? " << update_rhs << ", update_pb_rhs " << update_pb_rhs << ", update_card_rhs " << update_card_rhs << ", BT0 " << BT0 << ", write? " << writeInfo << ", multiObj " << multiObj << endl;
  cout << "init stats.numOfSolutionsFound = " << stats.numOfSolutionsFound << endl;
  
  // objective constraint should be not be shaved OR units should not be removed if using symbolic CA.
  if (update_rhs && multiObj) { 
    cout << "Parameter error: both update_rhs and multiObj are true,problem may happen when using symbolic conflic analyse" << endl; 
    exit(0);
  }
  //if (update_rhs)    multiObj = false;
  //else if (multiObj) update_rhs = false;
  
  propagate();
  WConstraint auxConstraint;
  removeDuplicatesAndNegativesFromObjective(auxConstraint); 
  if (conflict) {status = INFEASIBLE; return;}
  
  strat.reportInitialSizes(constraintsPB.size(),cardinalities.size(), clauses.size(),stats.numOfBinClauses);
  cout << "initial num units: " << model.trailSize() << endl;
  cout << endl;
  cout << "initial Props in PB:            " << stats.numOfPropagationsPB         << endl;
  cout << "initial Props in Clause:        " << stats.numOfPropagationsClauses    << endl;
  cout << "initial Props in BinClause:     " << stats.numOfPropagationsBinClauses << endl;
  cout << endl << "initial PBs: " << constraintsPB.size() << " ,Cards: " << cardinalities.size() << " ,Clauses: " << clauses.size() << " ,Bins: " << stats.numOfBinClauses << endl;
  doCleanup();
  
  while (true) {
    if (!conflict) propagate();
    
    while (conflict) {
      --nconfl_to_restart;
      strat.reportConflict(model.trailSize());
      if (model.currentDecisionLevel() == 0) {
        cout << endl << "conflict at dl 0" << ", nDecs: " << stats.numOfDecisions << " nConfs: " << stats.numOfConflicts << endl;
        updateStatusConflictAtDLZero();
        return;
      }
      
      conflictAnalysis();
      
      if (!conflict) propagate();
    }
    
    if (nconfl_to_restart <= 0) {
      backjumpToDL(0);
      strat.reportRestart(); 
      double rest_base = luby(2, stats.numOfRestarts);
      nconfl_to_restart = (long long)rest_base * 100;
      cout << "R" << flush;
      maxHeap.reset();
    }
    if (stats.numOfConflicts >= (stats.numOfCleanUps + 1) * nconfl_to_reduce) {
      backjumpToDL(0);
      strat.reportCleanup();
      cout << "C" << stats.numOfCleanUps << " " << flush;  
      doCleanup();                 assert( not conflict );
      while (stats.numOfConflicts >= stats.numOfCleanUps * nconfl_to_reduce) nconfl_to_reduce += 100;
      
      assert(watchPercent == 0 or !propagate_by_priority or (model.lastPropagatedPB == model.trailSize()-1 && model.lastPropagatedPB == model.lastPropagatedPBWatch && model.lastPropagatedPB == model.lastPropagatedCard && model.lastPropagatedPB == model.lastPropagatedClause));
    }
    
    if (timeout()) return;
    
    int decVar = getNextDecisionVar();
    
    if ( decVar == 0 ) { // all vars assigned and no conflict: solution found
      if (feasibilityProblem) { cout<<endl<<endl<<"Feasibility Proved"<<endl; status = OPTIMUM_FOUND; return; }
      long long bestSoFar = addedConstantToObjective;
      for ( pair<int,int>& p : objective) { bestSoFar += p.first * model.getValueLit( p.second ); }
      strat.reportSolutionFound(bestSoFar);
      status = SOME_SOLUTION_FOUND;
      for (int i=1; i<=numVars; ++i) {lastSolution[i] = model.getValue(i);}
      
      if (bestSoFar > stats.costUB) { cout << endl << "error: bestSoFar " << bestSoFar << " > stats.costUB " << stats.costUB << " , current stats.costLB " << stats.costLB << endl; exit(0); }
      if(bestSoFar < stats.costLB) { cout << endl << "error: bestSoFar " << bestSoFar << " < stats.costLB " << stats.costLB << endl; exit(0); }
      assert(bestSoFar <= stats.costUB);
      assert(bestSoFar >= stats.costLB);
      
      stats.RhsLB = next_obj_rhs;  // 1st valid next_obj_rhs(rhs) is set when 1st solution was found.
      long long int ub = addedConstantToCost - stats.RhsLB - removedUnitCoefFromObjective;
      if (bestSoFar > ub) {cout << "bestSoFar " << bestSoFar << " > ub " << ub << endl; exit(0);}
      assert(bestSoFar <= ub);
      
      double currentTime = process_time();
      
      if (writeInfo) *einfo << "#Sol-" << stats.numOfSolutionsFound << "   " << bestSoFar << "   [ " << stats.costLB << " ,  " << stats.costUB << " ] " << "d " << distanceCost(stats.costLB, bestSoFar) << "  " << percImprovementCost(stats.costLB, bestSoFar, true) << "%" << "     rhs[ " << stats.RhsLB << " ,  " << stats.RhsUB << " ]  " << percImprovementRHS(stats.RhsLB, stats.RhsUB) << "%    " << currentTime << " s" << endl;
      stats.costUB = bestSoFar;
      
      long long int rhs = auxConstraint.getConstant() + stats.lastSubtractConstant - bestSoFar;
      stats.lastSubtractConstant = bestSoFar;
      assert(rhs >= 0);
      next_obj_rhs = rhs;
      
      cout << "BestSoFar: " << bestSoFar << ", nSolu= " << stats.numOfSolutionsFound << " nDecs: " << stats.numOfDecisions << " nConfs: " << stats.numOfConflicts /*<< ", dl " << model.currentDecisionLevel() << ", next_obj_rhs " << rhs << ", obj_num " << obj_num*/ << endl;
      
      //cout << "BestSoFar: " << bestSoFar << ", nSolu= " << stats.numOfSolutionsFound << ", next_rhs " << rhs << ", LB " << stats.RhsLB << ", UB " << stats.RhsUB << ", cost LB " << stats.costLB << ", UB " << stats.costUB  << ", obj_num " << obj_num << ", " << currentTime << "s" << endl;
      
      if (rhs < 0 or abs(rhs) > INT_MAX) {cout << "Too LARGE new obj rhs = " << rhs << endl; exit(0);}
      auxConstraint.setConstant(rhs);
      if (stats.RhsLB >= stats.RhsUB or next_obj_rhs > stats.RhsUB or stats.costLB == stats.costUB ) {
        cout << endl << "found RHS LB " << stats.RhsLB << " >= UB " << stats.RhsUB << " or next_rhs " << rhs << " > UB " << stats.RhsUB << ", cost LB " << stats.costLB << ", UB " << stats.costUB << ", optimum solution is found, #Solu = " << stats.numOfSolutionsFound << ", new obj is a contradiction? " << constraintIsContradiction(auxConstraint) << endl;
        backjumpToDL(0); conflict = true; updateStatusConflictAtDLZero(); 
        return;
      }
      
      assert(next_obj_rhs >= 0);
      if (constraintIsContradiction(auxConstraint)) {cout << "obj ctr is contradict, DONE! " << endl; backjumpToDL(0); conflict = true; updateStatusConflictAtDLZero(); return;}
      assert(!conflict && useCounter.size() == constraintsPB.size());
      
      vector<int> pbs, cardIds;
      if (BT0 and update_rhs and stats.numOfSolutionsFound > 1) {
        PBConstraint& obj = constraintsPB[obj_num];
        sumOfWatches[obj_num] += (obj.getConstant() - next_obj_rhs);
        obj.setConstant(next_obj_rhs);
        assert(obj.getSize() == auxConstraint.getSize());
        
        backjumpToDL(0);
        bool found_inconsistent = false;
        found_inconsistent = updateRHSOfCardsAtDL0(cardIds);
        if (!found_inconsistent and !conflict) updateRHSOfPBsAtDL0(pbs);
        ++stats.numUpdateRHS;
          
        if (constraintsPB.size() > 0) {
          ++stats.nSoluExistPB;
          stats.sumPercE0 += (double)stats.numRHSObjNumE0/constraintsPB.size()*100;
          stats.sumPercG0Shaved += (double)stats.numRHSObjNumG0Shaved/constraintsPB.size()*100;
          stats.sumPercG0NotShaved += (double)stats.numRHSObjNumG0NotShaved/constraintsPB.size()*100;
        }
        if (cardinalities.size() > 0) {
          ++stats.nSoluExistCard;
          stats.sumPercCardG0 += (double)stats.numCardObjNumG0NotShaved/cardinalities.size()*100;
        }
        
        if (found_inconsistent or conflict) { // may be set when updating RHS of cardinalities
          cout << endl << "found_inconsistent.........conflict? " << (conflict? 1:0) << endl;
          conflict = true; 
          updateStatusConflictAtDLZero(); 
          return;
        }
      
        for (uint i = 0; !conflict and i < cardIds.size(); ++i) setAllLitsToTrueInCardinality(cardIds[i]);
        for (uint i = 0; !conflict and i < pbs.size();     ++i) {
          if (!useCounter[pbs[i]]) watchMoreLitsInPB(pbs[i]); 
          setAllLitsToTrueInPB(pbs[i]);
        }
        if (conflict) {
          assert(model.currentDecisionLevel() == 0);
          cout << "conflicting at dl 0 after updating all RHS " << endl;
          updateStatusConflictAtDLZero();
          return;
        }
      }
      
      // reuse trail (DL >= 0), update PB RHS only if the ctr will not be falsified (slkMC >= 0)
      if (!BT0 and update_rhs and stats.numOfSolutionsFound > 1) {
        assert(obj_num != -1);
        PBConstraint& obj = constraintsPB[obj_num];
        sumOfWatches[obj_num] += (obj.getConstant() - next_obj_rhs);
        obj.setConstant(next_obj_rhs);
        
        bool found_inconsistent = false;
        updateRHSOfPBsAtDLGth0(); // update RHS only if the ctr will not be falsified (SNF >= 0)
        found_inconsistent = updateRHSOfCardsAtDLGth0(cardIds);
        
        if (constraintsPB.size() > 0) {
          ++stats.nSoluExistPB;
          stats.sumPercE0 += (double)stats.numRHSObjNumE0/constraintsPB.size()*100;
          stats.sumPercG0Shaved += (double)stats.numRHSObjNumG0Shaved/constraintsPB.size()*100;
          stats.sumPercG0NotShaved += (double)stats.numRHSObjNumG0NotShaved/constraintsPB.size()*100;
        }
        if (cardinalities.size() > 0) {
          ++stats.nSoluExistCard;
          stats.sumPercCardG0 += (double)stats.numCardObjNumG0NotShaved/cardinalities.size()*100;
        }
        ++stats.numPercValid;
        stats.sumPercValid += (double)(stats.numValidUpdatesPB + stats.numValidUpdatesCard)/(constraintsPB.size() + cardinalities.size())*100;
        stats.sumPercValidPB += (constraintsPB.size() > 0 ? (double)stats.numValidUpdatesPB/constraintsPB.size()*100 : 0);
        stats.sumPercValidCard += (cardinalities.size() > 0 ? ((double)stats.numValidUpdatesCard/cardinalities.size()*100) : 0);
        stats.sumPercValidPBEnoughWatches += (constraintsPB.size() > 0 ? ((double)stats.tryToWatchMoreLitsEnough/constraintsPB.size()*100) : 0);
        
        if (found_inconsistent) {
          cout << endl << "found_inconsistent.........!" << endl;
          backjumpToDL(0);
          conflict = true; 
          updateStatusConflictAtDLZero(); 
          return;
        }
        if (cardIds.size() > 0) {
          backjumpToDL(0);  // updateRHSOfCardsAtDLGth0 found units in cardinalities!
          for (int i = 0; !conflict and i < (int)cardIds.size(); ++i) setAllLitsToTrueInCardinality(cardIds[i]);
          if (conflict) {
            cout << "conflicting at dl 0 after updating all RHS " << endl;
            assert(model.currentDecisionLevel() == 0);
            updateStatusConflictAtDLZero();
            return;
          }
        }
      }
      
      if (BT0) backjumpToDL(0);
      
      if (!update_rhs and !multiObj and stats.numOfSolutionsFound > 1) {
        assert(obj_num != -1);
        PBConstraint& obj = constraintsPB[obj_num];
        assert(obj.getSize() == auxConstraint.getSize());
        sumOfWatches[obj_num] += (obj.getConstant() - rhs);
        obj.setConstant(rhs);
      }
      
      if (model.currentDecisionLevel() != 0) {
        bool objIsConflicting, objIsPropagating;
        int dlToBackjumpTo = lowestDLAtWhichConstraintPropagates( auxConstraint, objIsConflicting, objIsPropagating);
        if ( dlToBackjumpTo != -1 ) {
          assert( dlToBackjumpTo < model.currentDecisionLevel() );
          backjumpToDL(dlToBackjumpTo);
        }
        assert(constraintIsConflictingOrPropagating(auxConstraint));
      }
      
      if (stats.numOfSolutionsFound == 1 or (!update_rhs and multiObj)) {
        objectiveFunctions.push_back(constraintsPB.size()); // New objective function, // objective is already sorted
        obj_num = (int)constraintsPB.size(); 
        assert(stats.numOfSolutionsFound == 1 or !update_rhs);
        
        if (multiObj) {
          assert(!update_rhs);
          removeUnits(auxConstraint);
        }
        addAndPropagatePBConstraint(auxConstraint, true,0,0, (multiObj? false:true)); // if only one obj constraint, don't simplify it.
      }
      else {
        assert(stats.numOfSolutionsFound > 1 and obj_num != -1 and obj_num < (int)constraintsPB.size());
        assert(constraintsPB[obj_num].getConstant() == rhs);
        assert(constraintsPB[obj_num].getSize() == auxConstraint.getSize());
        assert(!useCounter[obj_num] or sumOfWatches[obj_num] == maxSumOfConstraintMinusRhs(auxConstraint) - auxConstraint.getIthCoefficient(0));
        if (!useCounter[obj_num]) watchMoreLitsInPB(obj_num);
        checkObjectiveIsConflictingOrPropagating(obj_num);
      }
      continue;
    }  // END new solution found
    
    strat.reportDecision(model.currentDecisionLevel());
    takeDecisionForVar(decVar);
  }
}

bool Solver::updateRHSOfPBsAtDL0 (vector<int>& pbs) {
  assert(!conflict && model.currentDecisionLevel() == 0 && stats.numOfSolutionsFound > 0);
  stats.numRHSObjNumG0NotShaved = stats.numRHSObjNumG0Shaved = stats.numRHSObjNumE0 = 0;
  
  for (int k = 0; k < (int)constraintsPB.size(); ++k) {
    if (k == obj_num) continue;
    PBConstraint& c = constraintsPB[k];
    if (c.getObjectiveRHSNum() == 0) {
      ++stats.numRHSObjNumE0; 
      assert(!shavedPBs[k]);
      continue;
    }
    if (shavedPBs[k]) {++stats.numRHSObjNumG0Shaved; continue;}
    int new_rhs = latest_rhs(c.getIndependentRHS(), c.getObjectiveRHS(), next_obj_rhs);
    int constant = c.getConstant();
    if (new_rhs <= constant) {stats.numSmallerNewRHS += (new_rhs < constant); continue;}
    ++stats.numRHSObjNumG0NotShaved;
    c.setConstant(new_rhs);
    sumOfWatches[k] += (constant - new_rhs);
    if (sumOfWatches[k] < 0) pbs.push_back(k); // propagating or conflicting
  }
  return false;
}

// reuse trail (dl >= 0), only update the RHS of constraints that will not be propagating or conflicting (wslkMC >= 0) 
// we don't check for conflicts or propagation for any constraints, because they're too costly, and the DL could be different
bool Solver::updateRHSOfPBsAtDLGth0 () {
  assert(!conflict && stats.numOfSolutionsFound > 0);
  stats.numRHSObjNumG0NotShaved = stats.numRHSObjNumG0Shaved = stats.numRHSObjNumE0 = 0;
  stats.numValidUpdatesPB = stats.tryToWatchMoreLitsEnough = 0;
  
  for (int k = 0; k < (int)constraintsPB.size(); ++k) {
    if (k == obj_num) continue;
    PBConstraint& c = constraintsPB[k];
    if (c.getObjectiveRHSNum() == 0) {
      ++stats.numRHSObjNumE0; 
      assert(!shavedPBs[k]);
      continue;
    }
    if (shavedPBs[k]) {++stats.numRHSObjNumG0Shaved; continue;}
    int constant = c.getConstant();
    int new_rhs = latest_rhs(c.getIndependentRHS(), c.getObjectiveRHS(), next_obj_rhs);
    if (new_rhs <= constant) {stats.numSmallerNewRHS += (new_rhs < constant); continue;}
    
    ++stats.numRHSObjNumG0NotShaved;
    long long tempWslkMCNewRhs = sumOfWatches[k]; 
    tempWslkMCNewRhs += (constant - new_rhs);
    
    if (tempWslkMCNewRhs < 0) { // conflicting or propagating
      if (useCounter[k]) continue; 
      tryToWatchMoreLits(k, tempWslkMCNewRhs);
      if (tempWslkMCNewRhs < 0) continue; // no enough watches
      ++stats.tryToWatchMoreLitsEnough; // found enough watches --> update the RHS of watched PB
    }
    
    c.setConstant(new_rhs);
    sumOfWatches[k] = tempWslkMCNewRhs;
    ++stats.numValidUpdatesPB;
  }

  return false;
}

bool Solver::updateRHSOfCardsAtDL0 (vector<int>& cardIds) {
  assert(!conflict && model.currentDecisionLevel() == 0 && stats.numOfSolutionsFound > 0);
  stats.numCardObjNumG0Shaved = stats.numCardObjNumG0NotShaved = 0;
  
  for (uint k = 0; k < cardinalities.size(); ++k) {
    Cardinality& c = cardinalities[k];
    if (c.getObjectiveRHSNum() == 0) {assert(!shavedCards[k]); continue;}
    if (shavedCards[k]) {++stats.numCardObjNumG0Shaved; continue;}
    
    int new_rhs = latest_rhs(c.getIndependentRHS(), c.getObjectiveRHS(), next_obj_rhs);
    int old_rhs = c.getDegree();
    if (new_rhs <= old_rhs) {stats.numSmallerNewRHSCard += (new_rhs < old_rhs); continue;}
    
    ++stats.numCardObjNumG0NotShaved;
    c.setDegree(new_rhs);
    int ctrSize = c.getSize();
    if (new_rhs > ctrSize) {
      cout << "found_inconsistent, k " << k << ", new_rhs = " << new_rhs << ", ind_rhs " << c.getIndependentRHS() << ", obj_rhs " << c.getObjectiveRHS() << " * " << next_obj_rhs << ", ctrSize " << ctrSize << endl;
      return true;
    }
    if (new_rhs == ctrSize) {
      cardIds.push_back((int)k);
      continue;
    }
    
    int startIdx = c.getWatchIdx();
    int watchIdx = startIdx;
    assert(watchIdx > old_rhs);
    // Watch more true lit or false lit (highest level)
    for(int i = old_rhs+1; i <= new_rhs; ++i) {
      int lit_old = c.getIthLiteral(i); // to be replaced by a non-false lit
      if (not model.isFalseLit(lit_old)) {
        if (lit_old > 0) positiveCardLists[lit_old].emplace_back(k, i);
        else             negativeCardLists[-lit_old].emplace_back(k, i);
        continue;
      }
      int lit = 0;
      bool isFalse = true;
      watchIdx = startIdx = max(watchIdx, i+1);
      
      while (watchIdx < ctrSize && (isFalse = model.isFalseLit(lit = c.getIthLiteral(watchIdx))) )
        watchIdx++;
        
      if (isFalse and c.getNumBackjump() != stats.numOfBackjump) { // circular search
        assert(lit == 0 or model.isFalseLit(lit));
        c.setNumBackjump(stats.numOfBackjump);
        watchIdx = i + 1;
        while (watchIdx < startIdx && (isFalse = model.isFalseLit(lit = c.getIthLiteral(watchIdx))) )
          watchIdx++;
      }
      
      if (not isFalse) { // watch more lit
        assert(c.getIthLiteral(watchIdx) == lit);
        assert(not model.isFalseLit(lit));
        c.setIthLiteral(watchIdx, lit_old);
        c.setIthLiteral(i, lit);
        if (lit > 0) positiveCardLists[lit].emplace_back(k, i);
        else         negativeCardLists[-lit].emplace_back(k, i);
        assert(not model.isFalseLit(c.getIthLiteral(i))); // the new found no-false lit
        assert(model.isFalseLit(c.getIthLiteral(watchIdx))); // the old false lit at mid
      }
      else { // if it's inconsistent, conflict analysis should be able to found conflict at dl 0
        conflict = true;
        return false;
      }
    }
    c.setWatchIdx(new_rhs+1);
  }
  return false;
}


// reuse trail (DL >= 0), only update the RHS of cardinalities that will have enough watches 
// otherwise they could be conflicting or propagating at different levels, it's very costly to detect
bool Solver::updateRHSOfCardsAtDLGth0 (vector<int>& cardIds) {
  assert(!conflict && stats.numOfSolutionsFound > 0);
  stats.numValidUpdatesCard = stats.numCardObjNumG0NotShaved = 0;
  
  for (uint k = 0; k < cardinalities.size(); ++k) {
    Cardinality& c = cardinalities[k];
    if (c.getObjectiveRHSNum() == 0) {assert(!shavedCards[k]); continue;}
    int new_rhs = latest_rhs(c.getIndependentRHS(), c.getObjectiveRHS(), next_obj_rhs);
    int old_rhs = c.getDegree();
    if (new_rhs <= old_rhs) {stats.numSmallerNewRHSCard += (new_rhs < old_rhs); continue;}
    
    assert(new_rhs > old_rhs);
    
    int ctrSize = c.getSize();
    if (new_rhs > ctrSize) {c.setDegree(new_rhs); return true;}
    ++stats.numCardObjNumG0NotShaved;
    if (new_rhs == ctrSize) { // all lits must be true
      c.setDegree(new_rhs);
      cardIds.push_back((int)k);
      continue;
    }
    
    int startIdx = c.getWatchIdx();
    int watchIdx = startIdx;
    assert(watchIdx > old_rhs);
    // Watch more true lit or false lit (highest level)
    int i;
    for(i = old_rhs+1; i <= new_rhs; ++i) {
      int lit_old = c.getIthLiteral(i); // to be replaced by a non-false lit
      if (not model.isFalseLit(lit_old)) { 
           //// don't watch them here, because the RHS might not be updated
        //if (lit_old > 0) positiveCardLists[lit_old].emplace_back(k, i);
        //else             negativeCardLists[-lit_old].emplace_back(k, i);
        continue;
      }
      int lit = 0;
      bool isFalse = true;
      watchIdx = startIdx = max(watchIdx, i+1);
      
      while (watchIdx < ctrSize && (isFalse = model.isFalseLit(lit = c.getIthLiteral(watchIdx))) )
        watchIdx++;
        
      if (isFalse and c.getNumBackjump() != stats.numOfBackjump) { // circular search
        assert(lit == 0 or model.isFalseLit(lit));
        c.setNumBackjump(stats.numOfBackjump);
        watchIdx = i + 1;
        while (watchIdx < startIdx && (isFalse = model.isFalseLit(lit = c.getIthLiteral(watchIdx))) )
          watchIdx++;
      }
      
      if (not isFalse) { // watch more lit
        assert(c.getIthLiteral(watchIdx) == lit);
        assert(not model.isFalseLit(lit));
        c.setIthLiteral(watchIdx, lit_old);
        c.setIthLiteral(i, lit); // we just exchange the two unwatched lits, but not directly watch them
        //if (lit > 0) positiveCardLists[lit].emplace_back(k, i);
        //else         negativeCardLists[-lit].emplace_back(k, i);
        assert(not model.isFalseLit(c.getIthLiteral(i))); // the new found no-false lit
        assert(model.isFalseLit(c.getIthLiteral(watchIdx))); // the old false lit at mid
      }
      else 
        break;
    }
    
    if (i != new_rhs + 1) { 
      continue; // break the loop in advance, there is no enough watches
    }
    ++stats.numValidUpdatesCard;
    c.setDegree(new_rhs);
    c.setWatchIdx(new_rhs+1);
    for(int i = old_rhs+1; i <= new_rhs; ++i) {
      int lit_old = c.getIthLiteral(i);
      assert(not model.isFalseLit(lit_old));
      if (lit_old > 0) positiveCardLists[lit_old].emplace_back(k, i);
      else             negativeCardLists[-lit_old].emplace_back(k, i);
    }
  }
  return false;
}


void Solver::setAllLitsToTrueInCardinality(int cardId) {
  assert(!conflict);
  int numFalse = 0;
  Cardinality& c = cardinalities[cardId];
  int degree = c.getDegree();
  
  assert(!BT0 or (BT0 and degree == c.getSize()));
  
  if (degree == c.getSize()) {
    assert(model.currentDecisionLevel() == 0);
    for (int i = 0; i < degree; ++i) {
      int lit = c.getIthLiteral(i);
      if (model.isFalseLit(lit)) {
        cout << "found a conflict when setting all lits to true in card " << cardId << endl;
        conflict = true; typeConflict = CONFLICT_CARD; cardinalityConflictNum = cardId; 
        return;
      }
      else if (model.isUndefLit(lit)) {
        strat.reportPropagationInCard();
        setTrueDueToReason(lit,Reason(cardId,Reason::CARDINALITY));
      }
    }
    return;
  }
  
  for(int i = 0; i <= degree; ++i) {
    int lit = c.getIthLiteral(i);
    if (model.isUndefLit(lit)) {
      strat.reportPropagationInCard();
      setTrueDueToReason(lit,Reason(cardId,Reason::CARDINALITY));
    }
    else if (model.isFalseLit(lit)) {++numFalse; assert(model.getDLOfLit(lit) == model.currentDecisionLevel());}
  }
  
  assert(numFalse >= 1); 
  if (numFalse > 1) {  // there might be multiple propagating cards and this lit should be set to true, 
                       // but it has already been set to false by one of previous propagating card.
    conflict = true; typeConflict = CONFLICT_CARD; cardinalityConflictNum = cardId;
  }
  
  for(int i = degree+1; i < c.getSize(); ++i) { // should hold
    assert(model.isFalseLit(c.getIthLiteral(i)));
  }
}

void Solver::setAllLitsToTrueInPB ( const int ctrId) {
  assert(!conflict);
  const long long& wslkMC = sumOfWatches[ctrId];
  if (wslkMC >= 0) return; // it may hold only if the constraint is watched, and more enough lits are watched.
  assert(wslkMC < 0);

  PBConstraint& c = constraintsPB[ctrId];
  long long wslk = wslkMC + abs(c.getIthCoefficient(0)); 
  if (wslk < 0) { // it's possiblly conflicting only when DL = 0, otherwise we will not update rhs if wslkMC < 0
    assert(BT0 and model.currentDecisionLevel() == 0);
    cout << "found a conflict when setting all lits to true in PB " << ctrId << "......, BT0? " << BT0 << " ,current dl " << model.currentDecisionLevel() << endl;
    conflict = true; typeConflict = CONFLICT_PB; constraintConflictNum = ctrId;
    return;
  }
  
  assert(wslk >= 0);
  int size = c.getSize();
  int idx = 0; 
  while (idx < size and abs(c.getIthCoefficient(idx)) > wslk) {
    int lit = c.getIthLiteral(idx);
    if (model.isUndefLit(lit)) {
      strat.reportPropagationInPBCounter();
      setTrueDueToReason(lit,Reason(ctrId,Reason::PB_CONSTRAINT));
    }
    ++idx;
  }
  c.setMaxWIdx(idx);
  c.setNumBackjump(stats.numOfBackjump);
}

// conflicting at dl 0
bool Solver::constraintIsContradiction (const WConstraint & c) const {
  long long maxSum = 0;
  for (int i = 0; i < c.getSize(); ++i) { 
    int lit  = c.getIthLiteral(i);
    int coef = c.getIthCoefficient(i);
    if (!model.isFalseLit(lit) or model.getDLOfLit(lit) > 0) maxSum += coef; 
  }
  if (maxSum < c.getConstant()) return true;
  else return false;
}

bool Solver::constraintIsTrue ( const WConstraint & c) const { 
  assert(model.currentDecisionLevel() == 0);
  long long minSum = -c.getConstant();
  for (int i = 0; minSum < 0 && i < c.getSize(); ++i) { 
    int lit  = c.getIthLiteral(i);            
    int coef = c.getIthCoefficient(i);
    if (model.isTrueLit(lit)) minSum += abs(coef); 
  }
  if (minSum >= 0) return true;
  return false;
}


int Solver::maxUnassCoefOfConstraint(const WConstraint & c) const {
  int max = 0;
  for (int i = 0; i < c.getSize(); ++i) { 
    int  lit  = c.getIthLiteral(i);            
    int  coef = c.getIthCoefficient(i);
    if ( model.isUndefLit(lit) and max < coef ) max = coef;
  }
  return max;
}

long long Solver::maxSumOfConstraintMinusRhs (const WConstraint & c) const {
  long long maxSum = -c.getConstant();
  for (int i = 0; i < c.getSize(); ++i) { 
    int lit  = c.getIthLiteral(i);            
    int coef = c.getIthCoefficient(i);
    assert(coef > 0);
    if ( not model.isFalseLit(lit) ) maxSum += coef; 
  }
  return maxSum;
}
  
long long Solver::maxSumOfConstraintMinusRhsPropagated(const WConstraint & c) const {
  long long maxSum = -c.getConstant();
  for (int i = 0; i < c.getSize(); ++i) { 
    int lit  = c.getIthLiteral(i);            
    int coef = c.getIthCoefficient(i);
    if ( not model.isFalseLit(lit) or not model.isLitPropagatedPB(lit)) maxSum += abs(coef); 
  }
  return maxSum;
}

int  Solver::computeLBD (const WConstraint& c) const {
  static unordered_set<int> DLs; DLs.clear();
  for (int i = 0; i < c.getSize(); ++i) {  
    int lit = c.getIthLiteral(i);
    if (not model.isUndefLit(lit)) {
      int DL = model.getDLOfLit(lit);
      if (DL > 0) DLs.insert(DL);
    }
  }
  return DLs.size();
}

int  Solver::computeLBD (const vector<int>& c) const {
  static unordered_set<int> DLs; DLs.clear();
  for (uint i = 0; i < c.size() ;++i)
    if (not model.isUndefLit(c[i])) {
      int DL = model.getDLOfLit(c[i]);
      if (DL > 0) DLs.insert(DL);
    }
      
  return DLs.size();
}

void Solver::increaseScoresOfVars (const WConstraint& constraint) {
  for (int i = 0; i < constraint.getSize(); ++i) {
    int lit = constraint.getIthLiteral(i);
    increaseActivityScoreOfVar(abs(lit));
  }
}

 // The instantiation C^i of a constraint C is the constraint obtained from C by:
  //  -instantiating all literals lit of prev_S(C) as follows:
  //     if lit is false in S_previousDLs then replace lit by 0
  //     if lit is true  in S_previousDLs then replace lit by 1
  //  -instantiating all literals not defined in S by replacing them by 1.

WConstraint Solver::instantiateConstraint (WConstraint& c) const {
  int k = c.getConstant();
  WConstraint constraint;

  for (int i = 0; i < c.getSize(); ++i) {
    int lit = c.getIthLiteral(i);
    int coeff = c.getIthCoefficient(i);
    if (model.isUndefLit(lit)) k -= coeff;
    else {
      int dl = model.getDLOfLit(lit);
      if (dl < model.currentDecisionLevel()) { if (model.isTrueLit(lit)) k -= coeff;}
      else constraint.addMonomial(coeff,lit);
    }
  }
  
  constraint.setConstant(max(0, k));
  return constraint;
}

int Solver::lowestDLAtWhichClausePropagates (const WConstraint & c) const {
  assert(c.isClause());
  int maxDL = -1;
  int secondMaxDL = -1;
  int nMax = 0;
  for (int i = 0; i < c.getSize(); ++i) {
    if (not model.isFalseLit(c.getIthLiteral(i))) return -1;
    else {
      int dl = model.getDLOfLit(c.getIthLiteral(i));
      if (dl > maxDL) {secondMaxDL = maxDL; maxDL = dl; nMax = 1;}
      else if (dl == maxDL) ++nMax;
      else if (dl > secondMaxDL) secondMaxDL = dl;
    }
  }
  
  if (nMax == 1) {if (secondMaxDL == -1) secondMaxDL = 0; return secondMaxDL;}
  else return -1;
}

 int Solver::lowestDLAtWhichConstraintPropagates (const WConstraint & c, bool& isConflicting, bool& isPropagating) {

  if (c.isClause()) return lowestDLAtWhichClausePropagates(c);

  struct Triple{
    int coeff;
    int lit;
    int dl;    
    Triple(){}
    Triple(int c, int l, int d):coeff(c),lit(l),dl(d){}
  };
  
  static vector<Triple> coeffLitDL; // contains initially true/false literals
  coeffLitDL.clear();
  long long int sumOfNonFalseMinusRHS = -c.getConstant();
  int maxUnassigned = 0; 
  for (int i = 0; i < c.getSize(); ++i) {
    int l = c.getIthLiteral(i);
    int coeff = c.getIthCoefficient(i);
    if (not model.isFalseLit(l)) sumOfNonFalseMinusRHS += coeff;
    if (model.isUndefLit(l)) maxUnassigned = max(maxUnassigned,coeff);
    else coeffLitDL.push_back({coeff,l,model.getDLOfLit(l)});
  }

  sort(coeffLitDL.begin(),coeffLitDL.end(),
              [](const Triple& t1, const Triple& t2){return t1.dl > t2.dl;});
  coeffLitDL.push_back({0,0,0}); // to make sure next dl always exists
  
  //if(sumOfNonFalseMinusRHS - maxUnassigned >= 0) {cout << "err: sumOfNonFalseMinusRHS " << sumOfNonFalseMinusRHS << ", maxUnassigned " << maxUnassigned << endl << flush;  }
  assert(sumOfNonFalseMinusRHS - maxUnassigned < 0);
  int bestSoFar = coeffLitDL.size() == 0?0:coeffLitDL[0].dl;
  maxSumMinusRhs = sumOfNonFalseMinusRHS;
  
  isConflicting = true; isPropagating = false;
  for (uint i = 0; i < coeffLitDL.size() - 1; ++i) {
    if (model.isFalseLit(coeffLitDL[i].lit)) sumOfNonFalseMinusRHS += coeffLitDL[i].coeff;
    maxUnassigned = max(maxUnassigned,coeffLitDL[i].coeff);
    // If we finish the decision level and sumOfNonFalseMinusRHS - maxUnassigned < 0 then propagate
    if (coeffLitDL[i].dl != coeffLitDL[i+1].dl and sumOfNonFalseMinusRHS - maxUnassigned < 0) {
      bestSoFar = coeffLitDL[i+1].dl;
      maxSumMinusRhs = sumOfNonFalseMinusRHS;
      if (sumOfNonFalseMinusRHS >= 0) {
        isConflicting = false; 
        isPropagating = true;
      }
    }
  }
  
  if (bestSoFar == model.decisionLevel) return -1; // backjump to model.decisionLevel means no BJ
  else return bestSoFar;
}

 int Solver::lowestDLAtWhichPBPropagates (const int pbId, bool& isConflicting, bool& isPropagating) {

  struct Triple{
    int coeff;
    int lit;
    int dl;    
    Triple(){}
    Triple(int c, int l, int d):coeff(c),lit(l),dl(d){}
  };
  
  static vector<Triple> coeffLitDL; // contains initially true/false literals
  coeffLitDL.clear();
  PBConstraint& c = constraintsPB[pbId];
  long long int sumOfNonFalseMinusRHS = sumOfWatches[pbId] + c.getIthCoefficient(0);
  
  for (int i = 0; i < c.getSize(); ++i) {
    int l = c.getIthLiteral(i);
    int coeff = c.getIthCoefficient(i);
    coeffLitDL.push_back({coeff,l,model.getDLOfLit(l)});
  }
  
  sort(coeffLitDL.begin(),coeffLitDL.end(),
              [](const Triple& t1, const Triple& t2){return t1.dl > t2.dl;});
  coeffLitDL.push_back({0,0,0}); // to make sure next dl always exists
  
  isConflicting = isPropagating = false;

  if(sumOfNonFalseMinusRHS < 0) {
    isConflicting = true; 
  }
  
  int bestSoFar = coeffLitDL.size() == 0?0:coeffLitDL[0].dl;
  int maxUnassigned = 0; 
  
  for (uint i = 0; i < coeffLitDL.size() - 1 and coeffLitDL[i].dl > 0; ++i) {
    if (coeffLitDL[i].dl > 0 and model.isFalseLit(coeffLitDL[i].lit)) sumOfNonFalseMinusRHS += coeffLitDL[i].coeff;
    if (coeffLitDL[i].dl > 0 or  model.isUndefLit(coeffLitDL[i].lit)) maxUnassigned = max(maxUnassigned,coeffLitDL[i].coeff);
    // If we finish the decision level and sumOfNonFalseMinusRHS - maxUnassigned < 0 then propagate
    if (coeffLitDL[i].dl != coeffLitDL[i+1].dl and sumOfNonFalseMinusRHS - maxUnassigned < 0) {
      bestSoFar = coeffLitDL[i+1].dl;
      if (sumOfNonFalseMinusRHS >= 0) {
        isConflicting = false; 
        isPropagating = true;
      }
      else {
        isConflicting = true; 
        isPropagating = false;
      }
    }
  }
  
  if (!isConflicting and !isPropagating) {
    return -1;
  }
  return bestSoFar;
}

// also need to watch more false lits with highest DL
 int Solver::lowestDLAtWhichCardinalityPropagatesOrConflicts (const int cardId, const int startFalseIdx, bool& isConflicting, bool& isPropagating) {

  struct Triple{
    int lit;
    int dl;
    int idx;
    Triple(){}
    Triple(int l, int d, int i):lit(l),dl(d),idx(i) {}
  };
  
  static vector<Triple> litDLWatched, litDL; // contains initially true/false literals
  litDLWatched.clear(); litDL.clear();
  Cardinality& c = cardinalities[cardId];
  int size   = c.getSize();
  int degree = c.getDegree();
  long long int sumOfNonFalseMinusRHS = -degree;

  //int numFalseLitWatched = 0; 
  for (int i = 0; i < startFalseIdx; ++i) {
    int l = c.getIthLiteral(i);
    if (not model.isFalseLit(l)) ++sumOfNonFalseMinusRHS;
    litDLWatched.push_back({l, model.getDLOfLit(l), i}); 
  }
  //assert(numFalseLitWatched <= 1);  // the card is satisfied before, so it has at most one watched false lit (is propagating), 
                                    // and the false lit has the hightest DL among all false lits.
  for (int i = startFalseIdx; i < size; ++i) {
    int l = c.getIthLiteral(i);
    assert(model.isFalseLit(l));
    litDL.push_back({l, model.getDLOfLit(l), i}); 
  }
  
  sort(litDL.begin(),litDL.end(),
              [](const Triple& t1, const Triple& t2){return t1.dl > t2.dl;});
  
  assert(sumOfNonFalseMinusRHS <= 0); // no matter which case, we should watch more false lits with highest dl
  int j = 0;
  for (int i = startFalseIdx; i <= degree; ++i) {
    int falseLit = c.getIthLiteral(i);
    assert(model.isFalseLit(falseLit));
    for (; j < (int)litDL.size(); ++j) {
      int lit = litDL[j].lit;
      if (model.isFalseLit(lit)) {
        assert(c.getIthLiteral(litDL[j].idx) == lit );
        
        if (i > litDL[j].idx ) {
          assert(litDL[j].dl >= model.getDLOfLit(falseLit)); 
          assert(model.isFalseLit(litDL[j].lit));
          continue;
        }  // it's a flase lit that has been replaced by a false lit with highest DL.
        c.setIthLiteral(litDL[j].idx, falseLit); // put to front the current latest falsified literal, which is more close to the lit at degree.
        c.setIthLiteral(i, lit);
        litDL[j].lit = falseLit;
        litDL[j].dl  = model.getDLOfLit(falseLit);
        assert(c.getIthLiteral(litDL[j].idx) == falseLit);
        assert(model.getDLOfLit(falseLit) == litDL[j].dl);
        
        for (auto& t : litDL) 
          if (t.idx == i) {t.lit = lit; t.dl = model.getDLOfLit(lit); break;}
        // should sort again, its dl meight be samller than the dl of next false lit
        sort(litDL.begin() + j, litDL.end(), [](const Triple& t1, const Triple& t2) {return t1.dl > t2.dl;});
        
        if (lit > 0) positiveCardLists[lit].emplace_back(cardId, i);
        else         negativeCardLists[-lit].emplace_back(cardId, i);
        break;
      }
    }
  }
  
  for (auto& t : litDLWatched) litDL.push_back(t);
  litDL.push_back({0,0,0}); // to make sure next dl always exists
  int bestSoFar = 0;
  
  isConflicting = isPropagating = false;
  sort(litDL.begin(),litDL.end(),
            [](const Triple& t1, const Triple& t2){return t1.dl > t2.dl;});
            
  bestSoFar = litDL[0].dl;
  
  for (uint i = 0; sumOfNonFalseMinusRHS < 1 and i < litDL.size() - 1; ++i) {
    if (model.isFalseLit(litDL[i].lit)) sumOfNonFalseMinusRHS += 1;
    
    if (litDL[i].dl != litDL[i+1].dl and sumOfNonFalseMinusRHS - 1 < 0) {
      bestSoFar = litDL[i+1].dl;
      if (sumOfNonFalseMinusRHS == 0) {
        isConflicting = false; 
        isPropagating = true;
      }
      else {
        isConflicting = true; 
        isPropagating = false;
      }
    }
  }
  
  if (!isConflicting and !isPropagating) return -1;
  
  return bestSoFar;
}

// Cadical version
void Solver::visitWatchList (int lit) {
  
  vector<WatchListElem>& wl = (lit>0?positiveWatchLists[lit]:negativeWatchLists[-lit]);
  if (wl.size() == 0) return;
  
  const auto end = wl.end();
  auto itWL = wl.begin();
  auto itWL_kept = itWL; 
  while (itWL != end) {
    WatchListElem& e = *itWL_kept++ = *itWL++;
    if (model.isTrueLit(e.cachedLit)) continue;
    
    Clause cl = clauses[e.clauseId];
    int l0 = cl.getIthLiteral(0);  int l1 = cl.getIthLiteral(1);
    const int otherLit = l0 ^ l1 ^ lit; 
    
    if (model.isTrueLit(otherLit)) {
      e.cachedLit = otherLit;
      continue;
    }
    
    const auto middle = cl.middleNonWatched();
    const auto end    = cl.end();
    auto k = middle;
    // Find replacement watch 'r' at position 'k' 
    assert(cl.getWatchIdx() > 1 && cl.getWatchIdx() <= cl.getSize());
    int r = 0;
    bool isFalse = true;
    while (k != end && (isFalse = model.isFalseLit(r = *k)) )
      k++;
    
    if (isFalse) {
      assert(r == 0 or model.isFalseLit(r));
      k = cl.firstNonWatched(); // the 3rd lit
      while (k != middle && (isFalse = model.isFalseLit(r = *k)) )
        k++;
    }
    cl.setWatchIdx(k - cl.begin());
    
    if (not isFalse) { //we have found *k to be reselected
      if (model.isTrueLit(r)) e.cachedLit = r;  // Replacement satisfied,
      else {  // Found new unassigned replacement literal to be watched.
        assert(model.isUndefLit(r));
        cl.setIthLiteral(0, otherLit);
        cl.setIthLiteral(1, r);
        *k = lit;
        if (r > 0) positiveWatchLists[r].emplace_back(e.clauseId, lit);
        else       negativeWatchLists[-r].emplace_back(e.clauseId, lit);
        itWL_kept--;
      }
    }
    else if (model.isUndefLit(otherLit)) {
      strat.reportPropagationInClause();
      setTrueDueToReason(otherLit,Reason(e.clauseId,Reason::CLAUSE));
    }
    else {
      assert(model.isFalseLit(otherLit));
      conflict = true;
      typeConflict = CONFLICT_CLAUSE; 
      clauseConflictNum = e.clauseId;
      break;
    }
  }
  
  if (itWL_kept != itWL) {
    while(itWL != end) 
      *itWL_kept++ = *itWL++;
    wl.resize(itWL_kept - wl.begin());  // numElems, keep the allocatedInts
  }
}

// 2 pointers
void Solver::visitCardList (int lit) {
  vector<pair<int, int>>& wl = (lit>0?positiveCardLists[lit]:negativeCardLists[-lit]);
  if (wl.size() == 0) return;
  
  const auto end = wl.end();
  auto itWL = wl.begin();
  auto itWL_kept = itWL; 
  while (itWL != end) {
    auto& e = *itWL_kept++ = *itWL++;
    bool unwatch = propagateCardinalityCtr(e.first, e.second);
    if (conflict) break;
    if (unwatch) --itWL_kept;
  }
  if (itWL_kept != itWL) {
    while(itWL != end) {
      *itWL_kept++ = *itWL++;
    }
    wl.resize(itWL_kept - wl.begin());
  }
}

// move last position to current position
void Solver::visitPBWatches (int lit) { 
  
  vector<PBWatchElem>& wl = (lit>0?positivePBWatches[lit]:negativePBWatches[-lit]);
  if (wl.size() == 0) return;
  
  int nElems = wl.size();
  auto itWL = wl.begin();
  while (nElems != 0) {
    --nElems;
    auto& e = *itWL;
    assert(not useCounter[e.ctrId]);
    long long int& SNF = sumOfWatches[e.ctrId];
    SNF -= e.coef;

    bool unwatch = propagatePBCtrWatch(e.ctrId, SNF, e.idx, e.coef);
    if (unwatch) { e = wl.back(); wl.pop_back(); }
    else if (conflict) break; 
    else ++itWL;
  }
  
  if(conflict) {
    auto itWL_visited = wl.begin();
    while(itWL_visited <= itWL) {
      PBWatchElem& ve = *itWL_visited;
      sumOfWatches[ve.ctrId] += ve.coef;
      
      ++itWL_visited;
    }
    --model.lastPropagatedPBWatch;
  }
}

// move last position to current position
void Solver::visitPBWatchesLazily (int lit) { 
  
  vector<PBWatchElem>& wl = (lit>0?positivePBWatches[lit]:negativePBWatches[-lit]);
  if (wl.size() == 0) return;
  
  int nElems = wl.size();
  auto itWL = wl.begin();
  while (nElems != 0) {
    --nElems;
    auto& e = *itWL;
    assert(not useCounter[e.ctrId]);
    long long int& SNF = sumOfWatches[e.ctrId];
    SNF -= e.coef;
    if (SNF < 0) {
      bool unwatch = propagatePBCtrWatch(e.ctrId, SNF, e.idx, e.coef);
      if (unwatch) { e = wl.back(); wl.pop_back(); }
      else if (conflict) break; 
      else ++itWL;
    }
    else ++itWL;
  }
  
  if(conflict) {
    auto itWL_visited = wl.begin();
    while(itWL_visited <= itWL) {
      PBWatchElem& ve = *itWL_visited;
      sumOfWatches[ve.ctrId] += ve.coef;
      
      ++itWL_visited;
    }
    --model.lastPropagatedPBWatch;
  }
}


void Solver::visitPBCounterLists (int lit) {
  long long nVisited = 0; 
  int var = abs(lit);
  for (OccurListElem& e: (lit>0?positiveOccurLists[var]:negativeOccurLists[var])) {
    ++nVisited;
    assert(useCounter[e.ctrId]);
    long long & SNF = sumOfWatches[e.ctrId];
    SNF -= e.coefficient;
    
    if (SNF < 0 ) {
      ++stats.numLoadPBCounter;
      int maxCoef = constraintsPB[e.ctrId].getIthCoefficient(0); 
      long long wslk = SNF + maxCoef; 
      if (wslk < 0) {
        conflict = true; typeConflict = CONFLICT_PB; constraintConflictNum = e.ctrId;
        break;
      }
      assert(wslk < maxCoef);
      propagatePBCtrCounter(e.ctrId, wslk);
    }
  }
  
  if (conflict) {
    long long counter = 0;
    for (OccurListElem& e: (lit>0?positiveOccurLists[var]:negativeOccurLists[var])) {
      sumOfWatches[e.ctrId] += e.coefficient;
      ++counter;
      if (counter == nVisited) break;
    }
    --model.lastPropagatedPB;
  }
}


void Solver::visitPBCounterListsUniquePtr (int lit) {
  long long nVisited = 0; 
  int var = abs(lit);
  for (OccurListElem& e: (lit>0?positiveOccurLists[var]:negativeOccurLists[var])) {
    ++nVisited;
    assert(useCounter[e.ctrId]);
    long long & SNF = sumOfWatches[e.ctrId];
    SNF -= e.coefficient;
    
    if (SNF < 0 ) {
      int maxCoef = constraintsPB[e.ctrId].getIthCoefficient(0); 
      long long wslk = SNF + maxCoef; 
      if (wslk < 0) {
        conflict = true; typeConflict = CONFLICT_PB; constraintConflictNum = e.ctrId;
        break;
      }
      assert(wslk < maxCoef);
      propagatePBCtrCounter(e.ctrId, wslk);
    }
  }
  
  if (conflict) {
    long long counter = 0;
    for (OccurListElem& e: (lit>0?positiveOccurLists[var]:negativeOccurLists[var])) {
      sumOfWatches[e.ctrId] += e.coefficient;
      ++counter;
      if(counter == nVisited) break;
    }
  }
}

// move last position to current position
void Solver::visitPBWatchesUniquePtr (int lit) { 
  
  vector<PBWatchElem>& wl = (lit>0?positivePBWatches[lit]:negativePBWatches[-lit]);
  if (wl.size() == 0) return;
  
  int nElems = wl.size();
  auto itWL = wl.begin();
  while (nElems != 0) {
    --nElems;
    auto& e = *itWL;
    assert(not useCounter[e.ctrId]);
    long long int& SNF = sumOfWatches[e.ctrId];
    SNF -= e.coef;

    bool unwatch = propagatePBCtrWatch(e.ctrId, SNF, e.idx, e.coef);
    if (unwatch) {
      e = wl.back();
      wl.pop_back();
    }
    else {if (conflict) break; ++itWL;}
  }
  
  if(conflict) {
    auto itWL_visited = wl.begin();
    while(itWL_visited <= itWL) {
      PBWatchElem& ve = *itWL_visited;
      sumOfWatches[ve.ctrId] += ve.coef;
      ++itWL_visited;
    }
  }
}

// move last position to current position
void Solver::visitPBWatchesUniquePtrLazily (int lit) { 
  
  vector<PBWatchElem>& wl = (lit>0?positivePBWatches[lit]:negativePBWatches[-lit]);
  if (wl.size() == 0) return;
  
  int nElems = wl.size();
  auto itWL = wl.begin();
  while (nElems != 0) {
    --nElems;
    auto& e = *itWL;
    assert(not useCounter[e.ctrId]);
    long long int& SNF = sumOfWatches[e.ctrId];
    SNF -= e.coef;
    if (SNF < 0) {
      bool unwatch = propagatePBCtrWatch(e.ctrId, SNF, e.idx, e.coef);
      if (unwatch) { e = wl.back(); wl.pop_back(); }
      else         { if (conflict) break; ++itWL;}
    }
    else ++itWL;
  }
  
  if(conflict) {
    auto itWL_visited = wl.begin();
    while(itWL_visited <= itWL) {
      PBWatchElem& ve = *itWL_visited;
      sumOfWatches[ve.ctrId] += ve.coef;
      
      ++itWL_visited;
    }
  }
}

void Solver::visitBinClause (int lit){
  vector<int>& bcl = (lit > 0?positiveBinClauses[lit]:negativeBinClauses[-lit]);
  if (bcl.empty()) return;

  for (auto& otherLit:bcl) {
    if (model.isFalseLit(otherLit)) {
      conflict = true;
      typeConflict = CONFLICT_BIN_CLAUSE;
      binClauseConflict = {lit,otherLit};
      return;
    }
    else if (model.isUndefLit(otherLit)) {
      setTrueDueToReason(otherLit,Reason(lit,Reason::BIN_CLAUSE));
      strat.reportPropagationInBinClause();
    }
  }
}

 // propagate differnet watch lists by priority using different pointers to trail
bool Solver::propagate () {
  assert(!conflict);
  if (!propagate_by_priority) return propagate_by_uniquePtr();
  
  while (true) {
        
    if (not model.areAllLitsPropagatedBinClause()) { // Bin clause propagation
      int lit = model.getNextLitToPropagateBinClause();
      assert(lit != 0); 
      visitBinClause(-lit);
    }
    else if (not model.areAllLitsPropagatedClause()) { // Clause propagation
      int lit = model.getNextLitToPropagateClause();
      assert(lit != 0);
      visitWatchList(-lit);//visits watch lists and reselects
    }
    else if (useCardinality && not model.areAllLitsPropagatedCard()) { // Cardinality propagation
      int lit = model.getNextLitToPropagateCard();
      assert(lit != 0);
      visitCardList(-lit);//visits card lists and reselects
    }
    else if (not model.areAllLitsPropagatedPBWatch()) { // PB Watched propagation
      int lit = model.getNextLitToPropagatePBWatch();
      assert(lit != 0); 
      //visitPBWatches(-lit); // the version in RoundingSat, visits PB watches and directly check for propagation
      visitPBWatchesLazily(-lit); //slightly changed version, visits PB watches and check for propagation only when the counter < 0
    }
    else if (not model.areAllLitsPropagatedPB()) { // PB Counter propagation
      int lit = model.getNextLitToPropagatePB();
      assert(lit != 0);
      visitPBCounterLists(-lit); //paper counter version
    }
    else {
      assert(not conflict);
      //checkAllConstraintsPropagated();
      return !conflict;
    }
    
    if (conflict) return !conflict;  
  }
}


 // propagate differnet watch lists at same time using unique pointer to trail
bool Solver::propagate_by_uniquePtr () {
  assert(!conflict);
  assert(!propagate_by_priority);
  
  while (true) {
    
    if (not model.areAllLitsPropagatedPB()) {
      int lit = model.getNextLitToPropagatePB();
      assert(lit != 0);
      visitBinClause(-lit);           if (conflict) {--model.lastPropagatedPB; return !conflict;}
      visitWatchList(-lit);           if (conflict) {--model.lastPropagatedPB; return !conflict;}
      visitCardList(-lit);            if (conflict) {--model.lastPropagatedPB; return !conflict;}
      //visitPBWatchesUniquePtr(-lit); if (conflict) {--model.lastPropagatedPB; return !conflict;} // the version in RoundingSat, visits PB watches and directly check for propagation
      visitPBWatchesUniquePtrLazily(-lit); if (conflict) {--model.lastPropagatedPB; return !conflict;} //slightly changed version, visits PB watches and check for propagation only when the counter < 0
      visitPBCounterListsUniquePtr(-lit); 
      
      if (conflict) {
        --model.lastPropagatedPB;
        lit = -lit;
        
        vector<PBWatchElem>& wl = (lit>0?positivePBWatches[lit]:negativePBWatches[-lit]);
        if (wl.size() == 0) return !conflict;
        
        for (PBWatchElem& e: wl) sumOfWatches[e.ctrId] += e.coef;
        
        return !conflict; 
      }
    }
    else {
      //checkAllConstraintsPropagated();
      return !conflict;
    }
  }
}

void Solver::addPBConstraintCounter (const PBConstraint & c) {
  ++stats.numOfCounterCtr;
  const int size = c.getSize();
  long long slack = -c.getConstant() - c.getIthCoefficient(0);
  for (int i=0; i < size; i++) {
    int lit = c.getIthLiteral(i);
    int coef = c.getIthCoefficient(i);
    if ( !model.isFalseLit(lit) or !model.isLitPropagatedPB(lit) ) slack += coef; 
    if (lit > 0) positiveOccurLists[lit].addElem(constraintsPB.size(), coef);
    else         negativeOccurLists[-lit].addElem(constraintsPB.size(), coef);
  }
  
  useCounter.push_back(true);
  sumOfWatches.push_back(slack);
  constraintsPB.push_back(c);
}

void Solver::addPBConstraintWatchedDL0 (PBConstraint& c) {
  ++stats.numOfWatchedCtrs;
  long long wslk = -c.getConstant() - abs(c.getIthCoefficient(0));
  int size = c.getSize();
  int i; 
  for (i = 0; wslk < 0 and i < size; ++i) {
    int lit = c.getIthLiteral(i);
    if (not model.isFalseLit(lit) or !model.isLitPropagatedPBWatch(lit) ) { // or use isLitPropagatedPB, it's same here
      int coef = c.getIthCoefficient(i);
      wslk += coef;
      c.setIthLitWatched(i, true);
      if (lit > 0) positivePBWatches[lit].emplace_back(constraintsPB.size(), coef, i);
      else         negativePBWatches[-lit].emplace_back(constraintsPB.size(), coef, i);
    }
  }

  useCounter.push_back(false);
  sumOfWatches.push_back(wslk);
  constraintsPB.push_back(c);
}

// not watch all false lits
void Solver::addPBConstraintWatchedDLGreaterThan0 (PBConstraint& c) {
  ++stats.numOfWatchedCtrs;
  assert(!propagate_by_priority or model.areAllLitsPropagatedPBWatch());
  const int size    = c.getSize(); 
  long long wslk    = -c.getConstant();
  static vector<int> falseIdx; falseIdx.clear();
  for (int i = 0; i < size; ++i) {
    int lit = c.getIthLiteral(i); 
    if(not model.isFalseLit(lit)) {
      int coef = c.getIthCoefficient(i);
      wslk += coef;
      c.setIthLitWatched(i, true);
      if (lit > 0) positivePBWatches[lit].emplace_back(constraintsPB.size(), coef, i);
      else         negativePBWatches[-lit].emplace_back(constraintsPB.size(), coef, i);
    }
    else falseIdx.push_back(i);
  }
  const int maxCoef = abs(c.getIthCoefficient(0));
  assert(wslk < maxCoef); // conflicting or propagating
  // sort by decreasing height of false lits
  sort(falseIdx.begin(), falseIdx.end(), 
       [&](const int & i1, const int & i2) { return model.getHeightOfVar(abs(c.getIthLiteral(i1))) > model.getHeightOfVar(abs(c.getIthLiteral(i2))); } );
       
  long long diff = maxCoef - wslk; 
  assert(diff > 0);
  
  for (int& idx : falseIdx) { // watch only first N false lits to make sure the sumNonFalseMinusK > maxCoef
    int lit = c.getIthLiteral(idx); int coef = c.getIthCoefficient(idx);
    diff -= coef;
    c.setIthLitWatched(idx, true);
    if (lit > 0) positivePBWatches[lit].emplace_back(constraintsPB.size(), coef, idx);
    else         negativePBWatches[-lit].emplace_back(constraintsPB.size(), coef, idx);
    if (diff <= 0) break;
  }
  
  useCounter.push_back(false);
  sumOfWatches.push_back(wslk-maxCoef);
  constraintsPB.push_back(c);
}


void Solver::propagateInitialConstraintWatch ( const int ctrId) {  // 2 optimizations
  const long long& wslkMC = sumOfWatches[ctrId];
  if(wslkMC < 0) {
    long long wslk = wslkMC + abs(constraintsPB[ctrId].getIthCoefficient(0)); 
    if(wslk < 0) {
      conflict = true; typeConflict = CONFLICT_PB; constraintConflictNum = ctrId;
      return;
    }
    PBConstraint& c = constraintsPB[ctrId];
    assert(wslk < abs(c.getIthCoefficient(0)));
    int size = c.getSize();
    int idx = 0;
    while (idx < size and abs(c.getIthCoefficient(idx)) > wslk) {
      int lit = c.getIthLiteral(idx);
      if (model.isUndefLit(lit)) {
        strat.reportPropagationInPBWatch();
        setTrueDueToReason(lit,Reason(ctrId,Reason::PB_CONSTRAINT));
      }
      ++idx;
    }
    c.setMaxWIdx(idx);
    c.setNumBackjump(stats.numOfBackjump);
  }
}

void Solver::propagateInitialConstraintCounter ( const int ctrId) {
  const long long& wslkMC = sumOfWatches[ctrId];
  if(wslkMC < 0) {
    long long wslk = wslkMC + constraintsPB[ctrId].getIthCoefficient(0); 
    if(wslk < 0) {
      conflict = true; typeConflict = CONFLICT_PB; constraintConflictNum = ctrId;
      return;
    }
    PBConstraint& c = constraintsPB[ctrId];
    assert(wslk < c.getIthCoefficient(0));
    int size = c.getSize();
    int idx = 0; 
    while (idx < size and c.getIthCoefficient(idx) > wslk) {
      int lit = c.getIthLiteral(idx);
      if (model.isUndefLit(lit)) {
        strat.reportPropagationInPBCounter();
        setTrueDueToReason(lit,Reason(ctrId,Reason::PB_CONSTRAINT));
      }
      ++idx;
    }
    c.setMaxWIdx(idx);
    c.setNumBackjump(stats.numOfBackjump);
  }
}

//// one search
//void Solver::tryToWatchMoreLits (const int ctrNum, long long& tempWslkMCNewRhs) {
  //++stats.tryToWatchMoreLits;
  //assert(!useCounter[ctrNum]);
  //long long& wslkMC = sumOfWatches[ctrNum];
  //assert(tempWslkMCNewRhs < 0); // this is only the temperory counter since the new rhs has not been applied
 
  //PBConstraint& c = constraintsPB[ctrNum];
  //const int size = c.getSize();
  //int i = c.getMaxWIdx();
  //if (c.getNumBackjump() < stats.numOfBackjump) {
    //c.setNumBackjump(stats.numOfBackjump);
    //i = 0;
  //}
  //for ( ; tempWslkMCNewRhs < 0 and i < size; ++i) {
    //int lit  = c.getIthLiteral(i); 
    //int coef = c.getIthCoefficient(i); 
    //if (coef > 0 && !model.isFalseLit(lit)) {
      //tempWslkMCNewRhs += coef;
      //wslkMC += coef;
      //c.setIthLitWatched(i, true);
      //if (lit > 0) positivePBWatches[lit].emplace_back(ctrNum, coef, i);
      //else         negativePBWatches[-lit].emplace_back(ctrNum, coef, i);
    //}
  //}
//}

 // circular search
void Solver::tryToWatchMoreLits (const int ctrNum, long long& tempWslkMCNewRhs) {
  ++stats.tryToWatchMoreLits;
  assert(!useCounter[ctrNum]);
  long long& wslkMC = sumOfWatches[ctrNum];
  assert(tempWslkMCNewRhs < 0); // this is only the temperory counter since the new rhs has not been applied
 
  PBConstraint& c = constraintsPB[ctrNum];
  const int size = c.getSize();
  int i = c.getMaxWIdx();
  int start_i = i;
  for (; tempWslkMCNewRhs < 0 and i < size; ++i) {
    int lit  = c.getIthLiteral(i); 
    int coef = c.getIthCoefficient(i); 
    if (coef > 0 && !model.isFalseLit(lit)) {
      tempWslkMCNewRhs += coef;
      wslkMC += coef;
      c.setIthLitWatched(i, true);
      if (lit > 0) positivePBWatches[lit].emplace_back(ctrNum, coef, i);
      else         negativePBWatches[-lit].emplace_back(ctrNum, coef, i);
    }
  }
  if (tempWslkMCNewRhs < 0 and c.getNumBackjump() < stats.numOfBackjump) {
    c.setNumBackjump(stats.numOfBackjump);
    i = 0;
    for (; tempWslkMCNewRhs < 0 and i < start_i; ++i) {
      int lit  = c.getIthLiteral(i); 
      int coef = c.getIthCoefficient(i); 
      if (coef > 0 && !model.isFalseLit(lit)) {
        tempWslkMCNewRhs += coef;
        wslkMC += coef;
        c.setIthLitWatched(i, true);
        if (lit > 0) positivePBWatches[lit].emplace_back(ctrNum, coef, i);
        else         negativePBWatches[-lit].emplace_back(ctrNum, coef, i);
      }
    }
  }
  c.setMaxWIdx(i);
}

void Solver::watchMoreLitsInPB (const int ctrNum) {
  assert(ctrNum != -1);
  assert(!useCounter[ctrNum]);
  long long& wslkMC = sumOfWatches[ctrNum];
  if (wslkMC >= 0) return;
 
  PBConstraint& c = constraintsPB[ctrNum];
  const int size = c.getSize(); 
  static vector<int> falseIdx; falseIdx.clear();
  for (int i = 0; wslkMC < 0 and i < size; ++i) {
    int lit  = c.getIthLiteral(i); 
    int coef = c.getIthCoefficient(i); 
    if (coef > 0) {
      if (!model.isFalseLit(lit)) {
        wslkMC += coef;
        c.setIthLitWatched(i, true);
        if (lit > 0) positivePBWatches[lit].emplace_back(ctrNum, coef, i);
        else         negativePBWatches[-lit].emplace_back(ctrNum, coef, i);
      }
      else if (model.getDLOfLit(lit) > 0) falseIdx.push_back(i); // select the unwatched false lits
    }
  }
  if (wslkMC >= 0) return;
  if (model.currentDecisionLevel() == 0) return; // else this is obj ctr, we need to watch enough false lits
  assert(ctrNum == obj_num);
  int maxCoef = abs(c.getIthCoefficient(0)); 
  long long wslk = wslkMC + maxCoef;
  assert(wslk < maxCoef); // conflicting or propagating
  // sort by decreasing height of false lits
  sort(falseIdx.begin(), falseIdx.end(), 
       [&](const int i1, const int i2) { return model.getHeightOfVar(abs(c.getIthLiteral(i1))) > model.getHeightOfVar(abs(c.getIthLiteral(i2))); } );

  long long diff = maxCoef - wslk; 
  assert(diff > 0);
  
  for (int& idx : falseIdx) { // watch only first N false lits to make sure the sumNonFalseMinusK > maxCoef
    int lit = c.getIthLiteral(idx); int coef = c.getIthCoefficient(idx);
    assert(coef > 0);
    diff -= coef;
    c.setIthLitWatched(idx, true);
    if (lit > 0) positivePBWatches[lit].emplace_back(ctrNum, coef, idx);
    else         negativePBWatches[-lit].emplace_back(ctrNum, coef, idx);
    if (diff <= 0) break;
  }
}

void Solver::checkObjectiveIsConflictingOrPropagating ( const int ctrId) {
  assert(!conflict);
  const long long& wslkMC = sumOfWatches[ctrId];
  if (wslkMC >= 0) return;
 
  PBConstraint& c = constraintsPB[ctrId];
  long long wslk = wslkMC + abs(c.getIthCoefficient(0)); 
  if(wslk < 0) {
    conflict = true; typeConflict = CONFLICT_PB; constraintConflictNum = ctrId;
    return;
  }
  
  int size = c.getSize();
  int idx = 0; 
  while (idx < size and abs(c.getIthCoefficient(idx)) > wslk) {
    int lit = c.getIthLiteral(idx);
    if (model.isUndefLit(lit)) {
      strat.reportPropagationInPBCounter();
      setTrueDueToReason(lit,Reason(ctrId,Reason::PB_CONSTRAINT));
    }
    ++idx;
  }
  c.setMaxWIdx(idx);
  c.setNumBackjump(stats.numOfBackjump);
}

// Circular search
bool Solver::propagatePBCtrWatch (const int ctrId, long long SNF, int litIdx, int coef) {  // 2 optimizations
  bool unwatch = false;
  ++stats.numLoadPBWatch;
  
  PBConstraint& pc = constraintsPB[ctrId];
  int size = pc.getSize();
  assert(model.isFalseLit(pc.getIthLiteral(litIdx)));
  int idx = pc.getMaxWIdx();
  
  if(SNF + coef >= 0) {  // 2nd optimization: try to watch more lits only when previous wslk >= maxCoef
    int start_idx = idx;
    for (; idx < size and SNF < 0; ++idx) {  // 1st idx optimization
      int new_lit = pc.getIthLiteral(idx);
      int new_coef = pc.getIthCoefficient(idx); //int new_lit = pc.getIthLiteral(idx);
      if (new_coef > 0 && !model.isFalseLit(new_lit)) {  // not watched yet
        SNF += new_coef;
        pc.setIthLitWatched(idx, true);
        if (new_lit > 0) positivePBWatches[new_lit].emplace_back(ctrId, new_coef, idx);
        else             negativePBWatches[-new_lit].emplace_back(ctrId, new_coef, idx);
      } 
    }
    
    if (SNF < 0 and pc.getNumBackjump() < stats.numOfBackjump) {
      pc.setNumBackjump(stats.numOfBackjump);
      idx = 0;
      for (; SNF < 0 and idx < start_idx; ++idx) {
        int new_lit = pc.getIthLiteral(idx);
        int new_coef = pc.getIthCoefficient(idx); //int new_lit = pc.getIthLiteral(idx);
        if (new_coef > 0 && !model.isFalseLit(new_lit)) {  // not watched yet
          SNF += new_coef;
          pc.setIthLitWatched(idx, true);
    
          if (new_lit > 0) positivePBWatches[new_lit].emplace_back(ctrId, new_coef, idx);
          else             negativePBWatches[-new_lit].emplace_back(ctrId, new_coef, idx);
        }
      }
    }
    
    if (SNF < 0) idx = 0;
    sumOfWatches[ctrId] = SNF;
  }
  
  if (SNF >= 0) { // unwatch
    pc.setMaxWIdx(idx); pc.setIthLitWatched(litIdx, false); unwatch = true;
  }
  else {
    int maxCoef = abs(pc.getIthCoefficient(0)); 
    long long wslk = SNF + maxCoef; 
    if (wslk < 0) {     //conflicting
      conflict = true; typeConflict = CONFLICT_PB; constraintConflictNum = ctrId;
    }
    else {             // propagating
      assert(wslk < maxCoef);
      if (pc.getNumBackjump() < stats.numOfBackjump) {
        pc.setNumBackjump(stats.numOfBackjump);
        idx = 0;
      }
      for (; idx < size and wslk < abs(pc.getIthCoefficient(idx)); ++idx) {
        int lit  = pc.getIthLiteral(idx);
        if ( model.isUndefLit(lit)) {  // propagate lit
          strat.reportPropagationInPBWatch();
          setTrueDueToReason(lit,Reason(ctrId,Reason::PB_CONSTRAINT));
        }    
      }
      pc.setMaxWIdx(idx);
    }
  }
  
  return unwatch;
}

void Solver::propagatePBCtrCounter ( const int ctrId, const long long wslk ) {
  PBConstraint& c = constraintsPB[ctrId];
  const int size = c.getSize();
  assert(sumOfWatches[ctrId] < 0); // propagating
  int idx = 0;
  if (c.getNumBackjump() < stats.numOfBackjump)
    c.setNumBackjump(stats.numOfBackjump);
  else idx = c.getMaxWIdx();
  
  while (idx < size and c.getIthCoefficient(idx) > wslk) {
    int lit = c.getIthLiteral(idx);
    if (model.isUndefLit(lit)) {
      strat.reportPropagationInPBCounter();
      setTrueDueToReason(lit,Reason(ctrId,Reason::PB_CONSTRAINT));
    }
    ++idx;
  }
  c.setMaxWIdx(idx);
}


//// no circular search
//bool Solver::propagateCardinalityCtr (const int cardId, int idx) {

  //Cardinality& c = cardinalities[cardId];
  //const int ctrSize = c.getSize();
  //const int degree = c.getDegree();
  //assert(idx <= degree);
  //assert(model.isFalseLit(c.getIthLiteral(idx)));
  //assert(c.getIthLiteral(idx) == -model.getLitAtHeight(model.lastPropagatedCard));
  
  //int watchIdx = degree + 1;
  //if(c.getNumBackjump() != stats.numOfBackjump)
    //c.setNumBackjump(stats.numOfBackjump);
  //else watchIdx = c.getWatchIdx();
  //assert(watchIdx > degree);
  
  ////for(int i = degree+1; i < watchIdx; i++) assert(model.isFalseLit(c.getIthLiteral(i)));  // it holds
  //// we look for a no-false lit from the watchIdx to replace the current falsified lit
  //for(; watchIdx < ctrSize; ++watchIdx) {
    //int lit = c.getIthLiteral(watchIdx);
    //if(not model.isFalseLit(lit)) {  // found a new watch
      //int mid = (watchIdx + degree + 1) / 2;
      //assert(mid <= watchIdx);
      //assert(mid > degree);
      //c.setIthLiteral(watchIdx, c.getIthLiteral(mid)); // the lit at idx=mid become false much earlier than the current false lit
      //c.setIthLiteral(mid, c.getIthLiteral(idx)); // put to front the current latest falsified literal, which is more close to the lit at degree.
      //c.setIthLiteral(idx, lit);                  // put the found no-false lit at idx 
      //if (lit > 0) positiveCardLists[lit].emplace_back(cardId, idx);
      //else         negativeCardLists[-lit].emplace_back(cardId, idx);
      
      //assert(not model.isFalseLit(c.getIthLiteral(idx))); // the new found no-false lit
      //assert(model.isFalseLit(c.getIthLiteral(mid)));     // the current latest falsified lit
      //assert(model.isFalseLit(c.getIthLiteral(watchIdx))); // the old false lit at mid
      //assert(c.getIthLiteral(mid) == -model.getLitAtHeight(model.lastPropagatedCard));
      
      //c.setWatchIdx(watchIdx+1);
      //return true;    // unwatch the original lit at idx
    //}
  //}
  //// We did not find literals to watch --> propagating or conflicting
  //assert(watchIdx == ctrSize);
  //c.setWatchIdx(watchIdx);
  ////for (int i = degree + 1; i < ctrSize; ++i) assert(model.isFalseLit(c.getIthLiteral(i)));  // it holds
  //for (int i = 0; i <= degree; ++i) { // iterate over the watched literals
    //if (i != idx && model.isFalseLit(c.getIthLiteral(i))) { // conflicting
      //conflict = true; typeConflict = CONFLICT_CARD; cardinalityConflictNum = cardId; return false;
    //}
  //}
  //assert(model.isFalseLit(c.getIthLiteral(idx))); // the current propagated falsified lit

  //for (int i = 0; i <= degree; ++i) {
    //int lit = c.getIthLiteral(i);
    //if (model.isUndefLit(lit)) {  // propagating
      //strat.reportPropagationInCard();
      //setTrueDueToReason(lit,Reason(cardId,Reason::PB_CONSTRAINT)); // TODO
    //}
    ////else if(i != idx) assert(model.isTrueLit(lit));
  //}
  //return false;
//}


// Circular search
bool Solver::propagateCardinalityCtr (const int cardId, int idx) {
  Cardinality& c = cardinalities[cardId];
  const int ctrSize = c.getSize();
  const int degree = c.getDegree();
  assert(idx <= degree);
  assert(model.isFalseLit(c.getIthLiteral(idx)));
  
  const int startIdx = c.getWatchIdx();
  int watchIdx = startIdx;
  assert(watchIdx > degree);
  
  int lit = 0;
  bool isFalse = true;
  while (watchIdx < ctrSize && (isFalse = model.isFalseLit(lit = c.getIthLiteral(watchIdx))) )
    watchIdx++;
    
  if (isFalse and c.getNumBackjump() != stats.numOfBackjump) {
    assert(lit == 0 or model.isFalseLit(lit));
    c.setNumBackjump(stats.numOfBackjump);
    watchIdx = degree + 1;
    while (watchIdx < startIdx && (isFalse = model.isFalseLit(lit = c.getIthLiteral(watchIdx))) )
      watchIdx++;
  }
  c.setWatchIdx(watchIdx);
  
  if (not isFalse) {
    c.setIthLiteral(watchIdx, c.getIthLiteral(idx)); // put to front the current latest falsified literal, which is more close to the lit at degree.
    c.setIthLiteral(idx, lit); // the lit at idx=mid become false much earlier than the current false lit
    if (lit > 0) positiveCardLists[lit].emplace_back(cardId, idx);
    else         negativeCardLists[-lit].emplace_back(cardId, idx);
    assert(not model.isFalseLit(c.getIthLiteral(idx))); // the new found no-false lit
    assert(model.isFalseLit(c.getIthLiteral(watchIdx))); // the old false lit at mid
    return true;
  }
  
  //for (int i = degree + 1; i < ctrSize; ++i) assert(model.isFalseLit(c.getIthLiteral(i)));  // it holds
  for (int i = 0; i <= degree; ++i) { // iterate over the watched literals
    if (i != idx && model.isFalseLit(c.getIthLiteral(i))) { // conflicting
      conflict = true; typeConflict = CONFLICT_CARD; cardinalityConflictNum = cardId; return false;
    }
  }
  assert(model.isFalseLit(c.getIthLiteral(idx))); // the current propagated falsified lit

  for (int i = 0; i <= degree; ++i) {
    int lit = c.getIthLiteral(i);
    if (i != idx and !model.isTrueLit(lit)) {  // propagating
      strat.reportPropagationInCard();
      setTrueDueToReason(lit,Reason(cardId,Reason::CARDINALITY));
    }
  }
  return false;
}

/*
void Solver::checkBestSoluSatisfy (PBConstraint & c, int ctrNum) {
  if (not readInfo or stats.costOfBestSolution == bestCost) return; 
  long long sumMinusRHS = -c.getConstant();
  long long SNF = sumMinusRHS;
  for (int i = 0; i < c.getSize(); ++i) {
    int lit = c.getIthLiteral(i);
    int coef = c.getIthCoefficient(i);
    sumMinusRHS += coef*(lit > 0? opt_solu[abs(lit)] : 1-opt_solu[abs(lit)]);
    if (not model.isFalseLit(lit)) SNF += coef;
  }
  
  int current_sym_rhs = latest_rhs(c.getIndependentRHS(), c.getObjectiveRHS(), next_obj_rhs);
  int best_sym_rhs    = latest_rhs(c.getIndependentRHS(), c.getObjectiveRHS(), bestCost);
  
  if (sumMinusRHS < 0) {
    cout << "PB " << ctrNum << " is not satisfied by best solution." << " nDecs: " << stats.numOfDecisions << " nConfs: " << stats.numOfConflicts << endl;
    cout << "sumMinusRHS = " << sumMinusRHS << ", c.constant = " << c.getConstant() << endl;
    cout << "SNF = " << SNF << endl;
    
    pair<int,int> ind_rhs = c.getIndependentRHS();
    pair<int,int> obj_rhs = c.getObjectiveRHS();
    cout << "best_sym_rhs    = " << best_sym_rhs << " =  " << ind_rhs.first  << "/" << ind_rhs.second << " + " << bestCost << "*"<< obj_rhs.first << "/" << obj_rhs.second << endl;
    cout << "current_sym_rhs = " << current_sym_rhs << " =  " << ind_rhs.first  << "/" << ind_rhs.second << " + " << next_obj_rhs << "*"<< obj_rhs.first << "/" << obj_rhs.second << endl;
    
    exit(0);
  }
}

void Solver::checkBestSoluSatisfy (WConstraint& c, int ctrNum) {
  if (not readInfo or stats.costOfBestSolution == bestCost) return; //  the later lemmas may be not satisfied
  long long sumMinusRHS = -c.getConstant();
  long long SNF = sumMinusRHS;
  for (int i = 0; i < c.getSize(); ++i) {
    int lit = c.getIthLiteral(i);
    int coef = c.getIthCoefficient(i);
    sumMinusRHS += coef*(lit > 0? opt_solu[abs(lit)] : 1-opt_solu[abs(lit)]);
    if (not model.isFalseLit(lit)) SNF += coef;
  }
  
  int current_sym_rhs = latest_rhs(c.getIndependentRHS(), c.getObjectiveRHS(), next_obj_rhs);
  int best_sym_rhs    = latest_rhs(c.getIndependentRHS(), c.getObjectiveRHS(), bestCost);
  
  if (sumMinusRHS < 0) {
    cout << "WConstraint " << ctrNum << " is not satisfied by best solution." << " nDecs: " << stats.numOfDecisions << " nConfs: " << stats.numOfConflicts << endl;
    cout << "sumMinusRHS = " << sumMinusRHS << ", c.constant = " << c.getConstant() << endl;
    cout << "SNF = " << SNF << endl;
    
    pair<int,int> ind_rhs = c.getIndependentRHS();
    pair<int,int> obj_rhs = c.getObjectiveRHS();
    cout << "best_sym_rhs    = " << best_sym_rhs << " =  " << ind_rhs.first  << "/" << ind_rhs.second << " + " << bestCost << "*"<< obj_rhs.first << "/" << obj_rhs.second << endl;
    cout << "current_sym_rhs = " << current_sym_rhs << " =  " << ind_rhs.first  << "/" << ind_rhs.second << " + " << next_obj_rhs << "*"<< obj_rhs.first << "/" << obj_rhs.second << endl;
    
    writeConstraint(c);
    exit(0);
  }
}
void Solver::checkBestSoluSatisfy (Cardinality& c, int ctrNum) {
  if (not readInfo or stats.costOfBestSolution == bestCost) return;
  long long sumMinusRHS = -c.getDegree();
  for (int i = 0; i < c.getSize(); ++i) {
    int lit = c.getIthLiteral(i);
    int coef = 1;
    sumMinusRHS += coef*(lit > 0? opt_solu[abs(lit)] : 1-opt_solu[abs(lit)]);
  }
  
  int current_sym_rhs = latest_rhs(c.getIndependentRHS(), c.getObjectiveRHS(), next_obj_rhs);
  int best_sym_rhs    = latest_rhs(c.getIndependentRHS(), c.getObjectiveRHS(), bestCost);
  
  if (sumMinusRHS < 0) {
    cout << "CARD " << ctrNum << " is not satisfied by best solution." << " nDecs: " << stats.numOfDecisions << " nConfs: " << stats.numOfConflicts << endl;
    cout << "sumMinusRHS = " << sumMinusRHS << ", c.Degree = " << c.getDegree() << endl;
    
    pair<int,int> ind_rhs = c.getIndependentRHS();
    pair<int,int> obj_rhs = c.getObjectiveRHS();
    cout << "best_sym_rhs    = " << best_sym_rhs << " =  " << ind_rhs.first  << "/" << ind_rhs.second << " + " << bestCost << "*"<< obj_rhs.first << "/" << obj_rhs.second << endl;
    cout << "current_sym_rhs = " << current_sym_rhs << " =  " << ind_rhs.first  << "/" << ind_rhs.second << " + " << next_obj_rhs << "*"<< obj_rhs.first << "/" << obj_rhs.second << endl;
    
    exit(0);
  }
  
}
*/
void Solver::removeUnits (WConstraint& c) {
  vector<pair<int,int> > newCtr;
  int constant = c.getConstant(); 
  int size     = c.getSize();
  
  for(int i = 0; i < size; i++) {
    int lit = c.getIthLiteral(i); int coef = c.getIthCoefficient(i);
    if (!model.isUndefLit(lit) and model.getDLOfLit(lit) == 0){
      if (model.isTrueLit(lit)) {
        constant -= coef;
      }
    }
    else newCtr.push_back({coef, lit});
  }
  int constantToSubstractFromIndRHS = c.getConstant() - constant;
  c.setLHS(newCtr);
  c.setConstant(constant);
  
  if (constantToSubstractFromIndRHS) c.setIndependentRHS(add_rational(c.getIndependentRHS(),-constantToSubstractFromIndRHS));
}

int Solver::minWatches (const WConstraint & c) {
  int min = 0;
  long long int wslk = -c.getConstant() - c.getIthCoefficient(0);
  const int size = c.getSize();
  for (int i = 0; i < size and wslk < 0; ++i) {
    int lit  = c.getIthLiteral(i);
    int coef = c.getIthCoefficient(i);
    if (model.isUndefLit(lit) or model.getDLOfLit(lit) > 0) { wslk += coef; ++ min; } // T/U/F
    else if (model.isTrueLit(lit)) wslk += coef;
  }
  return min;
}

void Solver::minNumWatchesCleanup (const WConstraint & c, long long& wslk, int& numWatches) {
  wslk = -c.getConstant() - c.getIthCoefficient(0);
  int size = c.getSize();
  for (numWatches = 0; wslk < 0 and numWatches < size; ++numWatches) {
    int lit  = c.getIthLiteral(numWatches);
    int coef = c.getIthCoefficient(numWatches);
    if(not model.isFalseLit(lit)) wslk += coef;
  }
}

////---------------------------------
void Solver::addAndPropagatePBConstraint (WConstraint & c, const bool isInitial, int activity, const int LBD, bool isObj) {
  if (!isObj) c.simplify();
  shavedPBs.push_back(c.isShaved());
  stats.numPBG0NotShaved += (!c.isShaved() and c.getObjectiveRHSNum() > 0);
  
  PBConstraint pc(c,isInitial,activity,LBD);  // maxCoef is the first one
  int min = minWatches(c);
  
  if(min < c.getSize()*getWatchPercent()) { // WATCH
    if (model.currentDecisionLevel() == 0) 
      addPBConstraintWatchedDL0(pc);
    else 
      addPBConstraintWatchedDLGreaterThan0(pc);
    propagateInitialConstraintWatch(constraintsPB.size()-1);
  }
  else { // COUNTER
    addPBConstraintCounter(pc);
    propagateInitialConstraintCounter(constraintsPB.size()-1);
  }
  stats.numOfIntsInPbsAndClauses += pc.getNumInts();
}

void Solver::addAndPropagateCardinality (WConstraint & c, const bool isInitial, int activity, const int LBD) {
  assert(c.isCardinality());
  const int degree = c.getConstant();
  const int size = c.getSize();
  if (degree >= size) {  // example benchmarks: 1379.lp 1296.lp 1337.lp
    assert(degree == size); // otherwise, it's already conflicting at dl 0, this method is not called
    assert(model.currentDecisionLevel() == 0);
    for (int i = 0; i < size; i++) {
      int lit = c.getIthLiteral(i);
      assert(model.isUndefLit(lit));
      if (model.isUndefLit(lit)) {  // no need to check if units have been removed in lemma
        strat.reportPropagationInCard();
        setTrueDueToReason(lit,Reason(cardinalities.size(), Reason::CARDINALITY));
      }
    }
    return;
  }

  assert(degree < size); // Otherwise it is equivalent to a set of units
  //move No-false lits to front
  int watch = 0;
  int i;
  for(i = 0; i < size; i++) {
    int lit = c.getIthLiteral(i); 
    if(not model.isFalseLit(lit)) {
      c.setIthLiteral(i, c.getIthLiteral(watch));
      c.setIthLiteral(watch, lit);
      ++watch;
      if(watch >= degree + 1) break; // we found enough watches to satisfy the constraint. use > (because we increased watch again)
    }
  }
  
  // [0....watch-1] --> non-false lits
  // [watch.......] --> false lits
  for(int j = watch; j < i; j++) assert(model.isFalseLit(c.getIthLiteral(j)));  // it holds
  if(i < c.getSize()) assert(model.isFalseLit(c.getIthLiteral(i)));  // because of the break

  if(watch == degree) { // propagating
    assert(i == size and degree < size);
    assert(model.isFalseLit(c.getIthLiteral(degree)));
    for(int i = 0; i < watch; i++) {
      int lit = c.getIthLiteral(i);
      assert(not model.isFalseLit(lit));
      if (model.isUndefLit(lit)) {
        strat.reportPropagationInCard();
        setTrueDueToReason(lit,Reason(cardinalities.size(), Reason::CARDINALITY));
      }
    }
  }
  // Move the literal in  [watch.....] with highest DL to position "watch"
  for(int k = watch; k <= degree; k++) {
    int idxAtDegree = k;
    int dlOfLitDegree = model.getDLOfLit(c.getIthLiteral(idxAtDegree));
    for(int i = degree+1; i < size; i++) {
      int lit = c.getIthLiteral(i);
      assert(model.isFalseLit(lit));
      if (model.getDLOfLit(lit) > dlOfLitDegree) {  // ensure last watch is last falsified literal
        idxAtDegree = i;
        dlOfLitDegree = model.getDLOfLit(lit);
      }
    }
    int highestLit = c.getIthLiteral(idxAtDegree);
    int other = c.getIthLiteral(k);
    c.setIthLiteral(k,highestLit);
    c.setIthLiteral(idxAtDegree,other);
  }
  if(watch < degree) { // conflicting 1411.lp, 696.lp
    //cout << "lemma is still conflicting" << endl;
    assert(model.isFalseLit(c.getIthLiteral(degree-1)));
    //for(int i = watch; i < size; i++) assert(model.isFalseLit(card.getIthLiteral(i))); // it holds
    conflict = true; typeConflict = CONFLICT_CARD; cardinalityConflictNum = cardinalities.size();
  }

  if(watch >= degree + 1) { // nothing to do
    //cout << "lemma has nothing to do, nCards " << cardinalities.size() << ", watch " << watch << ", degree+1 " << degree+1 << ", size " << size << endl;
    assert(degree < size);
    assert(false); exit(0);
  }
    
  for(int idx = 0; idx <= degree; idx++) { 
    int lit = c.getIthLiteral(idx);
    if (lit > 0) positiveCardLists[lit].emplace_back(cardinalities.size(), idx);
    else         negativeCardLists[-lit].emplace_back(cardinalities.size(), idx);
  }
  
  Cardinality card(c,isInitial,activity,LBD);
  card.setWatchIdx(i);
  card.setNumBackjump(stats.numOfBackjump);
  cardinalities.push_back(card);
  shavedCards.push_back(c.isShaved());
  stats.numOfIntsInPbsAndClauses += ( card.getNumInts());
}

bool Solver::existsBinaryClause(int lit1, int lit2) {
  uint size1 = lit1 > 0 ? positiveBinClauses[lit1].size(): negativeBinClauses[-lit1].size();
  uint size2 = lit2 > 0 ? positiveBinClauses[lit2].size(): negativeBinClauses[-lit2].size();

  if (size1 < size2) {
    vector<int>& bins = lit1 > 0 ? positiveBinClauses[lit1] : negativeBinClauses[-lit1];
    for (auto& x:bins) if (x == lit2) return true;
  }
  else {
    vector<int>& bins = lit2 > 0 ? positiveBinClauses[lit2] : negativeBinClauses[-lit2];
    for (auto& x:bins) if (x == lit1) return true;
  }
  return false;
}

void Solver::addBinaryClause (int lit1, int lit2) {
  //if (existsBinaryClause(lit1,lit2)) return;
  if (lit1 > 0) positiveBinClauses[lit1].push_back(lit2);
  else          negativeBinClauses[-lit1].push_back(lit2);

  if (lit2 > 0) positiveBinClauses[lit2].push_back(lit1);
  else          negativeBinClauses[-lit2].push_back(lit1);
}

void Solver::addClause ( const Clause & c) {
  clauses.push_back(c);
  int firstLit = c.getIthLiteral(0);
  int secondLit = c.getIthLiteral(1);
  int lastLit = c.getIthLiteral(c.getSize()-1);
  if (firstLit > 0) positiveWatchLists[firstLit].emplace_back(clauses.size()-1,lastLit);
  else              negativeWatchLists[-firstLit].emplace_back(clauses.size()-1,lastLit);
  
  if (secondLit > 0) positiveWatchLists[secondLit].emplace_back(clauses.size()-1,lastLit);
  else               negativeWatchLists[-secondLit].emplace_back(clauses.size()-1,lastLit);
  stats.numOfIntsInPbsAndClauses += ( c.getNumInts());  
}

void Solver::cleanupPBConstraints (vector<ConstraintCleanup>& pbs, vector<ConstraintCleanup>& cards, vector<ConstraintCleanup>& cls, vector<pair<int,int> >& binClauses, vector<bool>& ctrIsRemoved, uint newestObjectiveFunction) {
  stats.PBObjNumG0NotShaved = 0;
  stats.numPBG0NotShaved = 0;
  uint idx_shavedPB = 0;
  assert(shavedPBs.size() == constraintsPB.size());
  
  for ( uint k = 0; k < constraintsPB.size(); ++k) {
    PBConstraint& c = constraintsPB[k];
    
    assert(c.getObjectiveRHSNum() > 0 or (c.getObjectiveRHSNum() == 0 and !shavedPBs[k]));
    if ((!multiObj or update_rhs) and k == newestObjectiveFunction) { // we don't remove obj ctr and its units, to be reused when a new solution is found
      assert(!shavedPBs[k]);
      shavedPBs[idx_shavedPB++] = false;
      ++stats.numPBG0NotShaved;
      obj_num = pbs.size();
      objectiveFunctions.push_back(pbs.size());
      pbs.emplace_back(WConstraint(c), c.isInitial(),strat.reduceActivityOfPBInCleanup(c.getActivity()),c.getLBD());
      c.freeMemory();
      continue;
    }
    
    if (not ctrIsRemoved[k]) { // We keep this constraint
      WConstraint wc;
      // Now remove lits that are defined at dl0, adapting the constant:
      int constant = c.getConstant();
      int constantToSubstractFromIndRHS = 0;
      for (int i = 0; i < c.getSize(); ++i) {
        int lit  = c.getIthLiteral(i);
        int coef = abs(c.getIthCoefficient(i));
        if (model.isUndefLit(lit)) wc.addMonomial(coef,lit);
        else if ( model.isTrueLit(lit) ) { constant -= coef; constantToSubstractFromIndRHS += coef;}
      }
      
      assert(constant > 0);
      wc.setConstant(constant);
      wc.setShaved(shavedPBs[k]);
      wc.setIndependentRHS(add_rational(c.getIndependentRHS(), -constantToSubstractFromIndRHS));
      wc.setObjectiveRHS(c.getObjectiveRHS());
      
      assert(wc.getConstant() > 0);
      assert( not constraintIsFalse(wc) );   // otherwise: undetected conflict before calling doCleanup
      assert( wc.getSize() > 1 );            // otherwise c would have been a bound already propagated at dl 0

      wc.simplify();
      
      if (wc.getConstant() == 1) {
        assert(wc.isClause()); // NOTE: this means we have 1 as RHS. Clauses currently do not have symbolic RHS
                     // However, they could have it, and if it becomes larger than 1, then the clause
                     // would become a cardinality constraint [we should whether this happens and how often]
        if (wc.getSize() > 2) {
          cls.emplace_back(wc,c.isInitial(),strat.reduceActivityOfClauseInCleanup(c.getActivity()),c.getLBD());
        }
        else {
          assert(wc.getSize() == 2);
          int lit1 = wc.getIthLiteral(0);
          int lit2 = wc.getIthLiteral(1);
          if (abs(lit1) > abs(lit2)) swap(lit1,lit2);
          binClauses.emplace_back(lit1,lit2);
        }
      }
      else if(wc.getIthCoefficient(0) == 1 and k != newestObjectiveFunction and useCardinality) {
        // since our constraints are always sorted by decreasing coefficient, it is cardinally iff first coeff is 1
        assert(wc.getConstant() < wc.getSize()); // otherwise it's conflicting or propagating
        assert(wc.getConstant() > 1);
        cards.emplace_back(wc, c.isInitial(),strat.reduceActivityOfCardInCleanup(c.getActivity()),c.getLBD());
      }
      else {
        if (k == newestObjectiveFunction) {obj_num = pbs.size(); objectiveFunctions.push_back(pbs.size());}
        pbs.emplace_back(wc,c.isInitial(),strat.reduceActivityOfPBInCleanup(c.getActivity()),c.getLBD());
        shavedPBs[idx_shavedPB++] = wc.isShaved();
        if(wc.getObjectiveRHSNum() > 0 and !wc.isShaved()) {++stats.numPBG0NotShaved; ++stats.PBObjNumG0NotShaved;}
      }
    }    
    c.freeMemory();
  }
  
  shavedPBs.resize(idx_shavedPB);
  assert(shavedPBs.size() == pbs.size());
}

void Solver::cleanupCardinalities (vector<ConstraintCleanup>& cards, vector<ConstraintCleanup>& cls, vector<pair<int,int> >& binClauses, vector<bool>& ctrIsRemoved) {
  if (!useCardinality) return;
  uint numCtr = constraintsPB.size() - 1;
  for ( uint k = 0; k < cardinalities.size(); ++k) {
    ++numCtr;
    Cardinality& c = cardinalities[k];
    if (not ctrIsRemoved[numCtr]) {
      WConstraint wc;
      // Now remove lits that are defined at dl0, adapting the constant:
      int constant = c.getDegree();
      int constantToSubstractFromIndRHS = 0;
      for (int i = 0; i < c.getSize(); ++i) {
        int lit  = c.getIthLiteral(i);
        if (model.isUndefLit(lit)) wc.addMonomial(1,lit);
        else if ( model.isTrueLit(lit) ) {constant -= 1; ++constantToSubstractFromIndRHS;}
      }

      assert(constant > 0);
      wc.setConstant(constant);
      wc.setShaved(shavedCards[k]);
      wc.setIndependentRHS(add_rational(c.getIndependentRHS(), -constantToSubstractFromIndRHS));
      wc.setObjectiveRHS(c.getObjectiveRHS());
      
      assert( not constraintIsFalse(wc) );   // otherwise: undetected conflict before calling doCleanup
      assert( wc.getSize() > 1 );            // otherwise c would have been a bound already propagated at dl 0
      
      if (wc.getConstant() == 1) {
        assert(wc.isClause());
        if (wc.getSize() > 2) {
          cls.emplace_back(wc,c.isInitial(),strat.reduceActivityOfClauseInCleanup(c.getActivity()),c.getLBD());
        }
        else {
          assert(wc.getSize() == 2);
          int lit1 = wc.getIthLiteral(0);
          int lit2 = wc.getIthLiteral(1);
          if (abs(lit1) > abs(lit2)) swap(lit1,lit2);
          binClauses.emplace_back(lit1,lit2);
        }
      }
      else {
        assert(wc.isCardinality());
        assert(wc.getConstant() < wc.getSize());
        assert(wc.getConstant() > 1);
        cards.emplace_back(wc,c.isInitial(),strat.reduceActivityOfCardInCleanup(c.getActivity()),c.getLBD());
      }
    } 
    c.freeMemory(); 
  }
}

void Solver::cleanupClauses (vector<ConstraintCleanup>& cls, vector<pair<int,int> >& binClauses, vector<bool>& ctrIsRemoved) {
  uint numCtr = constraintsPB.size() + cardinalities.size() - 1;
  
  for ( Clause& c : clauses ) {
    ++numCtr;
    
    if (not ctrIsRemoved[numCtr]) {
      WConstraint wc;
      // Now remove lits that are defined at dl0, adapting the constant:
      for (auto& lit:c) {
        if (model.isUndefLit(lit)) wc.addMonomial(1,lit);
        assert(not model.isTrueLit(lit));
      }
      wc.setConstant(1);
      assert( not constraintIsFalse(wc) );   // otherwise: undetected conflict before calling doCleanup
      assert( wc.getSize() > 1 );            // otherwise c would have been propagated at dl 0
      
      if (wc.getSize() == 2) {
        assert(wc.getSize() == 2);
        int lit1 = wc.getIthLiteral(0);
        int lit2 = wc.getIthLiteral(1);
        if (abs(lit1) > abs(lit2)) swap(lit1,lit2);
        binClauses.emplace_back(lit1,lit2);
      }
      else {
        cls.emplace_back(wc,c.isInitial(),strat.reduceActivityOfClauseInCleanup(c.getActivity()),c.getLBD());
      }
    }
    c.freeMemory();
  }
}

void Solver::cleanupBinaryClauses ( vector<pair<int,int> >& binClauses ){
  for (int v = 1; v <= stats.numOfVars; ++v) 
    if (model.isUndefLit(int(v))) 
      for (auto& lit2:positiveBinClauses[v]) 
        if (model.isUndefLit(lit2) and v < abs(lit2)) binClauses.emplace_back(v,lit2);

  for (int v = 1; v < stats.numOfVars; ++v) 
    if (model.isUndefLit(int(v))) 
      for (auto& lit2:negativeBinClauses[v]) 
        if (model.isUndefLit(lit2) and v < abs(lit2)) binClauses.emplace_back(-v,lit2);  
}


void Solver::doCleanup () {
  struct Triple{
    int LBD;
    int act;
    uint id;    
    Triple(){}
    Triple(int lbd, int a, uint i):LBD(lbd),act(a),id(i){}
  };
  static vector<Triple> LBDAct;
  LBDAct.clear();
  vector<bool> ctrIsRemoved(constraintsPB.size() + cardinalities.size() + clauses.size(), false);
  
  // Mark old objective functions to be deleted
  int newestObjectiveFunction = -1;
  if (objectiveFunctions.size() > 0) newestObjectiveFunction = objectiveFunctions.back();
  for (int i = 0; i < int(objectiveFunctions.size())-1; ++i) {
    assert(objectiveFunctions[i] >= 0);
    assert(objectiveFunctions[i] < ctrIsRemoved.size());
    ctrIsRemoved[objectiveFunctions[i]] = true;
  }
  objectiveFunctions.clear();
  assert(newestObjectiveFunction == -1 or newestObjectiveFunction == obj_num);
  
  size_t totalLearnts = 0;
  size_t promisingLearnts = 0;
  uint numPBLems = 0;
  
  for (uint i = 0; i < constraintsPB.size(); ++i) {
    if((!multiObj or update_rhs) and (int)i == obj_num) continue; // can not remove the obj ctr
    if (not ctrIsRemoved[i]) { // no need to check old objective constraint
      PBConstraint& c = constraintsPB[i];
      long long counter = -c.getConstant();
      int size = c.getSize();
      for (int j = 0; counter < 0 and j < size; ++j)
        if (model.isTrueLit(c.getIthLiteral(j))) counter += abs(c.getIthCoefficient(j));
      if (counter >= 0) {ctrIsRemoved[i] = true; continue;}
      if (not c.isInitial()) {
        ++numPBLems;
        int LBD  = c.getLBD();
        if (size > 2 && LBD > 2) LBDAct.push_back({LBD, c.getActivity(), i});
        if (size <= 2 || LBD <= 3) ++promisingLearnts;
        ++totalLearnts;
      }
    }
  }
  
  uint numCtr = constraintsPB.size()-1;
  for (uint i = 0; i < cardinalities.size(); ++i) {
    ++numCtr;
    Cardinality& c = cardinalities[i];
    long long counter = -c.getDegree();
    int size = c.getSize();
    for (int j = 0; counter < 0 and j < size; ++j)
      if (model.isTrueLit(c.getIthLiteral(j))) counter += 1;
    if (counter >= 0) {ctrIsRemoved[numCtr] = true; continue;}
    if (not c.isInitial()) {
      int LBD  = c.getLBD();
      if (size > 2 && LBD > 2) LBDAct.push_back({LBD, c.getActivity(), numCtr});
      if (size <= 2 || LBD <= 3) ++promisingLearnts;
      ++totalLearnts;
    }
  }
  
  for (uint i = 0; i < clauses.size(); ++i) {
    ++numCtr;
    Clause& c = clauses[i];
    bool isClauseTrue = false;
    for (auto& lit:c)
      if ( model.isTrueLit(lit) ) {isClauseTrue = true;break;}
    if (isClauseTrue) {ctrIsRemoved[numCtr] = true; continue;}
    if (not c.isInitial()) {
      int size = c.getSize();
      int LBD  = c.getLBD();
      if (size > 2 && LBD > 2) LBDAct.push_back({LBD, c.getActivity(), numCtr});
      if (size <= 2 || LBD <= 3) ++promisingLearnts;
      ++totalLearnts;
    }
  }
  assert(numCtr < ctrIsRemoved.size());
  
  if (promisingLearnts > totalLearnts / 2)
    nconfl_to_reduce += 10 * 100;
  else
    nconfl_to_reduce += 100;
  
  shuffle(LBDAct.begin(), LBDAct.end(), default_random_engine(stats.numOfCleanUps));
  //shuffle(LBDAct.begin(), LBDAct.end(), default_random_engine(rand()%(stats.numOfCleanUps+1)));
  //shuffle(LBDAct.begin(), LBDAct.end(), default_random_engine(rand()));
  
  std::sort(LBDAct.begin(), LBDAct.end(), [](Triple& x, Triple& y) {
    return x.LBD > y.LBD || (x.LBD == y.LBD && x.act < y.act);
  });
  
  size_t numDelete = min(totalLearnts/2, LBDAct.size());  // delete worest 75% of lemmas overall
  uint numRemovedPBLemmas = 0;
  for (size_t i = 0; i < numDelete; ++i) {
    ctrIsRemoved[LBDAct[i].id] = true; 
    if (LBDAct[i].id < constraintsPB.size()) ++numRemovedPBLemmas;
  }

  //if (numPBLems > 0 and constraintsPB.size() > 0) cout << endl << "nPBs " << constraintsPB.size() << ", %Deleted " << (double)numDelete/totalLearnts*100 << "% ,totalLearnts/2 " << totalLearnts/2 << ", LBDAct size " << LBDAct.size() << ", numPBLems " << numPBLems << ", %Removed PBLems: " << (double)numRemovedPBLemmas/numPBLems*100 << "%" << endl;

  vector<ConstraintCleanup> tempConstraints;
  vector<ConstraintCleanup> tempCardinalities;
  vector<ConstraintCleanup> tempClauses;
  vector<pair<int,int> >    tempBinaryClauses; // abs(first) < abs(second)
  
  cleanupPBConstraints(tempConstraints,tempCardinalities,tempClauses,tempBinaryClauses,ctrIsRemoved, newestObjectiveFunction);
  cleanupCardinalities(tempCardinalities,tempClauses,tempBinaryClauses, ctrIsRemoved);
  cleanupClauses(tempClauses,tempBinaryClauses, ctrIsRemoved);
  cleanupBinaryClauses(tempBinaryClauses);
  stats.numOfIntsInPbsAndClauses = 0;
  
  if(stats.numOfSolutionsFound > 0 and tempConstraints.size() > 0) {
    ++stats.numPerc;
    double currentG0NotShaved = (double)stats.PBObjNumG0NotShaved/tempConstraints.size()*100;
    stats.sumPercPBObjNumG0NotShaved += currentG0NotShaved;
    //cout << "clean-" << stats.numOfCleanUps << ": stats.sumPercPBObjNumG0NotShaved " << stats.sumPercPBObjNumG0NotShaved << ", avg " << stats.sumPercPBObjNumG0NotShaved/stats.numPerc << "%" << ", current " << currentG0NotShaved <<"% ,left PBs " << tempConstraints.size() << " (" << (double)tempConstraints.size()/constraintsPB.size()*100 << "%)" << ", percGood " << (double)stats.numPBG0NotShaved/tempConstraints.size()*100 << "%" << endl << flush;
  }

  
  for ( int i = 0; i < numVars+1; i++ ) positiveOccurLists[i].clear();
  for ( int i = 0; i < numVars+1; i++ ) negativeOccurLists[i].clear();
  
  for ( int i = 0; i <= numVars; i++ ) positiveCardLists[i].clear();
  for ( int i = 0; i <= numVars; i++ ) negativeCardLists[i].clear();
  
  for ( int i = 0; i <= numVars; i++ ) positiveWatchLists[i].clear();
  for ( int i = 0; i <= numVars; i++ ) negativeWatchLists[i].clear();
  
  for ( int i = 0; i <= numVars; i++ ) positiveBinClauses[i].clear();
  for ( int i = 0; i <= numVars; i++ ) negativeBinClauses[i].clear();
  
  for ( int i = 0; i <= numVars; i++ ) positivePBWatches[i].clear();
  for ( int i = 0; i <= numVars; i++ ) negativePBWatches[i].clear();
  
  constraintsPB.clear();
  cardinalities.clear();
  clauses.clear();
  sumOfWatches.clear();
  useCounter.clear();
  shavedCards.clear();
  stats.numOfBackjump = 0;
  
  int newPBs, newCls, numBins, newCards;
  newPBs = newCls = numBins = newCards = 0;
  
  buildBinaryClauses(tempBinaryClauses);

  for (uint i = 0; i < tempClauses.size(); ++i) {
    clauses.push_back(Clause(tempClauses[i].wc,tempClauses[i].isInit,tempClauses[i].activity,tempClauses[i].LBD));
    stats.numOfIntsInPbsAndClauses += clauses.back().getNumInts();
    if (not tempClauses[i].isInit) ++newCls;
  }
  buildWatchLists();
  
  for (uint i = 0; i < tempCardinalities.size(); ++i) {
    shavedCards.push_back(tempCardinalities[i].wc.isShaved());
    cardinalities.push_back(Cardinality(tempCardinalities[i].wc, tempCardinalities[i].isInit,tempCardinalities[i].activity,tempCardinalities[i].LBD));
    stats.numOfIntsInPbsAndClauses += (cardinalities.back().getNumInts());
    if (not tempCardinalities[i].isInit) {++newCards;}
  }
  buildCardLists();
  
  for (uint i = 0; i < tempConstraints.size(); ++i) {
    PBConstraint pc(tempConstraints[i].wc,tempConstraints[i].isInit,tempConstraints[i].activity, tempConstraints[i].LBD);
    
    long long wslk; int numWatches; bool useC; 
    int maxCoef = pc.getIthCoefficient(0);
    minNumWatchesCleanup(tempConstraints[i].wc, wslk, numWatches);

    if (numWatches <= pc.getSize()*getWatchPercent()) { // WATCH
      useC = false;
      pc.setMaxWIdx(numWatches);
      ++stats.numOfWatchedCtrs;
    }
    else { // COUNTER
      useC = true;
      wslk = maxSumOfConstraintMinusRhs(tempConstraints[i].wc) - maxCoef;
      ++stats.numOfCounterCtr;
    }
    
    useCounter.push_back(useC);
    sumOfWatches.push_back(wslk);
    constraintsPB.push_back(pc);
    
    stats.numOfIntsInPbsAndClauses += pc.getNumInts();
    if (not tempConstraints[i].isInit) {++newPBs;}
  }
  assert(shavedPBs.size() == constraintsPB.size());
  
  buildOccurListsAndPBWatches();
  
  //int total = constraintsPB.size();
  //int nInit = total-newPBs;
  //cout << endl << "doCleanup-" << stats.numOfCleanUps << ": nDecs " << stats.numOfDecisions << ", nConfs " << stats.numOfConflicts << ", total PBs: " << total << ", and #initial: " << nInit << ", newPBs " << newPBs << ", newCards " << newCards << ", newCls " << newCls << ", newBins " << tempBinaryClauses.size() << ", nLPB " << stats.numOfTotalLearnedPBConstraints  << ", nLCards " <<  stats.numOfTotalLearnedCardinalities << ", nLCls " << stats.numOfTotalLearnedClauses << ", nLBins " << stats.numOfTotalLearnedBinClauses << ", nPBs " << constraintsPB.size() << ", nCards " << cardinalities.size() << ", obj_num " << obj_num << endl;
  
  strat.reportNewPBClausesDatabase(constraintsPB.size() - newPBs, cardinalities.size() - newCards, clauses.size() - newCls, tempBinaryClauses.size(),
                                   newPBs, newCards, newCls);
}


void Solver::buildOccurListsAndPBWatches ( ) {
  for (uint i = 0; i < constraintsPB.size(); ++i) {
    PBConstraint& pc = constraintsPB[i];
    if (useCounter[i]) { // PB Counter
      for (int j = 0; j < pc.getSize(); ++j) {
        int lit = pc.getIthLiteral(j);
        int var = abs(lit);
        int coeff = pc.getIthCoefficient(j);
        if (lit > 0) positiveOccurLists[var].addElem(i,coeff);
        else         negativeOccurLists[var].addElem(i,coeff);
      }
    }
    else { // PB Watch
      const int maxWIdx = pc.getMaxWIdx();
      for (int j = 0; j < maxWIdx; ++j) {
        int lit = pc.getIthLiteral(j);
        int coeff = pc.getIthCoefficient(j);
        int var = abs(lit);
        pc.setIthLitWatched(j, true);
        if (lit > 0) positivePBWatches[var].emplace_back(i, coeff, j);
        else         negativePBWatches[var].emplace_back(i, coeff, j);
      }
      pc.setMaxWIdx(0);
    }
  }
}


void Solver::buildCardLists ( ) {
  if (!useCardinality) return;
  for (uint i = 0; i < cardinalities.size(); ++i) {
    Cardinality& card = cardinalities[i];
    for(int j = 0; j <= card.getDegree(); j++) {
      int lit = card.getIthLiteral(j);
      if (lit > 0) positiveCardLists[lit].emplace_back(i, j); // <cardId, idx>
      else         negativeCardLists[-lit].emplace_back(i, j);
    }
  }
}

void Solver::buildWatchLists ( ) {
  for (uint i = 0; i < clauses.size(); ++i) {
    Clause& cl = clauses[i];
    int firstWatched = cl.getIthLiteral(0);
    int secondWatched = cl.getIthLiteral(1);
    int cached = cl.getIthLiteral(cl.getSize()-1);
    
    if (firstWatched > 0) positiveWatchLists[ firstWatched].emplace_back(i,cached);
    else                  negativeWatchLists[-firstWatched].emplace_back(i,cached);

    if (secondWatched > 0) positiveWatchLists[ secondWatched].emplace_back(i,cached);
    else                   negativeWatchLists[-secondWatched].emplace_back(i,cached);
  }
}

void Solver::buildBinaryClauses (const vector<pair<int,int> >& binClauses) {
  for (auto& c:binClauses) {
    int lit1 = c.first;
    int lit2 = c.second;
    if (lit1 > 0) positiveBinClauses[lit1].push_back(lit2);  
    else          negativeBinClauses[-lit1].push_back(lit2);  
    if (lit2 > 0) positiveBinClauses[lit2].push_back(lit1);  
    else          negativeBinClauses[-lit2].push_back(lit1);  
  }
}

void Solver::discoverImplicitBinClauses (int ctrId, WConstraint& ic) {
  assert(model.currentDecisionLevel() == 0);
  static vector<bool> added(maxLitId() + 1,false);  added.resize(maxLitId()+1,false);
  static stack<int> st;
  
  // Instantiate it to remove true/false lits (makes sense because we are at dl zero)
  // after cleanupPBConstrains(), ic already removed the true and false lits 
  
  ic.sortByDecreasingCoefficient();
  long long int S = maxSumOfConstraintMinusRhs(ic);
  for (int i = 0; i < ic.getSize(); ++i) {
    assert(model.isUndefLit(ic.getIthLiteral(i)));  //rui
    long long int limit = S - ic.getIthCoefficient(i);
    if (i + 1 < ic.getSize() and ic.getIthCoefficient(i+1) <= limit) { // no more binaries  // because limit-ic.getIthCoefficient(i+1) >= 0 for all j > i
      if (not st.empty()) {
        constraintsPB[ctrId].setInitial(true);
        while (not st.empty()) {added[lit2id(st.top())] = false; st.pop();}
      }
      return;
    } 
    
    for (int j = i + 1; j < ic.getSize() and ic.getIthCoefficient(j) > limit; ++j) {
      int lit1 = ic.getIthLiteral(i);
      if (not added[lit2id(lit1)]) {
        //if (lit1 > 0) implicitPositiveBinClauses[lit1].push_back(ctrId);
        //else          implicitNegativeBinClauses[-lit1].push_back(ctrId);
        added[lit2id(lit1)] = true;
        st.push(lit1);
      }
      
      int lit2 = ic.getIthLiteral(j);
      if (not added[lit2id(lit2)]) {
        //if (lit2 > 0) implicitPositiveBinClauses[lit2].push_back(ctrId);
        //else          implicitNegativeBinClauses[-lit2].push_back(ctrId);
        added[lit2id(lit2)] = true;
        st.push(lit2);
      }
    }
  }
  if (not st.empty()) {    
    constraintsPB[ctrId].setInitial(true); // do not delete implicit binaries
    while (not st.empty()) {added[lit2id(st.top())] = false; st.pop();}
  }
}

int Solver::getNextDecisionVar() { 
  int v = maxHeap.consultMax();
  if (v==0) return v; 
  int ctr=0;
  if (strat.randomDecisionCondition()) { // take random decision
    strat.reportRandomDecision();
    while ( ctr < 200 and not model.isUndefVar(v) ) { v = rand() % numVars + 1; ctr++; }
    if ( model.isUndefVar(v) )  return v; 
  }
  v = maxHeap.consultMax();
  while ( v != 0 and not model.isUndefVar(v)) { maxHeap.removeMax(); v=maxHeap.consultMax(); }
  //if (v != 0) maxHeap.reduceScore(v);
  return v;
}

void Solver::takeDecisionForVar (int decVar) {  
  assert( not conflict );    assert( model.isUndefVar(decVar) );
  
  vector<DecPolarity>& pols = strat.decisionPolarities[decVar];
  
  int pol = -1;
  for (uint i = 0; i < pols.size(); ++i) {
    if      (pols[i] == OBJECTIVE)      pol = bestPolarityForVarInObjective[decVar];
    else if (pols[i] == LAST_PHASE)     pol = model.getLastPhase(decVar);
    else if (pols[i] == LAST_SOLUTION) {
      if (stats.numOfSolutionsFound != 0 and stats.numOfConflictsSinceLastSolution < strat.NUM_CONFLICTS_CLOSE_TO_SOLUTION)  // default 1000
        pol = lastSolution[decVar];
    }
    else if (pols[i] == POSITIVE) pol = 1;
    else if (pols[i] == NEGATIVE) pol = 0;
    else if (pols[i] == INITIAL_SOLUTION) {
      if (stats.numOfConflicts <= (uint)strat.NUM_CONFLICTS_CLOSE_TO_SOLUTION)
        pol = initialInputSolution[decVar];
    }
    else if (pols[i] == RANDOM) {break;}
    else {cout << "Non-existent polarity " << pols[i] << " for var " << decVar << endl;exit(1);}

    if      (pol == 1) {setTrueDueToDecision( decVar); return;}
    else if (pol == 0) {setTrueDueToDecision(-decVar); return;}
  }

  // Random polarity
  decVar = (rand()%2?decVar:-decVar);
  setTrueDueToDecision(decVar);
}

void Solver::printStats() const {
  stats.print();
}

//THE FOLLOWING IS FOR DEBUGGING ONLY: ===========================================


void Solver::artificialDecision(int lit)  {
  if (model.isTrueLit( lit)) { cout << lit << "is already true" << endl; return;}
  if (model.isFalseLit(lit)) { cout << lit << "is false!!" << endl; exit(0); }
  setTrueDueToReason(lit,noReason()); 
  //    setTrueDueToDecision(lit); 
  propagate();     
  if (conflict) { cout << "conflict w/ literal " << lit << endl; exit(0); }
}



void Solver::lemmaShorteningAuxFunction (int lit, vector<bool>& isMarked, vector<int>& lemma, int& lastMarkedInLemma, bool filterOutDLZero) {
  assert(not model.isUndefLit(lit));
  int v = abs(lit);
  if (isMarked[v]) return;
  if (filterOutDLZero and model.getDLOfLit(v) == 0) return;
  isMarked[v] = true;
  lemma.push_back(lit);
  ++lastMarkedInLemma;
}

Model *mod;
// PRE: UIP is first in lemma
void Solver::lemmaShortening (vector<int>& lemma){   
  /* Try to mark more intermediate variables, with the goal to minimize
   * the conflict clause.  This is a BFS from already marked variables
   * backward through the implication graph.  It tries to reach other marked
   * variables.  If the search reaches an unmarked decision variable or a
   * variable assigned below the minimum level of variables in the first uip
   * learned clause, then the variable from which the BFS is started is not
   * redundant.  Otherwise the start variable is redundant and will
   * eventually be removed from the learned clause.
   */
      
  if (lemma.size() <= 1) return;

  vector<int> lemmaToLearn;

  static vector<bool> isMarked; isMarked.resize(numVars+1,false);

  if (model.currentDecisionLevel() == 0) return;
 
  //First of all, mark all lits in original lemma.
  for (uint i = 0; i < lemma.size(); ++i) isMarked[abs(lemma[i])] = true;

  int originalSizeLemma = lemma.size();

  //Order lemma's lits from most recent to oldest 
  mod = &model;
  sort(lemma.begin()+1,lemma.end(),[](int lit1, int lit2) {return mod->getDLOfLit(lit1) > mod->getDLOfLit(lit2);}); // 1UIPs is not assigned ==> hence we cannot for its DL
  
  int lowestDL = model.getDLOfLit(lemma.back()); // lowestDL in lemma
  static vector<int> lemmaShortened; lemmaShortened.clear();

  //Go through the lits in lemma, and test if they're redundant
  for (int i=0; i < originalSizeLemma; ++i ){
    int lit = lemma[i];
    bool litIsRedundant=true;
    assert(isMarked[abs(lit)]);

    //Begins test to see if literal is redundant
    if (i == 0 or model.isUndefLit(lit) or model.getReasonOfLit(lit).isUnitOrDecision())      
      litIsRedundant=false;
    else if (model.getDLOfLit(lit) != 0) {
      //We add reasons' lits at the end of the lemma
      Reason r = model.getReasonOfLit(lit);
      int lastMarkedInLemma = originalSizeLemma;
      if (r.isBinClause())
        lemmaShorteningAuxFunction(r.getOtherBinLit(),isMarked,lemma,lastMarkedInLemma,true);
      else if (r.isClause()) {
        Clause& c = clauses[r.getClauseNum()];
        for (int j = 0; j < c.getSize(); ++j) {
          lemmaShorteningAuxFunction(c.getIthLiteral(j),isMarked,lemma,lastMarkedInLemma,true);
        }
      }
      else if (r.isCardinality()){
        const Cardinality& c = cardinalities[r.getCardinalityNum()];
        for (int j = 0; j < c.getSize(); ++j) { // Add all false lits plus lit
          int litInCard = c.getIthLiteral(j);
          if (model.isFalseLit(litInCard) or abs(litInCard) == abs(lit)) {
            lemmaShorteningAuxFunction(litInCard,isMarked,lemma,lastMarkedInLemma,true);
          }
        }
      }
      else if (r.isConstraint()){
        const PBConstraint& c = constraintsPB[r.getCtrId()];
        for (int j = 0; j < c.getSize(); ++j) { // Add all false lits plus lit
          int litInPB = c.getIthLiteral(j);
          if (model.isFalseLit(litInPB) or abs(litInPB) == abs(lit)) {
            lemmaShorteningAuxFunction(litInPB,isMarked,lemma,lastMarkedInLemma,true);
          }
        }
      }
      else assert(false);
    
      //test added literals and subsequent ones....
      int testingIndex = originalSizeLemma;
      while (testingIndex < lastMarkedInLemma){
        int testingLit = lemma[testingIndex];
        assert(isMarked[abs(testingLit)]);
        assert(model.getDLOfLit(lit) != 0);
        if ( model.getDLOfLit(testingLit) < lowestDL or //has lower dl
             model.getReasonOfLit(testingLit).isUnitOrDecision()) { //is decision
          //test fails
          litIsRedundant=false;
          break;
        }

        // Albert: the three true in AuxFunction were false in the previous SAT solver
        // it seems to me that this is stronger as we can ignore dl-zero literals
        Reason r = model.getReasonOfLit(testingLit);
        if (r.isBinClause())
          lemmaShorteningAuxFunction(r.getOtherBinLit(),isMarked,lemma,lastMarkedInLemma,true);
        else if (r.isClause())  {
          Clause& c = clauses[r.getClauseNum()];
          for (int j = 0; j < c.getSize(); ++j)
            lemmaShorteningAuxFunction(c.getIthLiteral(j),isMarked,lemma,lastMarkedInLemma,true);
        }
        else if (r.isCardinality()) {
          const Cardinality& c = cardinalities[r.getCardinalityNum()];
          for (int j = 0; j < c.getSize(); ++j) { // Add all false lits plus lit
            int litInCard = c.getIthLiteral(j);
            if (model.isFalseLit(litInCard) or abs(litInCard) == abs(testingLit)) {
              lemmaShorteningAuxFunction(litInCard,isMarked,lemma,lastMarkedInLemma,true);
            }
          }
        }
        else if (r.isConstraint()) {
          const PBConstraint& c = constraintsPB[r.getCtrId()];
          for (int j = 0; j < c.getSize(); ++j) { // Add all false lits plus lit
            int litInPB = c.getIthLiteral(j);
            if (model.isFalseLit(litInPB) or abs(litInPB) == abs(testingLit)) {
              lemmaShorteningAuxFunction(litInPB,isMarked,lemma,lastMarkedInLemma,true);
            }
          }
        } 
        else assert(false);
        
        ++testingIndex;
      }
      
      assert(testingIndex != lastMarkedInLemma or litIsRedundant);

      //Test ends only if a) Some unit or decision is reached
      //or b) all the reason's lits are already marked

      //Clean tested literals
      while ( lastMarkedInLemma > originalSizeLemma) {
        --lastMarkedInLemma;
        isMarked[abs(lemma[lastMarkedInLemma])] = false;
        lemma.pop_back();
      }
    }

    //Add (or not) litOfLemma to lemmaToLearn
    if (litIsRedundant) {
      lemma[i] = 0;
      isMarked[abs(lit)] = false;
    }
    else lemmaToLearn.push_back(lit);
  }

  lemma.clear();
  for (uint i = 0; i < lemmaToLearn.size(); ++i){
    lemma.push_back(lemmaToLearn[i]);
    isMarked[abs(lemmaToLearn[i])] = false;
  }

  strat.reportLemmaShortening(originalSizeLemma,lemma.size());
  // First lit is UIP
  // Second lit indicates where to Backjump
}  


/* for the moment, just generate the clause:  sum >= 1
   where sum are all the false lits in c plus the lit of x. */  
void Solver::fixRoundingProblemSAT (int l, WConstraint & c) const {
  WConstraint w2;
  int x = abs(l);
  long long int sumTotalMinusRhs = -c.getConstant();
  int coeffL = 0;
  for (int i = 0; i < c.getSize(); ++i) { 
    sumTotalMinusRhs += c.getIthCoefficient(i);
    int var = abs(c.getIthLiteral(i));
    if (var == x) {
      coeffL = c.getIthCoefficient(i);
      //      w2.addMonomial(1,c.getIthLiteral(i));
    }
  }  

  sumTotalMinusRhs -= coeffL;
  int i = 0;
  bool added = false;
  while (sumTotalMinusRhs >= 0 or not added) {
    int lit  = c.getIthLiteral(i);            
    if (model.isFalseLit(lit) and abs(lit) != x and sumTotalMinusRhs >=0) {
      w2.addMonomial(1,lit);
      sumTotalMinusRhs -= c.getIthCoefficient(i);
    }
    else if (abs(lit) == x) {
      w2.addMonomial(1,c.getIthLiteral(i));
      added = true;
    }
    ++i;
  }

  w2.setConstant(1);
  w2.setObjectiveRHS(0,1);
  w2.setIndependentRHS(1,1);
  w2.setShaved(false);
  c = w2;
}


// Returns whether an overflow or a tautology has occurred
bool Solver::applyCut ( int var, const WConstraint & c1, const WConstraint & c2, WConstraint & cut, bool& clash, bool& isInconsistentCut ) {
  assert(c1.isOrderedByIncreasingVariable());
  assert(c2.isOrderedByIncreasingVariable());

  if ((long long)(c1.getConstant()) * c2.getConstant() < TWOTOTHE30TH) {
    strat.reportIntCut();
    return applyCut<int, long long>(var,c1,c2,cut, clash, isInconsistentCut);
  }
  else {
    strat.reportLongIntCut();      
    return  applyCut<long long, int128>(var,c1,c2,cut,clash, isInconsistentCut);
  }
}

template<class T, class G>
bool Solver::applyCut ( int var, const WConstraint & c1, const WConstraint & c2, WConstraint & cut, bool& clash, bool& isInconsistentCut ) {
  bool shaved = (c1.isShaved() or c2.isShaved());
  assert(c1.isOrderedByIncreasingVariable());
  assert(c2.isOrderedByIncreasingVariable());
  if (isInconsistentCut) return false;
  clash = false;
  
  int size1 = c1.getSize(); // conf false ctr
  int size2 = c2.getSize();  // cut reason
  int a1    = c1.getCoefficientBinarySearch(var); 
  int a2    = c2.getCoefficientBinarySearch(var);
  assert(c1.getLiteralBinarySearch(var) == - c2.getLiteralBinarySearch(var)); 
  assert(a1 != 0);
  assert(a2 != 0);
  
  int g    = GCD<int>( a1, a2 );
  T newConstant = 0;
  T k1 = a2 / g; // type long long to force long long type of expressions k1 * ... below
  T k2 = a1 / g; // example: a1=12, a2=18, ====> gcd=6, k1=3, k2=2
  static vector<T> newCoeffs; newCoeffs.clear();
  static vector<int> newLits; newLits.clear();
  int i1 = 0;    int i2 = 0;
  
  while (i1 < size1 and i2 < size2) { // sum using the fact that they are ordered by increasing var
    int lit1 =c1.getIthLiteral(i1);  int coef1=c1.getIthCoefficient(i1); 
    int lit2 =c2.getIthLiteral(i2);  int coef2=c2.getIthCoefficient(i2);
    if      (abs(lit1)<abs(lit2)) { newCoeffs.push_back( k1 * coef1 ); newLits.push_back(lit1); ++i1; } 
    else if (abs(lit1)>abs(lit2)) { newCoeffs.push_back( k2 * coef2 ); newLits.push_back(lit2); ++i2; } 
    else { // same var
      if (abs(lit1) != var) clash = true;
      T lCoef;
      if ( lit1 != lit2 ) { // same var, different signs
        if (k1 * coef1 >= k2 * coef2 ) {  
          newConstant -= k2*coef2;                   // this is the amount that is cancelled out
          lCoef = k1 * coef1 - k2 * coef2;           // this is the amount that remains
          if (lCoef != 0) { newCoeffs.push_back(lCoef); newLits.push_back(lit1); } 
        } else {
          newConstant -= k1*coef1;                   // this is the amount that is cancelled out
          lCoef = k2 * coef2 - k1 * coef1;           // this is the amount that remains
          if (lCoef != 0) { newCoeffs.push_back(lCoef); newLits.push_back(lit2); }
        }
      } else { // same var, same sign
        lCoef = k2 * coef2 + k1 * coef1;
        newCoeffs.push_back(lCoef); newLits.push_back(lit1);
      }
      ++i1; ++i2;
    }
  }
  while (i1 < size1) { // the other one finished first
    int lit1=c1.getIthLiteral(i1);  int coef1=c1.getIthCoefficient(i1);
    newCoeffs.push_back( k1 * coef1 ); newLits.push_back(lit1); ++i1; } 
  while (i2 < size2) { 
    int lit2=c2.getIthLiteral(i2);  int coef2=c2.getIthCoefficient(i2);
    newCoeffs.push_back( k2 * coef2 ); newLits.push_back(lit2); ++i2; } 

  rational<G> c1ObjRHS = static_cast<rational<G>>(c1.getObjectiveRHS());
  rational<G> c1IndRHS = static_cast<rational<G>>(c1.getIndependentRHS());

  rational<G> c2ObjRHS = static_cast<rational<G>>(c2.getObjectiveRHS());
  rational<G> c2IndRHS = static_cast<rational<G>>(c2.getIndependentRHS());
  
  rational<G> cutIndRhs = k1 * c1IndRHS + k2 * c2IndRHS + newConstant;
  rational<G> cutObjRhs = k1 * c1ObjRHS + k2 * c2ObjRHS;
  
  assert(cutIndRhs.denominator() > 0); // nake sure there is not overflow
  assert(cutObjRhs.denominator() > 0);

  newConstant += k1 * c1.getConstant() + k2 * c2.getConstant();

  if (newConstant<=0) {cout << endl <<"applyCut found a tautology " << endl; return true;} // tautology
  if (newCoeffs.size()==0) { // inconsistency:  0 >= 1
    assert(newLits.size() == 0); cut = WConstraint(false); 
    isInconsistentCut = true;
    cout << endl << "applyCut found inconsistency cut:  0 >= 1" << endl; 
    return false; 
  } 
#ifndef NDEBUG
  for (auto x: newCoeffs) if (x == 0) {cout << "OF" << endl; exit(1);}
#endif
  // normalization:  compute gcd of all coeffs that are smaller or equal than the constant
  T gcdV = -1;
  for (uint i = 0; i < newCoeffs.size(); ++i) {
    if (newCoeffs[i] <= newConstant) {
      if (gcdV==-1) gcdV = newCoeffs[i]; 
      else gcdV = GCD<T>( gcdV, newCoeffs[i] );
    }
  }
  if (gcdV == -1) gcdV = newConstant; // in this case all newCoefs are larger than newConstant
  
  newConstant = divisionRoundedUp<T>( newConstant, gcdV );  
  if ( newConstant > TWOTOTHE30TH ) {++stats.numConstantOverflow; return true;}
  
  static vector<int> newCoeffsInt; newCoeffsInt.clear();
  for (uint i = 0; i < newCoeffs.size(); ++i) {
    newCoeffs[i] = divisionRoundedUp<T>(newCoeffs[i],gcdV);
    if (newCoeffs[i] > newConstant) {newCoeffs[i] = newConstant; shaved = true;}  // shaving
    newCoeffsInt.push_back((int)newCoeffs[i]);
  }

  assert(gcdV > 0);
  
  cutIndRhs/=gcdV;
  cutObjRhs/=gcdV;
  
  assert(cutIndRhs.denominator() > 0);
  assert(cutObjRhs.denominator() > 0);
  
  // the overflow would make the search behaviour slightly different
  if (abs(cutIndRhs.numerator()) > INT_MAX or
      abs(cutIndRhs.denominator()) > INT_MAX or
      abs(cutObjRhs.numerator()) > INT_MAX or
      abs(cutObjRhs.denominator()) > INT_MAX ) {++stats.numOverflow; return true;}
  
  pair<int,int> cutIndRHS = { int(cutIndRhs.numerator()),int(cutIndRhs.denominator())};
  pair<int,int> cutObjRHS = { int(cutObjRhs.numerator()),int(cutObjRhs.denominator())};
  
  if (cutObjRHS.first == 0) shaved = false;
  cut = WConstraint(newCoeffsInt, newLits,(int)newConstant,cutIndRHS, cutObjRHS, shaved);

  assert(cut.getSize() > 0);
  
  return false;
}

long long Solver::currentWatchedSNFMMaxCoef (int ctrNum) {
  assert(model.lastPropagatedPBWatch == model.trailSize()-1);
  PBConstraint& c = constraintsPB[ctrNum];
  const int size = c.getSize();
  long long sumMinusRHSCurrent = -c.getConstant() - abs(c.getIthCoefficient(0));
  for (int i = 0; i < size; ++i) { 
    int lit  = c.getIthLiteral(i);
    int coef = c.getIthCoefficient(i);
    if (coef < 0 and !model.isFalseLit(lit)) sumMinusRHSCurrent += abs(coef);
  }
  return sumMinusRHSCurrent;
}

void Solver::checkPropagatedPBs ( PBConstraint& c, int ctrId ) {
  assert(!conflict);
  const int size = c.getSize();
  long long sumMinusRHSCurrent = -c.getConstant();
  for (int i = 0; i < size; ++i) { 
    int lit  = c.getIthLiteral(i);
    int coef = abs(c.getIthCoefficient(i));
    if (not model.isFalseLit(lit)) sumMinusRHSCurrent += coef;
  }
  
  if (sumMinusRHSCurrent < 0) {  // Check it is not a conflict
    cout << "PB " << ctrId << " is conflicting!!  sumMinusRHSCurrent " << sumMinusRHSCurrent << ", snf+maxCoef " << sumOfWatches[ctrId] + abs(c.getIthCoefficient(0)) << ", maxCoef " << abs(c.getIthCoefficient(0)) << " nDecs: " << stats.numOfDecisions << " nConfs: " << stats.numOfConflicts << endl;
    exit(0);
  }
  
  if (!useCounter[ctrId]) {
    sumMinusRHSCurrent = -c.getConstant();
    for (int i = 0; i < size; ++i) { 
      int lit  = c.getIthLiteral(i);
      int coef = c.getIthCoefficient(i);
      if (coef < 0 and !model.isFalseLit(lit)) sumMinusRHSCurrent += abs(coef);
    }
  }
  if (sumMinusRHSCurrent - abs(c.getIthCoefficient(0)) != sumOfWatches[ctrId]) {
    cout << "PB " << ctrId << " slackMC error!!  sumMinusRHSCurrent " << sumMinusRHSCurrent << ", current slackMC " << sumMinusRHSCurrent - abs(c.getIthCoefficient(0)) << ", saved sumOfWatches " << sumOfWatches[ctrId] << ", maxCoef " << abs(c.getIthCoefficient(0)) << " nDecs: " << stats.numOfDecisions << " nConfs: " << stats.numOfConflicts << ", dl " << model.currentDecisionLevel() << ", obj_num " << obj_num << endl;
    exit(0);
  }

  for (int i = 0; i < size; ++i) { 
    int lit  = c.getIthLiteral(i);
    int coef = abs(c.getIthCoefficient(i));
    if ( model.isUndefLit(lit) ) {
      if(sumMinusRHSCurrent - coef < 0) {
        
        cout << endl << "PB "  << ctrId << " not propagate all, sumMinusRHSCurrent " << sumMinusRHSCurrent << ", maxCoef " << abs(c.getIthCoefficient(0)) << ", coef " << coef << ", i = " << i << ", isInitial? " << constraintsPB[ctrId].isInitial() << flush << endl;
        cout << " nDecs: " << stats.numOfDecisions << " nConfs: " << stats.numOfConflicts << endl;
        cout << endl << "real wslk-maxCoef = " << (sumMinusRHSCurrent - abs(c.getIthCoefficient(0))) << ", but we have " << sumOfWatches[ctrId] << flush << endl;
        cout << " nDecs: " << stats.numOfDecisions << " nConfs: " << stats.numOfConflicts << ", dl " << model.currentDecisionLevel() << endl;
        exit(0);
      }
      
      assert(sumMinusRHSCurrent - coef >= 0);
    }    
  }
}

void Solver::checkPropagatedCards ( Cardinality& c, int ctrId ) {
  const int size = c.getSize();
  long long sumMinusRHSCurrent = -c.getDegree();
  for (int i = 0; i < size; ++i) { 
    int lit  = c.getIthLiteral(i);
    int coef = 1;
    if (not model.isFalseLit(lit)) sumMinusRHSCurrent += coef;
  }
  assert(sumMinusRHSCurrent >= 0); // Check it is not a conflict

  for (int i = 0; i < size; ++i) { 
    int lit  = c.getIthLiteral(i);
    int coef = 1;
    if ( model.isUndefLit(lit) ) {
      if(sumMinusRHSCurrent - coef < 0) {
        cout << "CARD " << ctrId << " not propagate all, sumMinusRHSCurrent " << sumMinusRHSCurrent << ", maxCoef " << 1 << ", idx " << i << ", isInitial? " << cardinalities[ctrId].isInitial() << flush << endl;
        cout << endl << "real wslk-maxCoef = " << (sumMinusRHSCurrent - 1) << flush << endl;
        cout << " nDecs: " << stats.numOfDecisions << " nConfs: " << stats.numOfConflicts << endl;

        writeCardinalityNotFalseInfo(c);
      }
      
      assert(sumMinusRHSCurrent - coef >= 0);
    }    
  }
}


void Solver::checkAllConstraintsPropagated() {
  for ( int i = 1; i <= numVars; i++ ){
    if (model.isFalseLit(i)) {
      vector<int>& wl = positiveBinClauses[i];
      if (wl.empty()) continue;
      
      auto itWL = wl.begin();
      while (itWL != wl.end()) {
      assert(model.isTrueLit(*itWL));
      ++itWL;
      }
    }
    
    if (model.isFalseLit(-i)) {
      vector<int>& wl2 = negativeBinClauses[i];
      if(wl2.empty()) continue;
      auto itWL = wl2.begin();
      while (itWL != wl2.end()) {
      assert(model.isTrueLit(*itWL));
      ++itWL;
      }
    }
  }
  
  for(uint i = 0; i < clauses.size(); ++i ){
    Clause cl = clauses[i];
    //int lit_undef = 0;
    int numFalseLit = 0; 
    bool isTrue = false;
    for(int j = 0; j < cl.getSize(); ++j){
      int lit = cl.getIthLiteral(j);
      if(model.isTrueLit(lit)) {isTrue = true; break;}
      else if(model.isFalseLit(lit)) ++numFalseLit;
      //else lit_undef = lit;
    }
    if(isTrue) continue;
    if (numFalseLit == cl.getSize()-1) {
      for(int j = 0; j < cl.getSize(); ++j){
        int lit = cl.getIthLiteral(j);
        cout << lit;
        if (model.isTrueLit(lit)) cout << "(T" << model.getDLOfLit(lit) << ") ";
        else if (model.isFalseLit(lit)) cout << "(F" << model.getDLOfLit(-lit) << ") ";
        else cout << "(U)";      
      }
      cout << "[isInit " << cl.isInitial() << "]" << endl;
    }
    assert(numFalseLit != cl.getSize()-1);
    assert(numFalseLit != cl.getSize());
  }

  for (uint i = 0; i < cardinalities.size(); ++i) {
    Cardinality&  c = cardinalities[i];
    checkPropagatedCards(c,i);
  }
  
  for(uint i = 0; i < constraintsPB.size(); ++i){
    PBConstraint& c = constraintsPB[i];
    checkPropagatedPBs(c, i);
  }  
}
