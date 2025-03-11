#ifndef INC_STATISTICS_H
#define INC_STATISTICS_H

#include <iostream>
class Statistics {

 public:
  int           numOfVars;

  int           numOfSolutionsFound;
  long long int  costOfBestSolution, lastSubtractConstant, RhsLB, RhsUB, costLB, costUB;

  uint           numOfDecisions;
  uint           numOfConflicts;
  int            numOfBackjump;
  int            numOfPurelySATConflictAnalysis;

  long long int numOfResolutions;

  uint           numOfRestarts;
  uint           numOfCleanUps;
  long long int numOfPropagationsPB;
  long long int numOfPropagationsClauses;
  long long int numOfPropagationsBinClauses;
  long long int numOfPropagationsPBCounter;
  long long int numOfPropagationsPBWatch;
  long long int numOfPropagationsCards;
  
  long long int numOfWatchedCtrs = 0, numOfCounterCtr = 0;
  long long int numConstantOverflow = 0;
  
  unsigned long long int numGLPB = 0, numGLPBWatch = 0;
  unsigned long long int numCheckWatchidx = 0, numLoadPBCounter = 0, numLoadPBWatch = 0;
  unsigned long long int numGLclauses = 0;
  unsigned long long int numGLcards = 0;
  
  int numPerc = 0;
  double sumObjRHSNumG0PercNotCls = 0;
  
  uint PBObjNumG0NotShaved = 0;
  double sumPercPBObjNumG0NotShaved = 0;
  
  uint numPBG0NotShaved = 0, numUpdateRHS = 0;
  uint numRHSObjNumE0 = 0, numRHSObjNumG0NotShaved = 0, numRHSObjNumG0Shaved = 0;
  uint numCardObjNumG0Shaved = 0, numCardObjNumG0NotShaved = 0;
  int nSoluExistPB = 0, nSoluExistCard = 0; double sumPercE0 = 0, sumPercG0Shaved = 0, sumPercG0NotShaved = 0, sumPercCardG0 = 0;
  
  int numPercCompute = 0;
  uint numComputeDLPB, numComputeDLCard = 0;
  double sumPercCompute = 0, sumPercComputePB = 0, sumPercComputeCard = 0;
  
  uint numOverflow = 0, numSmallerNewRHS = 0, numSmallerNewRHSCard = 0;
  uint numValidUpdatesPB = 0, numValidUpdatesCard = 0, numPercValid = 0, tryToWatchMoreLits = 0, tryToWatchMoreLitsEnough = 0;
  double sumPercValid = 0, sumPercValidPB = 0, sumPercValidCard = 0, sumPercValidPBEnoughWatches = 0;
  uint numEqualMaxOptRhs = 0, numSmallerMaxOptRhs = 0, numGreaterMaxOptRhs = 0, numCheckedForMaxOptRhs = 0, numSmallerCostUB = 0;
  
  int           numOfIntCuts;
  int           numOfLongIntCuts;

  int           numOfLemmaShortenings;
  double        sumOfPercReductionsInLemmaShortenings;

  int           numOfNewPBConstraints;
  int           numOfNewCardinalities;
  int           numOfNewClauses;
  int           numOfBinClauses;

  int           numOfSurvivingInitPBConstraints;
  int           numOfSurvivingInitCardinalities;
  int           numOfSurvivingInitClauses;

  int           numOfInitialPBConstraints; // when we start the search
  int           numOfInitialCardinalities; // when we start the search
  int           numOfInitialClauses;       // when we start the search
  int           numOfInitialBinClauses;    // when we start the search

  int           numOfTotalLearnedPBConstraints;
  int           numOfTotalLearnedCardinalities;
  int           numOfTotalLearnedClauses;
  int           numOfTotalLearnedBinClauses;

  long long int numOfIntsInPbsAndClauses;

  long long int numOfLearnedLitsInPbs;
  long long int numOfLearnedLitsInCards;
  long long int numOfLearnedLitsInClauses;

  int           numOfConflictsSinceLastRestart;
  int           numOfDecisionsSinceLastRestart;
  int           numOfConflictsSinceLastSolution;

  clock_t       startSolvingTime;
  clock_t       lastTimeWhenStatisticsPrinted;

  int           numOfPBConstraintsInConflicts;
  int           numOfCardinalitiesInConflicts;
  int           numOfClausesInConflicts;
  int           numOfBinClausesInConflicts;
  
  struct { double process, real; } time;

  Statistics (clock_t beginTime, int nVars) :

    numOfVars(nVars),
    numOfSolutionsFound(0),
    numOfDecisions(0),
    numOfConflicts(0),
    numOfBackjump(0),
    numOfPurelySATConflictAnalysis(0),
    numOfResolutions(0),

    numOfRestarts(0),
    numOfCleanUps(0),
    numOfPropagationsPB(0),
    numOfPropagationsClauses(0),
    numOfPropagationsBinClauses(0),
    numOfPropagationsPBCounter(0),
    numOfPropagationsPBWatch(0),
    numOfIntCuts(0),
    numOfLongIntCuts(0),

    numOfLemmaShortenings(0),
    sumOfPercReductionsInLemmaShortenings(0),

    numOfNewPBConstraints(0),
    numOfNewCardinalities(0),
    numOfNewClauses(0),
    numOfBinClauses(0),

    numOfInitialPBConstraints(0),
    numOfInitialCardinalities(0),
    numOfInitialClauses(0),
    numOfInitialBinClauses(0),

    numOfTotalLearnedPBConstraints(0),
    numOfTotalLearnedCardinalities(0),
    numOfTotalLearnedClauses(0),
    numOfTotalLearnedBinClauses(0),

    numOfIntsInPbsAndClauses(0),

    numOfLearnedLitsInPbs(0),
    numOfLearnedLitsInCards(0),
    numOfLearnedLitsInClauses(0),

    numOfConflictsSinceLastRestart(0),
    numOfDecisionsSinceLastRestart(0),
    numOfConflictsSinceLastSolution(0),

    startSolvingTime(beginTime),
    lastTimeWhenStatisticsPrinted(beginTime),

    numOfPBConstraintsInConflicts(0),
    numOfCardinalitiesInConflicts(0),
    numOfClausesInConflicts(0),
    numOfBinClausesInConflicts(0)
  
    {}

  inline void print ( ) const {
    cout << endl;
    cout << "Solutions found:          " << numOfSolutionsFound << endl;
    if (numOfSolutionsFound)
      cout << "Cost of best solution:    " << costOfBestSolution << endl;
    cout << "Decisions:                " << numOfDecisions << endl;
    cout << "Conflicts:                " << numOfConflicts << endl;
    cout << "Restarts:                 " << numOfRestarts << endl;
    cout << "CleanUps:                 " << numOfCleanUps << endl;
    cout << "Initial PBs:              " << numOfInitialPBConstraints << endl;
    cout << "Initial Cards:            " << numOfInitialCardinalities << endl;
    cout << "Initial Clauses:          " << numOfInitialClauses << endl;
    cout << "Initial BinClauses:       " << numOfInitialBinClauses << endl;
    cout << "Final PBs:                " << numOfSurvivingInitPBConstraints + numOfNewPBConstraints << endl;
    cout << "Final Cards:              " << numOfSurvivingInitCardinalities + numOfNewCardinalities << endl;
    cout << "Final Clauses:            " << numOfSurvivingInitClauses + numOfNewClauses << endl;
    cout << "Final BinClauses:         " << numOfBinClauses << endl;
    cout << "Final learned PBs:        " << numOfNewPBConstraints << endl;
    cout << "Final learned Cards:      " << numOfNewCardinalities << endl;
    cout << "Final learned Clauses     " << numOfNewClauses << endl;
    cout << "Total learned PBs:        " << numOfTotalLearnedPBConstraints << endl;
    cout << "Total learned Cards:      " << numOfTotalLearnedCardinalities << endl;
    cout << "Total learned Clauses:    " << numOfTotalLearnedClauses << endl;
    cout << "Total learned BinClauses: " << numOfTotalLearnedBinClauses << endl;
    cout << "Avg. size of learned PBs: " << double(numOfLearnedLitsInPbs)/numOfTotalLearnedPBConstraints << endl;
    cout << "Avg. size of learned Cards: " << double(numOfLearnedLitsInCards)/numOfTotalLearnedCardinalities << endl;
    cout << "Avg. size of learned cls: " << double(numOfLearnedLitsInClauses)/numOfTotalLearnedClauses << endl;
    cout << "avg. %red. lemma short.:  " << sumOfPercReductionsInLemmaShortenings/numOfLemmaShortenings*100 << endl;
    cout << "Long-int cuts:            " << numOfLongIntCuts << endl;
    cout << "Integer cuts:             " << numOfIntCuts << endl;
    cout << "avg. num resolutions/conf:" << numOfResolutions/double(numOfPurelySATConflictAnalysis) << endl;
    cout << "avg. num cuts/conf:       " << (numOfIntCuts + numOfLongIntCuts)/double(numOfConflicts-numOfPurelySATConflictAnalysis) << endl;
    
    long long numOfPropagationsPBTotal = numOfPropagationsPBCounter + numOfPropagationsPBWatch;
    double totalProps = numOfPropagationsPBTotal + numOfPropagationsCards + numOfPropagationsClauses + numOfPropagationsBinClauses;
    
    cout << "%Prop in PBs:            " << numOfPropagationsPB/totalProps*100 << "%" << endl;
    cout << "%Prop in Cards:          " << numOfPropagationsCards/totalProps*100 << "%" << endl;
    cout << "%Prop in Clauses:        " << numOfPropagationsClauses/totalProps*100 << "%" << endl;
    cout << "%Prop in BinClauses:     " << numOfPropagationsBinClauses/totalProps*100 << "%" << endl;
    cout << "Props in PBs:            " << numOfPropagationsPBTotal << " ( %Counter: " << (double)numOfPropagationsPBCounter/numOfPropagationsPBTotal*100 
           << "% ,%Watch: " << (double)numOfPropagationsPBWatch/numOfPropagationsPBTotal*100 << "% )"<< endl;
    
    cout << "Props in Cards:          " << numOfPropagationsCards     << endl;
    cout << "Props in Clauses:        " << numOfPropagationsClauses     << endl;
    cout << "Props in BinClauses:     " << numOfPropagationsBinClauses  << endl;
    cout << "Props:                   " << totalProps                   << endl;
    
    cout << "numLoadPB:                 " << (numLoadPBCounter + numLoadPBWatch) << " (counter " << numLoadPBCounter << " ,watch " << numLoadPBWatch << " )" << endl;        
    
    cout << "numOfWatchedCtrs:        " << numOfWatchedCtrs << " ( " << (double)numOfWatchedCtrs/(numOfWatchedCtrs+numOfCounterCtr)*100 << "% )" << endl;        
    cout << "numOfCounterCtr:         " << numOfCounterCtr << " ( " << (double)numOfCounterCtr/(numOfWatchedCtrs+numOfCounterCtr)*100 << "% )" << endl;
    
    long long totalConf = numOfPBConstraintsInConflicts + numOfCardinalitiesInConflicts + numOfClausesInConflicts + numOfBinClausesInConflicts;
    cout << ". PB    conf: " << numOfPBConstraintsInConflicts << " ,perc " << (double)numOfPBConstraintsInConflicts/totalConf*100 << "%" << endl;
    cout << ". card  conf: " << numOfCardinalitiesInConflicts << " ,perc " << (double)numOfCardinalitiesInConflicts/totalConf*100 << "%" << endl;
    cout << ". cl    conf: " << numOfClausesInConflicts << " ,perc " << (double)numOfClausesInConflicts/totalConf*100 << "%" << endl;
    cout << ". bin   conf: " << numOfBinClausesInConflicts << " ,perc " << (double)numOfBinClausesInConflicts/totalConf*100 << "%" << endl << endl;     
    
    // -bt0 = false, only update the RHS of constraints that will not be falsified (counter >= 0) 
    cout << "avgPerc.Valid:         " << sumPercValid/numPercValid << "%" << " ,sumPerc " << sumPercValid << " ,nPerc " << numPercValid << endl;
    cout << "avgPerc.ValidPB:       " << sumPercValidPB/numPercValid << "%" << " ,sumPerc " << sumPercValidPB << endl;        
    cout << "avgPerc.ValidCard:     " << sumPercValidCard/numPercValid << "%" << " ,sumPerc " << sumPercValidCard << endl;
    cout << "avgPerc.ValidPBTryMore:  " << sumPercValidPBEnoughWatches/numPercValid << "%" << " ,sumPerc " << sumPercValidPBEnoughWatches << endl;
    
    // average percent in all cleanups
    cout << "\navgPerc.sumPercPBObjNumG0NotShaved:    " << sumPercPBObjNumG0NotShaved/numPerc << "%" << " ,sumPerc " << sumPercPBObjNumG0NotShaved << " ,nPerc " << numPerc << endl << endl;  
    
    // statistics at each new solution
    cout << "avgPerc.RHSObjNumE0:    " << sumPercE0/nSoluExistPB << "%" << " ,sumPerc " << sumPercE0 << " ,nPerc " << nSoluExistPB << endl;  
    cout << "avgPerc.G0Shaved:       " << sumPercG0Shaved/nSoluExistPB << "%" << " ,sumPerc " << sumPercG0Shaved << endl;  
    cout << "avgPerc.G0NotShaved:    " << sumPercG0NotShaved/nSoluExistPB << "%" << " ,sumPerc " << sumPercG0NotShaved << endl;
    cout << "avgPerc.G0Card:         " << sumPercCardG0/nSoluExistCard << "%" << " ,sumPerc " << sumPercCardG0 << " ,nSoluExistCard " << nSoluExistCard << endl;  
    
    cout << "numUpdateRHS          " << numUpdateRHS << endl;
    cout << "numSmallerNewRHS      " << numSmallerNewRHS << endl;
    cout << "numSmallerNewRHSCard  " << numSmallerNewRHSCard << endl;
    cout << "tryToWatchMoreLits    " << tryToWatchMoreLits << endl;
    
    cout << "\nnumOverflow           " << numOverflow << endl;
    cout << "#over TWOTOTHE30TH:   " << numConstantOverflow << endl;  
    
    cout << "\nnumGreaterMaxOptRhs:   " << numGreaterMaxOptRhs << " ,numCheckedForMaxOptRhs " << numCheckedForMaxOptRhs << endl;  
    cout << "numSmallerMaxOptRhs:   " << numSmallerMaxOptRhs << " ( " << (double)numSmallerMaxOptRhs/numCheckedForMaxOptRhs*100 << "% )" << endl;  
    cout << "numEqualMaxOptRhs:     " << numEqualMaxOptRhs   << " ( " << (double)numEqualMaxOptRhs/numCheckedForMaxOptRhs*100 << "% )" << endl;  
    cout << "numSmallerCostUB:     " << numSmallerCostUB << endl;  
  }

  inline void shortPrint ( ) {
    static int n = 0;
    ++n;
    numOfPropagationsPB = numOfPropagationsPBCounter + numOfPropagationsPBWatch;
    lastTimeWhenStatisticsPrinted = clock();
    cout << endl << double(lastTimeWhenStatisticsPrinted/CLOCKS_PER_SEC) << "s. Decs: " << numOfDecisions
   << ". confs: " << numOfConflicts << "(" << numOfPurelySATConflictAnalysis/double(numOfConflicts)*100 << "% SAT)"
   << ". init PBs: " << numOfSurvivingInitPBConstraints
   << ". init cls: " << numOfSurvivingInitClauses
   << ". PB lemmas: " << numOfNewPBConstraints
   << ". cl lemmas: " << numOfNewClauses
   << ". bin cls: " << numOfBinClauses
   << ". PB  conf: " << numOfPBConstraintsInConflicts
   << ". card  conf: " << numOfCardinalitiesInConflicts
   << ". cl  conf: " << numOfClausesInConflicts
   << ". bin conf: " << numOfBinClausesInConflicts
   << ". %props PB: " << double(numOfPropagationsPB)/(numOfPropagationsPB+numOfPropagationsClauses+numOfPropagationsBinClauses) * 100  << "%"
   << ". %props cl: " << double(numOfPropagationsClauses)/(numOfPropagationsPB+numOfPropagationsClauses+numOfPropagationsBinClauses) * 100  << "%";
    if (numOfSolutionsFound > 0) cout << ". incumbent: " << costOfBestSolution << "  ";
    else                 cout << ". incumbent: -  ";
  }
};

#endif /* INC_STRATEGY_H */
