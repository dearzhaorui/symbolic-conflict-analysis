#include "Model.h"
using namespace std;

Model::Model(int nVars) {
  modelStack = vector<StackElement>(0);
  //    truthValueOfVar  = vector<int>( nVars + 1, 0  );
  truthValueOfVar  = new char [nVars+1];
  for( int i=0; i<=nVars; i++) truthValueOfVar[i]=0;
  lastPhaseOfVar   = vector<int>( nVars + 1, -1 );
  stackHeightOfVar = vector<int>( nVars + 1, -1 );
  lastPropagatedPB = -1;
  lastPropagatedPBWatch = -1;
  lastPropagatedCard = -1;
  lastPropagatedClause = -1;
  lastPropagatedBinClause = -1;
  decisionLevel = 0;
  agilityCounter = 0;
}
void Model::printStack() const {
  cout << endl << "MODEL STACK:   dl   lit   reasonConstraintNum" << endl;
  for (int i=0; i<(int)modelStack.size(); i++) {
    cout << "     "<< i << ":         " << getDLAtHeight(i) << "   x";
    if (getLitAtHeight(i)>0) 
      cout << abs(getLitAtHeight(i)) << "=1       ";
    else
      cout << abs(getLitAtHeight(i)) << "=0       ";
    cout << getReasonAtHeight(i) << endl;
  }
  cout << endl << endl;
}

void Model::setTrueDueToDecision( int lit ) {
  assert(isUndefLit(lit));
  ++decisionLevel;
  modelStack.push_back(StackElement(lit,decisionLevel));
  int var = abs(lit);
  if (lit>0) setTrue(var); else setFalse(var);
  stackHeightOfVar[var] = modelStack.size()-1;
}

void Model::setTrueDueToReason( int lit, const Reason& r) {
  agilityCounter *= g;

  if      (lit > 0 and lastPhaseOfVar[lit]  == 0) agilityCounter += 1-g;
  else if (lit < 0 and lastPhaseOfVar[-lit] == 1) agilityCounter += 1-g;  

  modelStack.push_back(StackElement(lit,decisionLevel,r));
  int var = abs(lit);
  if (lit>0) setTrue(var); else setFalse(var);
  stackHeightOfVar[var] = modelStack.size()-1;
}

int Model::popAndUnassign() { 
  assert ( modelStack.size() > 0 );
  int lit = modelStack.back().lit;
  int var = abs( lit );
  if (isTrueVar(var)) lastPhaseOfVar[var] = 1; else lastPhaseOfVar[var] = 0;
  setUndef(var);
  stackHeightOfVar[var] = -1;
  modelStack.pop_back();
  decisionLevel = modelStack.size()==0?0:modelStack[modelStack.size()-1].dl;
  
  int maxIdx = (int)modelStack.size()-1;
  if (lastPropagatedPB > maxIdx)        lastPropagatedPB = maxIdx;
  if (lastPropagatedPBWatch > maxIdx)   lastPropagatedPBWatch = maxIdx;
  if (lastPropagatedCard > maxIdx)      lastPropagatedCard = maxIdx;
  if (lastPropagatedClause > maxIdx)    lastPropagatedClause = maxIdx;
  if (lastPropagatedBinClause > maxIdx) lastPropagatedBinClause = maxIdx;
  return lit;
}

// mapping: oldVar --> newLit
void Model::applyVariableRenaming (const vector<int>& mapping, int newNumVars) {
  assert(decisionLevel == 0);
  vector<StackElement> oldStack = modelStack;
  modelStack.clear();
  delete[] truthValueOfVar;
  truthValueOfVar = new char[newNumVars + 1];
  for( int i=0; i<=newNumVars; i++) truthValueOfVar[i]=0;
  stackHeightOfVar.resize(newNumVars+1);
  for (auto& elem : stackHeightOfVar) elem = -1;

  // for (auto& elem : oldStack) {
  //   int newLit = (elem.lit > 0 ? mapping[elem.lit] : -mapping[-elem.lit]);
  //   setTrueDueToReason(newLit,elem.reason);
  // }

  vector<int> newLastPhase(newNumVars + 1);
  for (uint v = 1; v < mapping.size(); ++v) 
    if (mapping[v] > 0 and mapping[v] <= newNumVars)   // If < 0 then v is not representative and we do not care
      newLastPhase[mapping[v]] = lastPhaseOfVar[v];

  lastPhaseOfVar = newLastPhase;
  lastPropagatedPB =        (int)modelStack.size() - 1;
  lastPropagatedPBWatch =   (int)modelStack.size() - 1;
  lastPropagatedCard =      (int)modelStack.size() - 1;
  lastPropagatedClause =    (int)modelStack.size() - 1;
  lastPropagatedBinClause = (int)modelStack.size() - 1;
}
