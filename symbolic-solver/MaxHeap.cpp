#include "MaxHeap.h"
#include <cassert>
#include <cstdlib>
#include <cfloat>
#include <algorithm>
#include <iostream>

using namespace std;

void MaxHeap::percolateUp ( int pos ){
  int node=maxHeap[pos], parentNode;
  while (pos > 1) {                    // not yet at top of the maxHeap
    parentNode = maxHeap[pos/2];
    if (nodeIsGreater(parentNode,node)) break;
    placeNode(parentNode,pos);
    pos = pos/2;
  }
  placeNode(node,pos);  
}

MaxHeap::MaxHeap ( int nElems ):
  maxHeap(nElems+2),
  value(nElems+1),
  heapPositions(nElems+2),
  maxHeapLast(0),
  numElems(nElems){
    maxHeap[0]=0;  
    for (int elem=1;elem<=nElems;elem++){
      maxHeap[elem]=elem;
      value[elem]=1;
      heapPositions[elem]=elem;
    }
    maxHeapLast=nElems;
}

void MaxHeap::print( ){
  for (int i = 1; i <= maxHeapLast; ++i)
    cout << "v" << maxHeap[i] << " --> " << value[maxHeap[i]] << "; ";
  cout << endl;
}

void MaxHeap::reset() { for (int elem = 1; elem <= numElems; elem++ ) value[elem]=0;  }
// void MaxHeap::reset() {
//   double score;
//   for (int elem = 1; elem <= numElems; elem++ ) {
//     score = value[elem] /= (DBL_MAX/20);
//     if (score < DBL_MIN) value[elem] = 0;
//   }
//   return;
//   maxHeapLast=0;
//   for (int elem = 1; elem <= numElems; elem++ ) {
//     value[elem] = rand() % 20000;
//     heapPositions[elem]=0;
//     insertElement( elem );
//   }
//   //  for (int elem = 1; elem <= numElems; elem++ )  value[elem] = 0;  
// }
	  
void MaxHeap::insertElement ( int elem ){
  if (heapPositions[elem]!=0) return;
  int pos = ++maxHeapLast;
  maxHeap[pos]=elem;
  percolateUp(pos);
}

bool MaxHeap::increaseValueBy ( int elem, double increment ){
  assert(increment >= 0);
  double newVal = value[elem]+increment;
  if (newVal > DBL_MAX) return true;  // i.e., newVal is "infty": overflow.
  value[elem]+=increment;
  int pos = heapPositions[elem];
  if (pos) percolateUp(pos); //if in heap percolate up
  return false;
}

void MaxHeap::removeMax ( ){
  int      resultVar;
  int      pos=1, childPos=2;
  int      node, childNode, rchildNode;
  assert(maxHeapLast != 0);                 // Heap must be non-empty
  resultVar = maxHeap[1];
  heapPositions[resultVar] = 0;             // out of heap
  node = maxHeap[maxHeapLast--];            // now sink node until its place:
  while (childPos <= maxHeapLast) {         // i.e., while lchild exists
    childNode = maxHeap[childPos];
    if (childPos < maxHeapLast) {           // if rchild also exists, make
      rchildNode = maxHeap[childPos+1];     //   childNode the largest of both:
      if (nodeIsGreater(rchildNode,childNode)) {childNode=rchildNode; childPos++;}
    }
    if (nodeIsGreater(node,childNode)) break;  // no need to sink any further
    placeNode(childNode,pos);
    pos = childPos;
    childPos = pos*2;
  }
  if (maxHeapLast) placeNode(node,pos);
}

void MaxHeap::reduceScore(int v) { // used after chosing this var for decision based on score
  if (heapPositions[v]==0) // v is not in heap
    value[v] *= 0.9;
  else {
    assert( v == consultMax() );
    removeMax();
    value[v] *= 0.9;
    insertElement(v);
  }
}  

void MaxHeap::applyVariableRenaming (const vector<int>& oldVar2NewLit, int newNumVars, int mark1, int mark2) {
  vector<double> accumulatedScore(newNumVars+1);
  for (uint i = 1; i < maxHeap.size() - 1; ++i) {
    if (oldVar2NewLit[maxHeap[i]] != mark1 and oldVar2NewLit[maxHeap[i]] != mark2) {
      int newVar = abs(oldVar2NewLit[maxHeap[i]]);
      accumulatedScore[newVar] += value[maxHeap[i]];
    }
  }

  vector<pair<int,double> > varScore(newNumVars+1);
  for (int v = 1; v <= newNumVars; ++v) varScore[v] = {v,accumulatedScore[v]};
  sort(varScore.begin()+1,varScore.end(),
       [](const pair<int,double> & p1, const pair<int,double> & p2) { return p1.second > p2.second; } ); // do not consider initial {0,0}

  //  for (auto& p : varScore) cout << "[" << p.first << "," << p.second << "] ";
  //cout << endl;
  
  // Now we have new vars sorted by score. We can place them in the heap
  maxHeap = vector<int>(newNumVars+2);;
  value = vector<double>(newNumVars+1);
  heapPositions = vector<int>(newNumVars+2);
  numElems = newNumVars;
  maxHeap[0] = 0;
  for (uint i = 1; i < varScore.size(); ++i) { // do not consider initial {0,0}
    maxHeap[i] = varScore[i].first;
    value[varScore[i].first] = varScore[i].second;
    heapPositions[varScore[i].first] = i;
  }
  maxHeapLast = newNumVars;
}
