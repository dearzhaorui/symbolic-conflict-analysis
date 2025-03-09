#ifndef INC_MAXHEAP_H
#define INC_MAXHEAP_H

#include <vector>
#include <assert.h>

using namespace std;

class MaxHeap{
private:
  vector<int>     maxHeap;
  vector<double>  value;
  vector<int>     heapPositions;  // position in heap of each var (0 if not in maxHeap)
  int                  maxHeapLast;    // zero iff heap is empty   
  int                  numElems;  
  inline bool nodeIsGreater ( int n1, int n2 ) const { return (value[n1]>value[n2] or (value[n1]==value[n2] and n1>n2)); }
  inline void placeNode ( int  n, int pos ){  maxHeap[pos]=n;  heapPositions[n]=pos; }
  void percolateUp ( int pos );

public:
  MaxHeap ( int nElems );
  void reset();
  inline int consultMax ( ) const{  if (!maxHeapLast) return 0;  else return maxHeap[1]; } //returns 0 if empty
  void insertElement ( int elem );
  bool increaseValueBy ( int elem, double increment );
  void removeMax ( );
  void reduceScore(int v);
  void  applyVariableRenaming (const vector<int>& oldVar2NewLit, int newNumVars, int mark1, int mark2);
  void print( );
  double score (int v) {assert(v >= 1); return value[v];}
};
#endif /* INC_MAXHEAP_H */
