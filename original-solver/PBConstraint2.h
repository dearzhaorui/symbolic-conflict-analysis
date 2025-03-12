#ifndef INC_PBCONSTRAINT_H
#define INC_PBCONSTRAINT_H

#include "MemoryManager.h"
#include <vector>
#include <string>
#include <cassert>
#include <algorithm>
#include <iostream>
#include "Constraint.h"

class WConstraint;

using namespace std;

class PBConstraint { // numBackjump[-7], maxWIdx[-6]
  uint ptr;   // isInit[-5], activity[-4], LBD[-3] rhs[-2], size[-1] (number of vars in lhs)
            // longPtr[0] is <coeff1,x1,coeff2,x2,coeff3,x3,....>
            // longPtr[2*size()] starts number of propagations of every lit
           
 public:
  
  PBConstraint ( );
  PBConstraint (const PBConstraint& c);
  // PRE: lits are ordered by increasing variable, posCoeffs > 0, posCoeff.size() > 0,  r > 0, 
  PBConstraint (const vector<int>& posCoeffs, const vector<int>& lits, int r, bool isInit, int activity, int LBD);
  // PRE: in l, pairs are <coeff,lit> and are ordered by increasing variable
  // coeffs > 0, r > 0, l.size() > 0
  PBConstraint (const vector<pair<int,int> >& l, int r, bool isInit, int activity, int LBD); 
  // PRE: wc is ordered by increasing variable. wc is not a tautology or contradiction
  PBConstraint (const WConstraint& wc, bool isInit, int activity, int LBD);
  ~PBConstraint ();

  void freeMemory        ( );
  int  getSize           ( )       const;
  int  getNumInts        ( )       const;
  int  getConstant       ( )       const;
  int  getCoefficient    (int var) const; // coeff that goes with var or -var
  int  getLiteral        (int var) const; // return var, -var or zero
  int  getIthLiteral     (int i)   const;   // 0 <= i < getSize()
  int  getIthCoefficient (int i)   const;   // 0 <= i < getSize()
  int  getActivity       (     )   const;
  void setActivity       (int a);
  void increaseActivity  (int amount);
  bool isInitial         (     )   const;
  void setInitial        (bool b);
  int  getLBD            (     )   const;
  void setLBD            (int lbd);
  
  bool isIthLitWatched         (int i)   const;
  void setIthLitWatched        (int i, bool w);
  int getMaxWIdx        (     )   const;  // optimization 1: the max idx of watched lits  
  void setMaxWIdx        (int i);  
  int getNumBackjump    (     )   const;  // optimization 1: check if there's already one backjump before propagating
  void setNumBackjump    (int i); 
  
  int  maxCoefOfConstraint( ) const;
  void simplify ( );
  friend ostream& operator<<(ostream& os, const PBConstraint& pc);

  inline PBConstraint operator= (const PBConstraint& c) {ptr = c.ptr; return *this; }
  
 //private:
  inline int* longPointer() const;
  
  // size[-1], rhs[-2], watchIdx[-3], numBackjump[-4], activity[-5], isInit[-6], LBD[-7], capacity[-8]

  void setSize(int s)        { longPointer()[-1] = s;}
  void setConstant (int co)  { longPointer()[-2] = co; assert(getConstant() == co);}
  void setIthCoefficient (int i, int value) {
    assert(value > 0);
    assert(i < getSize() and i >= 0);
    longPointer()[2*i] = value;
  }

  template <class Constraint>
  friend
  void simplify(Constraint& cons);
};

#include "WConstraint.h"

inline PBConstraint::PBConstraint (const PBConstraint& c) {
  assert(c.ptr != 0);
  ptr = c.ptr;
}

inline PBConstraint::PBConstraint ( ){
  ptr = 0;
}

// PRE: lits are ordered by increasing variable, posCoeffs > 0, posCoeff.size() > 0,  r > 0, 
inline PBConstraint::PBConstraint (const vector<int>& posCoeffs, const vector<int>& lits, int r, bool isInit, int activity, int LBD) {
  assert(isOrdered(lits));
  assert(posCoeffs.size() == lits.size());
  assert(posCoeffs.size() > 0);
  assert(r > 0);
  
  MemoryManager* mem = MemoryManager::getMemoryManager();
  int size = (int)2*posCoeffs.size() + 8; // size, rhs, watchIdx, numBackjump, activity, isInit, LBD, capacity
  int* longPtr;
  int allocatedInts;
  mem->alloc(size,ptr,longPtr,allocatedInts);
  longPtr[7] = (int)posCoeffs.size(); 
  longPtr[6] = r;
  longPtr[5] = 0; 
  longPtr[4] = 0;
  longPtr[3] = activity;
  longPtr[2] = isInit;
  longPtr[1] = LBD;
  longPtr[0] = allocatedInts;
  
  longPtr += 8;   // size[-1], rhs[-2], watchIdx[-3], numBackjump[-4], activity[-5], isInit[-6], LBD[-7], capacity[-8]
  for (uint i = 0; i < lits.size(); ++i) {
    assert(posCoeffs[i] > 0);
    longPtr[2*i] = posCoeffs[i];
    longPtr[2*i + 1] = lits[i];
  }
  assert(longPtr == longPointer());
  assert(isInitial() == isInit);
  assert(getActivity() == activity);
  assert(getLBD() == LBD);
  assert(getMaxWIdx() == getNumBackjump()); 
  assert(getSize() == (int)lits.size());
  assert(getConstant() == r);
  //for (uint i = 0; i < lits.size(); ++i) {
    //assert(getIthCoefficient(i) == posCoeffs[i]);
    //assert(getIthLiteral(i)     == lits[i]);
  //}
}


// PRE: in l, pairs are <coeff,lit> and are ordered by increasing variable
// coeffs > 0, r > 0, l.size() > 0
inline PBConstraint::PBConstraint (const vector<pair<int,int> >& l, int r, bool isInit, int activity, int LBD) {
  assert(l.size() > 0);
  assert(isOrderedByIncreasingVariable(l));
  assert(r > 0);
  
  MemoryManager* mem = MemoryManager::getMemoryManager();
  int size = (int)2*l.size() + 8; // size, rhs, watchIdx, numBackjump, activity, isInit, LBD, capacity
  int* longPtr;
  int allocatedInts;
  mem->alloc(size,ptr,longPtr,allocatedInts);
  longPtr[7] = (int)l.size(); 
  longPtr[6] = r;
  longPtr[5] = 0; 
  longPtr[4] = 0;
  longPtr[3] = activity;
  longPtr[2] = isInit;
  longPtr[1] = LBD;
  longPtr[0] = allocatedInts;
  
  longPtr += 8;   // size[-1], rhs[-2], watchIdx[-3], numBackjump[-4], activity[-5], isInit[-6], LBD[-7], capacity[-8]
  for (uint i = 0; i < l.size(); ++i) {
    assert(l[i].first > 0);
    longPtr[2*i] = l[i].first;
    longPtr[2*i + 1] = l[i].second;
  }
  
  assert(longPtr == longPointer());
  assert(isInitial() == isInit);
  assert(getActivity() == activity);
  assert(getLBD() == LBD);
  assert(getMaxWIdx() == getNumBackjump()); 
  assert(getSize() == (int)l.size());
  assert(getConstant() == r);
  //for (uint i = 0; i < l.size(); ++i) {
    //assert(getIthCoefficient(i) == l[i].first);
    //assert(getIthLiteral(i)     == l[i].second);
  //}
} 

// PRE: wc is ordered by increasing variable. wc is not a tautology or contradiction
inline PBConstraint::PBConstraint (const WConstraint& wc, const bool isInit, int activity, int LBD) {
  //assert(wc.isOrderedByIncreasingVariable());  // for counter propgation
  //assert(wc.isOrderedByDecreasingCoefficient()); // for watched prop, it's right
  assert(wc.getSize() > 0);
  
  MemoryManager* mem = MemoryManager::getMemoryManager();
  int size = (int)2*wc.getSize() + 8; // size, rhs, watchIdx, numBackjump, activity, isInit, LBD, capacity
  int* longPtr;
  int allocatedInts;
  mem->alloc(size,ptr,longPtr,allocatedInts);
  longPtr[7] = (int)wc.getSize(); 
  longPtr[6] = wc.getConstant();
  longPtr[5] = 0; 
  longPtr[4] = 0;
  longPtr[3] = activity;
  longPtr[2] = isInit;
  longPtr[1] = LBD;
  longPtr[0] = allocatedInts;
  
  longPtr += 8;   // size[-1], rhs[-2], watchIdx[-3], numBackjump[-4], activity[-5], isInit[-6], LBD[-7], capacity[-8]

  for (int i = 0; i < wc.getSize(); ++i) {
    longPtr[2*i] = wc.getIthCoefficient(i);
    longPtr[2*i + 1] = wc.getIthLiteral(i);
  }
  
  assert(longPtr == longPointer());
  assert(isInitial() == isInit);
  assert(getActivity() == activity);
  assert(getLBD() == LBD);
  assert(getMaxWIdx() == getNumBackjump()); 
  assert(getSize() == wc.getSize());
  assert(getConstant() == wc.getConstant());
  //for (int i = 0; i < wc.getSize(); ++i) {
    //assert(getIthCoefficient(i) == wc.getIthCoefficient(i));
    //assert(getIthLiteral(i)     == wc.getIthLiteral(i));
  //}
}

inline PBConstraint::~PBConstraint () {}

// size[-1], rhs[-2], watchIdx[-3], numBackjump[-4], activity[-5], isInit[-6], LBD[-7], capacity[-8]

inline int PBConstraint::getSize ( )     const {return longPointer()[-1]; }
inline int PBConstraint::getNumInts ( )     const { return 8 + 2*getSize();}
inline int PBConstraint::getConstant ( ) const { return longPointer()[-2];}
inline int PBConstraint::getCoefficient (int var) const {
  // coeff that goes with var or -var
  assert(var > 0);
  int* longPtr = longPointer();
  for (int i = 1; i < 2*getSize(); i+=2) {
    if (abs(longPtr[i]) == var) return longPtr[i-1];
  }
  return 0;
}

inline int PBConstraint::getLiteral (int var) const { 
  // return var, -var or zero
  assert(var > 0);
  int* longPtr = longPointer();
  for (int i = 1; i < 2*getSize(); i+=2) {
    if (abs(longPtr[i]) == var) return longPtr[i];
  }
  return 0;
}

inline int PBConstraint::getIthLiteral (int i) const {
  assert(i < getSize() and i >= 0);
  return longPointer()[2*i + 1];
}

inline int PBConstraint::getIthCoefficient (int i) const {
  assert(i < getSize() and i >= 0); 
  return longPointer()[2*i];
}

// size[-1], rhs[-2], watchIdx[-3], numBackjump[-4], activity[-5], isInit[-6], LBD[-7], capacity[-8]

inline int  PBConstraint::getActivity ( ) const         { return longPointer()[-5];}
inline void PBConstraint::setActivity (int a)           { longPointer()[-5] = a;}
inline void PBConstraint::increaseActivity (int amount) { longPointer()[-5] += amount;}
inline bool PBConstraint::isInitial ( )   const         { return longPointer()[-6];}
inline void PBConstraint::setInitial(bool b)            { longPointer()[-6] = b;}
inline int  PBConstraint::getLBD (     )   const        { return longPointer()[-7];}
inline void PBConstraint::setLBD (int lbd)              { longPointer()[-7] = lbd;}

inline int  PBConstraint::getMaxWIdx ( )   const        { return longPointer()[-3];}
inline void PBConstraint::setMaxWIdx (int i)            { longPointer()[-3] = i;}
inline int PBConstraint::getNumBackjump ( ) const       { return longPointer()[-4];}
inline void PBConstraint::setNumBackjump (int nc)       { longPointer()[-4] = nc;  }

inline bool PBConstraint::isIthLitWatched (int i) const { 
  assert(i < getSize() and i >= 0); 
  return (longPointer()[2*i] < 0);
}
inline void PBConstraint::setIthLitWatched (int i, bool w) { 
  assert(i < getSize() and i >= 0); 
  assert(isIthLitWatched(i) != w);
  int* longPtr = longPointer();
  longPtr[2*i] = -(longPtr[2*i]);
  assert(isIthLitWatched(i) == w);
}

inline int PBConstraint::maxCoefOfConstraint( ) const {
  return ::maxCoefOfConstraint(*this);
}

inline void PBConstraint::simplify() {
  ::simplify(*this);
}

inline void PBConstraint::freeMemory ( ) {
  if (ptr != 0) {
    int* longPtr = longPointer();
    MemoryManager::getMemoryManager()->free(ptr,longPtr[-8]);
    ptr = 0;
  }
}

inline int* PBConstraint::longPointer() const {
  assert(ptr);
  return MemoryManager::getMemoryManager()->shortPtrToLongPointer(ptr) + 8;
}


#endif /* INC_PBCONSTRAINT_H */
