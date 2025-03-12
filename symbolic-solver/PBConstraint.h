#ifndef INC_PBCONSTRAINT_H
#define INC_PBCONSTRAINT_H

#include <vector>
#include <string>
#include <cassert>
#include <algorithm>
#include <iostream>
#include "Constraint.h"

class WConstraint;

using namespace std;

static const int INTS_MEM = 11;

class PBConstraint {
  int *mem;
  // ind_rhs_den[-8] (denominator of the independent term of the rhs)
  // ind_rhs_num[-7] (numerator of the independent term of the rhs)
  // obj_rhs_den[-6] (denominator of the objective term of the rhs)
  // obj_rhs_num[-5] (numerator of the objective term of the rhs)  
  // size[-1], rhs[-2], watchIdx[-3], numBackjump[-4], 
  // activity[-9], isInit[-10], LBD[-11]
  // mem[0] is <coeff1,x1,coeff2,x2,coeff3,x3,....>
  // mem[2*size()] starts number of propagations of every lit
  
 public:
  
  PBConstraint ( );
  PBConstraint (const PBConstraint& c);
  // PRE: lits are ordered by increasing variable, posCoeffs > 0, posCoeff.size() > 0,  r > 0, 
  PBConstraint (const vector<int>& posCoeffs, const vector<int>& lits, int r, bool isInit, int activity, int LBD, int num_ind, int den_ind, int num_obj, int den_obj);
  // PRE: in l, pairs are <coeff,lit> and are ordered by increasing variable
  // coeffs > 0, r > 0, l.size() > 0
  PBConstraint (const vector<pair<int,int> >& l, int r, bool isInit, int activity, int LBD, int num_ind, int den_ind, int num_obj, int den_obj);

  PBConstraint (const vector<int>& posCoeffs, const vector<int>& lits, int r, bool isInit, int activity, int LBD, const pair<int,int>& indep_rhs, const pair<int,int>& object_rhs);
  // PRE: in l, pairs are <coeff,lit> and are ordered by increasing variable
  // coeffs > 0, r > 0, l.size() > 0
  PBConstraint (const vector<pair<int,int> >& l, int r, bool isInit, int activity, int LBD, const pair<int,int>& indep_rhs, const pair<int,int>& object_rhs);

  
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
  
  void setShaved         (bool s);
  bool isShaved          (      )  const;


  void setIndependentRHS (int num_ind, int den_ind);
  void setObjectiveRHS   (int num_obj, int den_obj);
  void setIndependentRHS (const pair<int,int>& r);
  void setObjectiveRHS   (const pair<int,int>& r);
  void setIndependentRHS (const rational<int>& r);
  void setObjectiveRHS   (const rational<int>& r);
  
  int getIndependentRHSNum ( ) const;
  int getIndependentRHSDen ( ) const;
  int getObjectiveRHSNum   ( ) const;
  int getObjectiveRHSDen   ( ) const;
  void setIndependentRHSNum (int a);
  void setIndependentRHSDen (int a);
  void setObjectiveRHSNum   (int a);
  void setObjectiveRHSDen   (int a);
  //pair<int,int> getIndependentRHS ( ) const;
  //pair<int,int> getObjectiveRHS ( ) const;
  
  rational<int> getIndependentRHS ( ) const;
  rational<int> getObjectiveRHS ( ) const;

  
  bool isIthLitWatched         (int i)   const;
  void setIthLitWatched        (int i, bool w);
  int getMaxWIdx        (     )   const;  // optimization 1: the max idx of watched lits  
  void setMaxWIdx        (int i);  
  int getNumBackjump    (     )   const;  // optimization 1: check if there's already one backjump before propagating
  void setNumBackjump    (int i); 
  void setConstant (int co);
  
  int  maxCoefOfConstraint( ) const;
  void simplify ( );
  friend ostream& operator<<(ostream& os, const PBConstraint& pc);

 private:

  // We do not allow assignments
  PBConstraint operator= (const PBConstraint& c) {assert(false); return *this; }

  void setSize(int s)        { mem[-1] = s;}
  
  void setIthCoefficient (int i, int value) {
    assert(value > 0);
    assert(i < getSize() and i >= 0);
    mem[2*i] = value;
  }

  template <class Constraint>
  friend
  void simplify(Constraint& cons);
};

#include "WConstraint.h"

inline PBConstraint::PBConstraint (const PBConstraint& c) {
  assert(c.mem != 0);
  mem = c.mem;
}

inline PBConstraint::PBConstraint ( ){
  mem = 0;
}

inline PBConstraint::PBConstraint (const vector<int>& posCoeffs, const vector<int>& lits, int r, bool isInit, int activity, int LBD, const pair<int,int>& indep_rhs, const pair<int,int>& object_rhs) : PBConstraint(posCoeffs,lits,r,isInit,activity,LBD,indep_rhs.first,indep_rhs.second,object_rhs.first,object_rhs.second){}


inline PBConstraint::PBConstraint (const vector<pair<int,int> >& l, int r, bool isInit, int activity, int LBD, const pair<int,int>& indep_rhs, const pair<int,int>& object_rhs) : PBConstraint(l,r,isInit,activity,LBD,indep_rhs.first,indep_rhs.second,object_rhs.first,object_rhs.second) {}



// PRE: lits are ordered by increasing variable, posCoeffs > 0, posCoeff.size() > 0,  r > 0, 
inline PBConstraint::PBConstraint (const vector<int>& posCoeffs, const vector<int>& lits, int r, bool isInit, int activity, int LBD, int num_ind, int den_ind, int num_obj, int den_obj) {
  assert(isOrdered(lits));
  assert(posCoeffs.size() == lits.size());
  assert(posCoeffs.size() > 0);
  assert(r > 0);

  mem = new int[2*posCoeffs.size()+INTS_MEM];
  mem += INTS_MEM;
  
  setSize((int)posCoeffs.size());
  setConstant(r);
  setMaxWIdx(0);
  setNumBackjump(0);
  setActivity(activity);
  setInitial(isInit);
  setLBD(LBD);
  setIndependentRHS(num_ind,den_ind);
  setObjectiveRHS(num_obj,den_obj);
  
  for (uint i = 0; i < lits.size(); ++i) {
    assert(posCoeffs[i] > 0);
    mem[2*i] = posCoeffs[i];
    mem[2*i + 1] = lits[i];
  }
}


// PRE: in l, pairs are <coeff,lit> and are ordered by increasing variable
// coeffs > 0, r > 0, l.size() > 0
inline PBConstraint::PBConstraint (const vector<pair<int,int>>& l, int r, bool isInit, int activity, int LBD, int num_ind, int den_ind, int num_obj, int den_obj) {
  assert(l.size() > 0);
  assert(isOrderedByIncreasingVariable(l));
  assert(r > 0);
  
  mem = new int[2*l.size()+INTS_MEM];
  mem += INTS_MEM;
  
  setSize((int)l.size());
  setConstant(r);
  setMaxWIdx(0);
  setNumBackjump(0);
  setActivity(activity);
  setInitial(isInit);
  setLBD(LBD);
  setIndependentRHS(num_ind,den_ind);
  setObjectiveRHS(num_obj,den_obj);
  
  for (uint i = 0; i < l.size(); ++i) {
    assert(l[i].first > 0);
    mem[2*i] = l[i].first;
    mem[2*i + 1] = l[i].second;
  }
} 

// PRE: wc is ordered by increasing variable. wc is not a tautology or contradiction
inline PBConstraint::PBConstraint (const WConstraint& wc, const bool isInit, int activity, int LBD) {
  assert(wc.getSize() > 0);
  
  mem = new int[2*wc.getSize() + INTS_MEM];
  mem += INTS_MEM;

  setSize((int)wc.getSize());
  setConstant(wc.getConstant());
  setMaxWIdx(0);
  setNumBackjump(0);
  setActivity(activity);
  setInitial(isInit);
  setLBD(LBD);
  setIndependentRHS(wc.getIndependentRHSNum(),wc.getIndependentRHSDen());
  setObjectiveRHS(wc.getObjectiveRHSNum(),wc.getObjectiveRHSDen());
  
  for (int i = 0; i < wc.getSize(); ++i) {
    mem[2*i] = wc.getIthCoefficient(i);
    mem[2*i + 1] = wc.getIthLiteral(i);
  }
}

inline PBConstraint::~PBConstraint () {}

inline void PBConstraint::freeMemory ( ) {
  if (mem) {
    mem -= INTS_MEM;
    delete[] mem;
  }
}

inline void PBConstraint::setShaved ( bool s ) { // bot used
  return;
}
inline bool PBConstraint::isShaved ( ) const {  // not used
  return true;
}

inline int PBConstraint::getSize ( )     const { assert(mem); return mem[-1]; }
inline int PBConstraint::getNumInts ( )     const { return INTS_MEM + 2*getSize();}
inline int PBConstraint::getConstant ( ) const { assert(mem); return mem[-2];}
inline int PBConstraint::getCoefficient (int var) const {
  // coeff that goes with var or -var
  assert(var > 0);
  for (int i = 1; i < 2*getSize(); i+=2) {
    if (abs(mem[i]) == var) return mem[i-1];
  }
  return 0;
}

inline int PBConstraint::getLiteral (int var) const { 
  // return var, -var or zero
  assert(var > 0);
  for (int i = 1; i < 2*getSize(); i+=2) {
    if (abs(mem[i]) == var) return mem[i];
  }
  return 0;
}

inline int PBConstraint::getIthLiteral (int i) const {
  assert(i < getSize() and i >= 0);
  return mem[2*i + 1];
}

inline int PBConstraint::getIthCoefficient (int i) const {
  assert(i < getSize() and i >= 0); 
  return mem[2*i];
}
  
inline int  PBConstraint::getActivity ( ) const         { assert(mem); return mem[-9];}
inline void PBConstraint::setActivity (int a)           { assert(mem); mem[-9] = a;}
inline void PBConstraint::increaseActivity (int amount) { assert(mem); mem[-9] += amount;}
inline bool PBConstraint::isInitial ( )   const         { assert(mem); return mem[-10];}
inline void PBConstraint::setInitial(bool b)            { assert(mem); mem[-10] = b;}
inline int  PBConstraint::getLBD (     )   const        { assert(mem); return mem[-11];}
inline void PBConstraint::setLBD (int lbd)              { assert(mem); mem[-11] = lbd;}

inline int  PBConstraint::getMaxWIdx ( )   const        { assert(mem); return mem[-3];}
inline void PBConstraint::setMaxWIdx (int i)            { assert(mem); mem[-3] = i;}
inline int  PBConstraint::getNumBackjump ( ) const       { assert(mem); return mem[-4];}
inline void PBConstraint::setNumBackjump (int nc)       { assert(mem); mem[-4] = nc;  }
inline void PBConstraint::setConstant (int co)          { assert(mem); mem[-2] = co;  }

inline bool PBConstraint::isIthLitWatched (int i) const { 
  assert(i < getSize() and i >= 0); 
  return (mem[2*i] < 0);
}

inline void PBConstraint::setIthLitWatched (int i, bool w) { 
  assert(i < getSize() and i >= 0); 
  assert(isIthLitWatched(i) != w);
  mem[2*i] = -(mem[2*i]);
}

inline void PBConstraint::setIndependentRHS (int num_ind, int den_ind) {
  mem[-7] = num_ind;
  mem[-8] = den_ind;
}

inline void PBConstraint::setIndependentRHS (const pair<int,int>& r) {
  mem[-7] = r.first;
  mem[-8] = r.second;
}


inline void PBConstraint::setObjectiveRHS (const pair<int,int>& r) {
  mem[-5] = r.first;
  mem[-6] = r.second;
}

inline void PBConstraint::setObjectiveRHS (int num_obj, int den_obj) {
  mem[-5] = num_obj;
  mem[-6] = den_obj;
}

inline void PBConstraint::setIndependentRHS (const rational<int>& r) {
  mem[-7] = r.numerator();
  mem[-8] = r.denominator();
}
inline void PBConstraint::setObjectiveRHS (const rational<int>& r) {
  mem[-5] = r.numerator();
  mem[-6] = r.denominator();
}

inline int PBConstraint::getIndependentRHSNum ( ) const {assert(mem); return mem[-7];}
inline int PBConstraint::getIndependentRHSDen ( ) const {assert(mem); return mem[-8];}
inline int PBConstraint::getObjectiveRHSNum ( )   const {assert(mem); return mem[-5];}
inline int PBConstraint::getObjectiveRHSDen ( )   const {assert(mem); return mem[-6];}

inline void PBConstraint::setIndependentRHSNum (int a) {assert(mem); mem[-7]  = a;}
inline void PBConstraint::setIndependentRHSDen (int a) {assert(mem); mem[-8]  = a;}
inline void PBConstraint::setObjectiveRHSNum   (int a) {assert(mem); mem[-5] = a;}
inline void PBConstraint::setObjectiveRHSDen   (int a) {assert(mem); mem[-6] = a;}
//inline pair<int,int> PBConstraint::getIndependentRHS ( ) const {assert(mem); return {mem[-7],mem[-8]};}
//inline pair<int,int> PBConstraint::getObjectiveRHS ( ) const {assert(mem); return {mem[-5],mem[-6]};}

inline rational<int> PBConstraint::getIndependentRHS ( ) const {assert(mem); return rational<int>(mem[-7],mem[-8]);}
inline rational<int> PBConstraint::getObjectiveRHS ( ) const {assert(mem); return rational<int>(mem[-5],mem[-6]);}

inline int PBConstraint::maxCoefOfConstraint( ) const {
  return ::maxCoefOfConstraint(*this);
}

inline void PBConstraint::simplify() {
  ::simplify(*this);
}

#endif /* INC_PBCONSTRAINT_H */
