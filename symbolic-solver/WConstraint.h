#ifndef INC_WCONSTRAINT_H
#define INC_WCONSTRAINT_H

#pragma once

#include <vector>
#include <string>
#include <cassert>
#include <algorithm>
#include <iostream>
#include "Constraint.h"

using namespace std;

class PBConstraint;
class Cardinality;
class Clause;
class Model;

class WConstraint {

  vector<pair<int,int> > lhs; // pairs are <coeff,lit> with coeff > 0
  int rhs;                    // constraint is lhs >= rhs
  pair<int,int> rhs_ind;
  pair<int,int> rhs_obj;
  bool shaved;
  
 public:

  // posCoeffs[i] > 0 and r >= 0
  // creates posCoeffs*lits >= r
  WConstraint (const vector<int>& posCoeffs, const vector<int>& lits, int r, const pair<int,int>& rhs_indep, const pair<int,int>& rhs_object, bool shav);
  //WConstraint (const vector<int>& posCoeffs, const vector<int>& lits, int r, const rational<int>& rhs_indep, const rational<int>& rhs_object, bool shav);

  // b ==> creates tautology 0 >= 0, not(b) ==> creates contradiction 0 >= 1
  WConstraint (bool b = true);

  // pairs are <coeff,lit> with coef > 0 and r >= 0
  // creates l >= r
  WConstraint(const vector<pair<int,int> >& l, int r, const pair<int,int>& rhs_indep, const pair<int,int>& rhs_object, bool shav);

  WConstraint (const PBConstraint& pc);
  
  WConstraint (const Cardinality& c);

  WConstraint (const Clause& c);

  int  getSize           ( ) const;  // return number of variables
  int  getNumInts        ( ) const;
  int  getConstant       ( ) const;
  void setConstant       ( int c ); // c >= 0
  void clearLHS          ( );
  void reset             ( );
  void setLHS            ( const vector<pair<int,int>>& l );
  
  bool  isShaved         ( ) const; 
  void  setShaved        (bool s); 


  void setIndependentRHS (int num_ind, int den_ind);
  void setObjectiveRHS   (int num_obj, int den_obj);
  rational<int> getIndependentRHS ( ) const ;
  rational<int> getObjectiveRHS ( ) const ;
  int getIndependentRHSNum ( ) const;
  int getIndependentRHSDen ( ) const;
  int getObjectiveRHSNum ( ) const;
  int getObjectiveRHSDen ( ) const;

  void setIndependentRHS (const pair<int,int>& r);
  void setObjectiveRHS (const pair<int,int>& r);
  void setIndependentRHS (const rational<int>& r);
  void setObjectiveRHS (const rational<int>& r);
  void setIndependentRHSNum (int a);
  void setIndependentRHSDen (int a);
  void setObjectiveRHSNum   (int a);
  void setObjectiveRHSDen   (int a);

  pair<int,int> getCoefficientLiteral(int var) const;
  int  getCoefficient    (int var) const; // coeff that goes with var or -var
  int  getLiteral        (int var) const; // return var, -var or zero
  
  pair<int,int> getCoefficientLiteralBinarySearch (int var) const;
  int  getCoefficientBinarySearch (int var) const; // coeff that goes with var or -var
  int  getLiteralBinarySearch(int var) const; // return var, -var or zero
  
  int  getIthLiteral     (int i) const; // 0 <= i < getSize()
  int  getIthCoefficient (int i) const; // 0 <= i < getSize()
  void setIthLiteral     (int i, int lit); // 0 <= i < getSize()
  void setIthCoefficient (int i, int coeff); // 0 <= i < getSize()
  void addMonomial       (int coeff, int lit); // coeff > 0, var(lit) not in the constraint
  

  void sortByIncreasingCoefficient     ();
  void sortByDecreasingCoefficient     ();
  void sortByIncreasingVariable        ();
         void sortByModel                     (const Model& m);
  bool isOrderedByIncreasingVariable   ( ) const;
  bool isOrderedByDecreasingCoefficient ( ) const;

  void removeDuplicates ( ); // assumes ordered by increasing variable
  bool isClause ( ) const;
  bool isCardinality ( ) const;

  void simplify ( );
  friend ostream& operator<<(ostream& os, const WConstraint& wc);
 private:

  int  getCoefficientBinarySearch (int var, int l, int r) const; // coeff that goes with var or -var
  pair<int,int> getCoefficientLiteralBinarySearch (int var, int l, int r) const;
  // For debugging
  bool coeffsStrictlyPositive(const vector<pair<int,int> >& l) const;
  
  int  maxCoefOfConstraint ( ) const;

};

#include "PBConstraint.h"
#include "Cardinality.h"
#include "Clause.h"
#include "Model.h"


inline WConstraint::WConstraint (const vector<int>& posCoeffs, const vector<int>& lits, int r, const pair<int,int>& rhs_indep, const pair<int,int>& rhs_object, bool shav)
  : rhs(r), rhs_ind(rhs_indep), rhs_obj(rhs_object), shaved(shav) { 
  assert(posCoeffs.size() == lits.size());
  assert(r >= 0);
  
  for (uint i = 0; i < posCoeffs.size(); ++i) {
    assert(posCoeffs[i] > 0);
    lhs.push_back({posCoeffs[i],lits[i]});
  }
}

inline WConstraint::WConstraint (bool b) : rhs(not b) {
  rhs_ind = {not b,1};
  rhs_obj = {0,1};
  shaved = false;
}

inline void WConstraint::reset () {
  rhs_ind = {0,1};
  rhs_obj = {0,1};
  lhs.clear();
  rhs = 0;
  shaved = false;
}

inline WConstraint::WConstraint(const vector<pair<int,int> >& l, int r, const pair<int,int>& rhs_indep, const pair<int,int>& rhs_object, bool shav) : lhs(l), rhs(r), rhs_ind(rhs_indep), rhs_obj(rhs_object), shaved(shav) {
  assert(coeffsStrictlyPositive(l));
  assert(r >= 0);
}

inline WConstraint::WConstraint(const PBConstraint& pc) {
  for (int i = 0; i < pc.getSize(); ++i) 
    lhs.push_back({abs(pc.getIthCoefficient(i)),pc.getIthLiteral(i)});
  rhs = pc.getConstant();
  setIndependentRHS(pc.getIndependentRHS());
  setObjectiveRHS(pc.getObjectiveRHS());
  shaved = false;
}  

inline WConstraint::WConstraint (const Cardinality& c) {
  for (int i = 0; i < c.getSize(); ++i) 
    lhs.push_back({1,c.getIthLiteral(i)});
  rhs = c.getDegree();
  setIndependentRHS(c.getIndependentRHS());
  setObjectiveRHS(c.getObjectiveRHS());
  shaved = false;
}

inline WConstraint::WConstraint (const Clause& c) {
  for (int i = 0; i < c.getSize(); ++i) 
    lhs.push_back({1,c.getIthLiteral(i)});
  rhs = 1;
  rhs_ind = {1,1};
  rhs_obj = {0,1};  
  shaved = false;
}

inline int WConstraint::getNumInts ( ) const {
  return 5 + 2*getSize();
}

inline int WConstraint::getSize( ) const {  // return number of variables
  return lhs.size();
}
  
inline int WConstraint::getConstant ( ) const {
  return rhs;
}

inline void WConstraint::setConstant ( int c ) { // c >= 0
  assert(c >= 0);
  rhs = c;
}

inline void WConstraint::setShaved ( bool s ) {
  shaved = s;
}
inline bool WConstraint::isShaved ( ) const {
  return shaved;
}

inline void WConstraint::clearLHS ( ) {
  lhs.clear();
}
inline void WConstraint::setLHS ( const vector<pair<int,int>>& l ) {
  assert(l.size() > 0);
  lhs = l;
}

inline pair<int,int> WConstraint::getCoefficientLiteral (int var) const {
  assert(var > 0);
  for (uint i = 0; i < lhs.size(); ++i)
    if (abs(lhs[i].second) == var) return lhs[i];
  return {0, 0};
}

inline int WConstraint::getCoefficient (int var) const { // coeff that goes with var or -var
  return getCoefficientLiteral(var).first;
}

inline int WConstraint::getLiteral (int var) const { // return var, -var or zero
  return getCoefficientLiteral(var).second;
}

inline pair<int,int> WConstraint::getCoefficientLiteralBinarySearch (int var) const {
  assert(var > 0);
  assert(isOrderedByIncreasingVariable());
  int l = 0;
  int r = lhs.size()-1;
  while (l <= r) {
    int m = (l+r)/2;
    int a = abs(lhs[m].second);
    if      (a < var) l = m+1;
    else if (a > var) r = m-1;
    else return lhs[m];
  }
  return {0,0};
}

inline int WConstraint::getCoefficientBinarySearch (int var) const {
  return getCoefficientLiteralBinarySearch(var).first;
}

inline int WConstraint::getLiteralBinarySearch (int var) const {
  return getCoefficientLiteralBinarySearch(var).second;
}


inline int WConstraint::getIthLiteral(int i) const { // 0 <= i < getSize()
  assert( 0 <= i and i < getSize());
  return lhs[i].second;
}

inline int WConstraint::getIthCoefficient(int i) const { // 0 <= i < getSize()
  assert( 0 <= i and i < getSize());
  return lhs[i].first;
}

inline void WConstraint::setIthLiteral(int i, int lit) { // 0 <= i < getSize()
  assert( 0 <= i and i < getSize());
  lhs[i].second = lit;
}

inline void WConstraint::setIthCoefficient(int i, int coeff) { // 0 <= i < getSize()
  assert( 0 <= i and i < getSize());
  assert(coeff > 0);
  lhs[i].first = coeff;
} 

inline void WConstraint::addMonomial (int coeff, int lit) { // coeff > 0, var(lit) not in the constraint
  assert(getCoefficient(abs(lit)) == 0);
  assert(coeff > 0);
  lhs.push_back({coeff,lit});
}

inline void WConstraint::sortByIncreasingCoefficient() {
  sort( lhs.begin(), lhs.end(),
         [](const pair<int,int> & m1, const pair<int,int> & m2) { return abs(m1.first) < abs(m2.first); } );
}

struct dec_coef_inc_var {
  bool operator () (pair<int,int> m1, pair<int,int> m2) const {
    return abs(m1.first) > abs(m2.first) || (abs(m1.first) == abs(m2.first) && abs(m1.second) < abs(m2.second));
  }
};

inline void WConstraint::sortByDecreasingCoefficient() {
  sort( lhs.begin(), lhs.end(),
         [](const pair<int,int> & m1, const pair<int,int> & m2) { return m1.first > m2.first; } );
}

inline void WConstraint::removeDuplicates ( ){
  assert(isOrderedByIncreasingVariable());
  uint i = 0;

  // This operation should take two rational numbers and add them
  // Also, we need an operation that, given a rational number, simplifies it (i.e. compute gcd of numerator
  // and denominator and divides both by the gcd).
  vector<pair<int,int> > newLhs;
  int newRhs = rhs;
  
  while (i < lhs.size()) {
    // Start block with new variable
    int v = abs(lhs[i].second);
    int posCoeffs = 0;
    int negCoeffs = 0;
    while (i < lhs.size() and abs(lhs[i].second) == v) {
      if (lhs[i].second > 0) posCoeffs += lhs[i].first;
      else                   negCoeffs += lhs[i].first;
      ++i;
    }
    // End block
    if (posCoeffs > negCoeffs) {
      newLhs.push_back({posCoeffs - negCoeffs, v});
      newRhs -= negCoeffs;
      setIndependentRHS(add_rational(getIndependentRHS(), rational<int>(-negCoeffs, 1)));
    }
    else if (posCoeffs < negCoeffs) {
      newLhs.push_back({negCoeffs - posCoeffs, -v});
      newRhs -= posCoeffs;
      setIndependentRHS(add_rational(getIndependentRHS(), rational<int>(-posCoeffs, 1)));
    }
    else {
      newRhs -= posCoeffs;
      setIndependentRHS(add_rational(getIndependentRHS(), rational<int>(-posCoeffs, 1)));
    }
  }
  
  assert(rhs == rhs_ind.first/rhs_ind.second);
  
  lhs = newLhs;
  rhs = newRhs;
}

inline void WConstraint::sortByIncreasingVariable() {
  sort( lhs.begin(), lhs.end(),
         [](const pair<int,int> & m1, const pair<int,int> & m2) {
    return abs(m1.second) < abs(m2.second);
  } );
}

inline bool WConstraint::isOrderedByIncreasingVariable ( ) const {
  return ::isOrderedByIncreasingVariable(lhs);
}

inline bool WConstraint::coeffsStrictlyPositive(const vector<pair<int,int> >& l) const {
  for (uint i = 0; i < l.size(); ++i) 
    if (l[i].first <= 0) return false;
  return true;
}

inline bool WConstraint::isClause ( ) const {
  if (getConstant() != 1) return false;
  for (int i = 0; i < getSize(); ++i) 
    if (getIthCoefficient(i) != 1) return false;
  return true;
}

inline bool WConstraint::isCardinality ( ) const {
  for (int i = 0; i < getSize(); ++i) 
    if (getIthCoefficient(i) != 1) return false;
  return true;
}

inline int WConstraint::maxCoefOfConstraint( ) const {
  return ::maxCoefOfConstraint(*this);
}

inline void WConstraint::simplify() {
  ::simplify(*this);
}

inline void WConstraint::setIndependentRHS (int num_ind, int den_ind) {rhs_ind = {num_ind,den_ind};}
inline void WConstraint::setObjectiveRHS (int num_obj, int den_obj) {rhs_obj = {num_obj,den_obj};}
inline void WConstraint::setIndependentRHS (const pair<int,int>& r) { rhs_ind = r;}
inline void WConstraint::setObjectiveRHS (const pair<int,int>& r) { rhs_obj = r;}
inline void WConstraint::setIndependentRHS (const rational<int>& r) { rhs_ind = {r.numerator(), r.denominator()};}
inline void WConstraint::setObjectiveRHS (const rational<int>& r) { rhs_obj = {r.numerator(), r.denominator()};}

inline int WConstraint::getIndependentRHSNum ( )        const {return rhs_ind.first;}
inline int WConstraint::getIndependentRHSDen ( )        const {return rhs_ind.second;}
inline int WConstraint::getObjectiveRHSNum ( )          const {return rhs_obj.first;}
inline int WConstraint::getObjectiveRHSDen ( )          const {return rhs_obj.second;}

inline void WConstraint::setIndependentRHSNum (int a) {rhs_ind.first  = a;}
inline void WConstraint::setIndependentRHSDen (int a) {rhs_ind.second = a;}
inline void WConstraint::setObjectiveRHSNum   (int a) {rhs_obj.first  = a;}
inline void WConstraint::setObjectiveRHSDen   (int a) {rhs_obj.second = a;}

inline rational<int> WConstraint::getIndependentRHS ( ) const  {return rational<int>(rhs_ind.first, rhs_ind.second);}
inline rational<int> WConstraint::getObjectiveRHS ( ) const    {return rational<int>(rhs_obj.first, rhs_obj.second);}

#endif
