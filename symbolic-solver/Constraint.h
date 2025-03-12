#ifndef INC_CONSTRAINT_H
#define INC_CONSTRAINT_H

#include <vector>
#include "Functions.h"

using namespace std;

template <class Constraint>
int maxCoefOfConstraint(const Constraint& cons) {
  int max = 0;
  for (int i = 0; i < cons.getSize(); ++i) { 
    int coef = cons.getIthCoefficient(i);
    if ( max < coef ) max=coef;
  }
  return max;
}

template <class Constraint>
void simplify(Constraint& cons) {
  assert (cons.getSize() > 0);
  int c = cons.getConstant();
  
  bool shaved = cons.isShaved();
  
  assert(cons.getObjectiveRHSNum() != 0 or (cons.getObjectiveRHSNum() == 0 and !shaved));
  int gcdV = 0; // compute gcd of coeffs < c, normalize coeffs > c
  for (int i = 0; i < cons.getSize(); ++i) {
    int coef = cons.getIthCoefficient(i);
    if (coef < c) 
      gcdV = GCD(gcdV, coef);
    else if (coef > c) {
      cons.setIthCoefficient(i, c);
      shaved = true;
    }
  }
  if (gcdV == 0) gcdV = c; // in this case all coefs are larger than or equal to the constant c

  cons.setConstant(divisionRoundedUp( c, gcdV ));
  
  //----------------
#ifndef NDEBUG
  rational<int> p;
  rational<int> indep_rhs = cons.getIndependentRHS();
  long long int x = (long long)(indep_rhs.denominator()) * gcdV;
  if (abs(x) > INT_MAX) {
    p = roundedUpDouble(rational_cast<double>(indep_rhs)/gcdV);
  }
  else {
    p = indep_rhs / gcdV;
  }
  cons.setIndependentRHS(p);
#else
  cons.setIndependentRHS(cons.getIndependentRHS()/gcdV);
#endif 
  

#ifndef NDEBUG
  rational<int> object_rhs = cons.getObjectiveRHS();
  x = (long long)(object_rhs.denominator()) * gcdV;
  if (abs(x) > INT_MAX) {
    p = roundedUpDouble((double)object_rhs.numerator()/x);
  }
  else {
    p = object_rhs / gcdV;
  }
  cons.setObjectiveRHS(p);
#else
  cons.setObjectiveRHS(cons.getObjectiveRHS()/gcdV);
#endif 
  //----------------
  
  for (int i = 0; i < cons.getSize(); ++i) 
    cons.setIthCoefficient(i, divisionRoundedUp(cons.getIthCoefficient(i), gcdV));
  
  if (cons.getObjectiveRHS().numerator() == 0) shaved = false; 
  cons.setShaved(shaved);
  
}

#endif
