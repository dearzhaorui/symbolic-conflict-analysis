#ifndef INC_FUNCTIONS_H
#define INC_FUNCTIONS_H

#pragma once

#include<cassert>
#include<climits>
#include<iostream>
#include <vector>
#include <numeric>

#include <boost/multiprecision/cpp_int.hpp>
//#if WITHGMP
//#include <boost/multiprecision/gmp.hpp>
//#endif  // WITHGMP

#include <boost/config.hpp>
#include <exception>
#include <boost/rational.hpp>
using namespace std;
using boost::rational;
using boost::rational_cast;

//#if WITHGMP
//using int128 = boost::multiprecision::int128_t;  // NOTE: a bit slower than __int128, but plays nice with mpz_int
//using bigint = boost::multiprecision::mpz_int;   // NOTE: requires GMP
//#else
using int128 = __int128;
using bigint = boost::multiprecision::cpp_int;
//#endif  // WITHGMP

#define TWOTOTHE30TH (long long)(1<<30)
#define TWOTOTHE31ST (((long long)(1))<<31)
#define debug 0
#define bdebug 0


inline std::ostream& operator<<(std::ostream& os, const __int128& x) {
  // Outputs an int128 as a string.
  if (x < 0) return os << "-" << -x;
  if (x < 10) return os << (char)(x + '0');
  return os << x / 10 << (char)(x % 10 + '0');
}

//string to_string(const __int128& x) {
  //string s = "";
  //if (x < 0) { s += "-"; s += to_string(-x); }
  //else if (x < 10) s += ((char)(x + '0'));
  //else {s += to_string(x / 10); s += ((char)(x % 10 + '0'));}
  //return s;
//}


template <typename T>
T abs(const T& x) {
  return std::abs(x);
}

template <>
inline int128 abs(const int128& x) {
  return x < 0 ? -x : x;
}

template <>
inline bigint abs(const bigint& x) {
  return boost::multiprecision::abs(x);
}
template <>
inline boost::multiprecision::int128_t abs(const boost::multiprecision::int128_t& x) {
  return boost::multiprecision::abs(x);
}

inline std::ostream& operator<<(std::ostream& os, const rational<int>& x) {
  return os << x.numerator() << "/" << x.denominator();
}
inline std::ostream& operator<<(std::ostream& os, const pair<int, int>& x) {
  return os << x.first << "/" << x.second;
}

//template<class T>
//T GCD(T a, T b) {
  //assert(a>=0); assert(b>=0);
  //if (b == 0) return a;
  //return GCD<T>( b, a%b );
//}

template<class T>
T GCD(T a, T b) {   // new
  assert(a>=0); assert(b>=0);
  return std::gcd(a, b);
}

template <typename T>
T lcm(const T& x, const T& y) {
  return std::lcm(x, y);
}

template<class T>
inline T divisionRoundedUp( T n, T c ) {
  assert( c>0 ); assert( n>=0 );
  T d = n / c;
  if ( d*c != n ) d = d+1;
  return(d);
}

inline int roundedUpDouble( double a ) {
#ifndef NDEBUG
long long int x = (long long)abs(a);
if (abs(x) > 2e9) {cout << "Possible overflow in roundedUpDouble(), a = " << a << endl; exit(1);}
#endif 

  return ceil(a);
}

inline int latest_rhs(const rational<int>& ind_rhs, const rational<int>& obj_rhs, int obj) {
  assert(ind_rhs.denominator() > 0);
  assert(obj_rhs.denominator() > 0);
  
  double symb_rhs = boost::rational_cast<double>(ind_rhs) + obj*boost::rational_cast<double>(obj_rhs);
  return roundedUpDouble(symb_rhs);
}

inline bool isOrdered(const vector<int>& v) {
  for (uint i = 1; i < v.size(); ++i) if (abs(v[i-1]) >= abs(v[i])) return false;
  return true;
}

// v is vector of <coeff,var>. Returns whether increasingly order by variable
inline bool isOrderedByIncreasingVariable(const vector<pair<int,int> >& v) {
  for (uint i = 1; i < v.size(); ++i) if (abs(v[i-1].second) >= abs(v[i].second)) return false;
  return true;
}


inline pair<int,int> simplify_rational (const pair<int,int>& a) {
  //if (a.second <= 0) {cout << "Possible overflow type G, a.second = " << a.second << ", a.first " << a.first << endl; exit(0);}
  assert(a.second > 0);
  int gcdV = GCD(abs(a.first), abs(a.second));
  return {a.first/gcdV, a.second/gcdV}; // compute GCD of num and den, and divide both of them
}

inline int sign_int (int a) { return (a > 0) - (a < 0); }

//inline rational<int> simplify_rational2 (const rational<int>& a) {
  //if (a.denominator() <= 0) {cout << "Possible overflow type G, a.second = " << a.denominator()  << ", a.first " << a.numerator() << endl; exit(0);}
  //assert(a.denominator() > 0);
  //int gcdV = GCD(abs(a.numerator()), a.denominator());
  //return a/gcdV; // compute GCD of num and den, and divide both of them
//}

/*
inline rational<int> add_rational (const rational<int>& a, const rational<int>& b) {
  assert(a.denominator() > 0);
  assert(b.denominator() > 0);

  #ifndef NDEBUG
    if (a.denominator() == b.denominator()) {
      long long int w = ((long long)(a.numerator()) + (long long)(b.numerator()));
      if (abs(w) > INT_MAX) {cout << "Possible overflow type E, we are adding " << (long long)(a.numerator()) << " " << b.numerator() << " den " << a.denominator() << endl; exit(1);}
    }
    else {
      long long int x = (long long)(a.denominator())*(long long)(b.denominator()); 
      if (x < 0  or abs(x) > INT_MAX) {cout << "Possible overflow type A" << endl; exit(1);}
      
      long long int y = ((long long)(a.numerator()) * (long long)(b.denominator())); 
      long long int z = ((long long)(b.numerator()) * (long long)(a.denominator())); 
      
      if (abs(y) > INT_MAX or abs(z) > INT_MAX or abs(z+y) > INT_MAX) {
        cout << "Possible overflow type C, b.denominator() = " << b.denominator() << ", y " << y << ", z " << z << ", z+y " << z+y << endl; 
        
        assert(b.denominator() == 1);  // it should because of removing units. it happens when only update RHS of PBs, no Cards. eg. 459*.lp
          int int_a = roundedUpDouble(boost::rational_cast<double>(a));
          int int_b = roundedUpDouble(boost::rational_cast<double>(b));
          if (abs((long long)int_a + (long long)int_b) > INT_MAX) {cout << "Possible overflow type F!" << endl; exit(0);}
          int v = int_a + int_b;
          
          int v2 = roundedUpDouble(boost::rational_cast<double>(a+b));
          
          if (v != v2) {
            cout << "Possible rational overflow 1, b.denominator() = " << b.denominator() << endl; 
            cout << "we should get v " << v << ", but rational v2 = " << v2 << ", cast = " << boost::rational_cast<double>(a+b) << endl;
            cout << "int_a = " << int_a << ", b.numerator() = " << b.numerator() << endl;
            exit(0);
          }
        
      }
      
    }
  #endif
  
  rational<int> v(0, 1);
  try {
    v = a+b;
  }
  catch (const boost::bad_rational &e) {
    cout << "Bad rational, as expected: " << e.what() << endl;
    exit(0);
  }
  catch (...) {
    cout << "Wrong exception raised!" << endl;
    exit(0);
  }
  return v;
}
*/

inline rational<int> add_rational (const rational<int>& a, const rational<int>& b) {
  assert(a.denominator() > 0);
  assert(b.denominator() > 0);

  #ifndef NDEBUG
    rational<long long> ra = static_cast<rational<long long>>(a);
    rational<long long> rb = static_cast<rational<long long>>(b);
    rational<long long> rc = ra + rb;
    if(abs(rc.numerator()) > INT_MAX or rc.denominator() < 0 or abs(rc.denominator()) > INT_MAX) {
      cout << "Possible overflow type E, we are adding a: " << a << " b: " << b << ", rc " << rc << endl; 
      exit(1);
    }
  #endif
  
  try {
    return a+b;
  }
  catch (const boost::bad_rational &e) {
    cout << "Bad rational, as expected: " << e.what() << endl;
    exit(0);
  }
  catch (...) {
    cout << "Wrong exception raised!" << endl;
    exit(0);
  }
  return 0;
}

#endif /* INC_FUNCTIONS_H */
