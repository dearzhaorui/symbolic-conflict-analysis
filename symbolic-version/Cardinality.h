#ifndef INC_Cardinality_H
#define INC_Cardinality_H

#include <vector>
#include <iostream>
#include <iterator>

using namespace std;

class WConstraint;

class Cardinality {

  int* mem;
  // ind_rhs_den[-8] (denominator of the independent term of the rhs)
  // ind_rhs_num[-7] (numerator of the independent term of the rhs)
  // obj_rhs_den[-6] (denominator of the objective term of the rhs)
  // obj_rhs_num[-5] (numerator of the objective term of the rhs)  
  // size[-1], rhs[-2], watchIdx[-3], numBackjump[-4], 
  // activity[-9], isInit[-10], LBD[-11]
  
 public:

  //class iterator : public std::iterator<std::forward_iterator_tag,int*> {

    //int *itr;

  //public:
    //iterator (int* temp) : itr(temp) {}
    //iterator (const iterator& myitr) : itr(myitr.itr) {}
    //iterator& operator++()    {itr++; return *this;}//Pre-increment
    //iterator  operator++(int) {iterator tmp(*this); itr++; return tmp;}//Post-increment
    //bool operator== (const iterator& rhs) const {return itr == rhs.itr;}
    //bool operator!= (const iterator& rhs) const {return itr != rhs.itr;}
    //int& operator* () {return *itr;}
    //int* operator->() {return  itr;}    
  //};
  
  class iterator {
    int *itr;
    
    public:
      using iterator_category = std::forward_iterator_tag;
      using value_type = int;
      using difference_type = int;
      using pointer = int*;
      using reference = int&;
      
      iterator (int* temp) : itr(temp) {}
      iterator (const iterator& myitr) : itr(myitr.itr) {}
      iterator& operator++()    {itr++; return *this;}//Pre-increment
      iterator  operator++(int) {iterator tmp(*this); itr++; return tmp;}//Post-increment
      bool operator== (const iterator& rhs) const {return itr == rhs.itr;}
      bool operator!= (const iterator& rhs) const {return itr != rhs.itr;}
      int& operator* () {return *itr;}
      int* operator->() {return  itr;}    
  };

  inline Cardinality ( );
  inline Cardinality (const Cardinality& card); // quick, pointer copy
  inline Cardinality (const vector<int>& lits, int rhs, bool isInit, int activity, int LBD, int num_ind, int den_ind, int num_obj, int den_obj); // two first lits will be watched
  inline Cardinality (const vector<int>& lits, int rhs, bool isInit, int activity, int LBD, const pair<int,int>& indep_rhs, const pair<int,int>& object_rhs); // two first lits will be watched
  inline Cardinality (const WConstraint& wc,   bool isInit, int activity, int LBD); // two first lits will be watched
  
  inline ~Cardinality() {}
  
  inline void freeMemory        ( );
  inline int  getSize           ( )       const { assert(mem); return mem[-1]; }
  inline void setSize           (int size)      { assert(mem); mem[-1] = size; }
  inline int  getIthLiteral     (int i)   const { assert(i >= 0 and i < getSize()); return mem[i]; }  // 0 <= i < getSize()
  inline void setIthLiteral     (int i, int lit){ assert(i >= 0 and i < getSize()); mem[i] = lit; }  // 0 <= i < getSize()
  inline int  getDegree         (     )   const { return mem[-2];}
  inline void setDegree         (int c)         { mem[-2] = c;}
  inline int  getActivity       (     )   const { return mem[-9];}
  inline void setActivity       (int a)         { mem[-9] = a;}
  inline void increaseActivity  (int amount)    { mem[-9] += amount;}
  inline bool isInitial         (     )   const { return mem[-10];}
  inline void setInitial        (bool i)        { mem[-10] = i;}
  inline int  getLBD            (     )   const { return mem[-11];}
  inline void setLBD            (int LBD)       { mem[-11] = LBD;}
  inline int  getNumInts        (     )   const { return getSize() + INTS_MEM;}
  
  inline int  getWatchIdx       (     )   const { return mem[-3];}
  inline void setWatchIdx       (int idx)       { mem[-3] = idx;}
  inline int  getNumBackjump    (     )   const { return mem[-4];}
  inline void setNumBackjump    (int n)         { mem[-4] = n;}


  inline void setIndependentRHS (int num_ind, int den_ind);
  inline void setObjectiveRHS   (int num_obj, int den_obj);
  //inline void setIndependentRHS (const pair<int, int>& r);
  //inline void setObjectiveRHS   (const pair<int, int>& r);
  void setIndependentRHS (const rational<int>& r);
  void setObjectiveRHS   (const rational<int>& r);
  inline void setIndependentRHS (const pair<int, int>& r);
  inline void setObjectiveRHS   (const pair<int, int>& r);
  //inline pair<int,int> getIndependentRHS ( ) const;
  //inline pair<int,int> getObjectiveRHS ( ) const;
  rational<int> getIndependentRHS ( ) const;
  rational<int> getObjectiveRHS ( ) const;
  
  inline int getIndependentRHSNum ( ) const;
  inline int getIndependentRHSDen ( ) const;
  inline int getObjectiveRHSNum   ( ) const;
  inline int getObjectiveRHSDen   ( ) const;
  inline void setIndependentRHSNum (int a);
  inline void setIndependentRHSDen (int a);
  inline void setObjectiveRHSNum   (int a);
  inline void setObjectiveRHSDen   (int a);
  
  inline iterator begin() const {return mem;}
  inline iterator end()   const {return mem + mem[-1];}

  inline friend ostream& operator<<(ostream& os, const Cardinality& c) {
    for (auto& e:c) os << e << " ";
    os << "  >= " << c.getDegree() << " [ " << c.getIndependentRHSNum() << "/" << c.getIndependentRHSDen() << " + " << c.getObjectiveRHSNum() << "/" << c.getObjectiveRHSDen() << ", isInitial " << c.isInitial() << ", LBD " << c.getLBD() << ", size " << c.getSize() << " ]";
    return os;
  }  

  inline Cardinality operator= (const Cardinality& c) { mem = c.mem; return *this;}
 private:
  inline int* longPointer() const;
};

#include "WConstraint.h"

inline Cardinality::Cardinality ( ) {}

inline Cardinality::Cardinality (const Cardinality& c) {
  assert(c.mem != 0);
  mem = c.mem;
}

inline Cardinality::Cardinality (const vector<int>& lits, int rhs, bool isInit, int activity, int LBD, int num_ind, int den_ind, int num_obj, int den_obj) {
  mem = new int[lits.size()+INTS_MEM];
  mem += INTS_MEM;
  
  setSize((int)lits.size());
  setDegree(rhs);
  setWatchIdx(rhs+1);
  setNumBackjump(0);
  setActivity(activity);
  setInitial(isInit);
  setLBD(LBD);
  setIndependentRHS(num_ind,den_ind);
  setObjectiveRHS(num_obj,den_obj);
  
  for (uint i = 0; i < lits.size(); ++i) mem[i] = lits[i];
}

inline Cardinality::Cardinality (const vector<int>& lits, int rhs, bool isInit, int activity, int LBD, const pair<int,int>& indep_rhs, const pair<int,int>& object_rhs) : Cardinality(lits,rhs,isInit,activity,LBD,indep_rhs.first,indep_rhs.second,object_rhs.first,object_rhs.second) {}

inline Cardinality::Cardinality (const WConstraint& wc, bool isInit, int activity, int LBD) { // two first lits will be watched
  assert(wc.isCardinality());
  vector<int> lits;
  for (int i = 0; i < wc.getSize(); ++i) lits.push_back(wc.getIthLiteral(i));
  *this = Cardinality(lits, wc.getConstant(),isInit,activity,LBD, wc.getIndependentRHSNum(),wc.getIndependentRHSDen(), wc.getObjectiveRHSNum(),wc.getObjectiveRHSDen());
}

inline void Cardinality::setIndependentRHS (int num_ind, int den_ind) {
  mem[-7] = num_ind;
  mem[-8] = den_ind;
}

inline void Cardinality::setIndependentRHS (const pair<int,int>& r) {
  mem[-7] = r.first;
  mem[-8] = r.second;
}

inline void Cardinality::setObjectiveRHS (int num_obj, int den_obj) {
  mem[-5] = num_obj;
  mem[-6] = den_obj;
}

inline void Cardinality::setObjectiveRHS (const pair<int,int>& r) {
  mem[-5] = r.first;
  mem[-6] = r.second;
}

inline void Cardinality::setIndependentRHS (const rational<int>& r) {
  mem[-7] = r.numerator();
  mem[-8] = r.denominator();
}
inline void Cardinality::setObjectiveRHS (const rational<int>& r) {
  mem[-5] = r.numerator();
  mem[-6] = r.denominator();
}
inline int Cardinality::getIndependentRHSNum ( ) const {assert(mem); return mem[-7];}
inline int Cardinality::getIndependentRHSDen ( ) const  {assert(mem); return mem[-8];}
inline int Cardinality::getObjectiveRHSNum ( ) const {assert(mem); return mem[-5];}
inline int Cardinality::getObjectiveRHSDen ( ) const {assert(mem); return mem[-6];}

inline void Cardinality::setIndependentRHSNum (int a) {assert(mem); mem[-7]  = a;}
inline void Cardinality::setIndependentRHSDen (int a) {assert(mem); mem[-8]  = a;}
inline void Cardinality::setObjectiveRHSNum   (int a) {assert(mem); mem[-5] = a;}
inline void Cardinality::setObjectiveRHSDen   (int a) {assert(mem); mem[-6] = a;}

//inline pair<int,int> Cardinality::getIndependentRHS ( ) const {assert(mem); return {mem[-7],mem[-8]};}
//inline pair<int,int> Cardinality::getObjectiveRHS ( ) const {assert(mem); return {mem[-5],mem[-6]};}
inline rational<int> Cardinality::getIndependentRHS ( ) const {assert(mem); return rational<int>(mem[-7],mem[-8]);}
inline rational<int> Cardinality::getObjectiveRHS ( ) const {assert(mem); return rational<int>(mem[-5],mem[-6]);}

inline void Cardinality::freeMemory ( ) {
  if (mem) {
    mem -= INTS_MEM;
    delete[] mem;
  }
}


inline int* Cardinality::longPointer() const {
  assert(mem);
  return mem;
}

#endif
