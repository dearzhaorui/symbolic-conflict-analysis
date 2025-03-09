#ifndef INC_Cardinality_H
#define INC_Cardinality_H

#include <vector>
#include <iostream>
#include <iterator>

using namespace std;

class WConstraint;

class Cardinality {

  int* mem;
  
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
  inline Cardinality (const vector<int>& lits, int rhs, bool isInit, int activity, int LBD); // two first lits will be watched
  inline Cardinality (const WConstraint& wc,   bool isInit, int activity, int LBD); // two first lits will be watched
  
  inline ~Cardinality() {}

  // size[-1], rhs[-2], watchIdx[-3], numBackjump[-4], activity[-5], isInit[-6], LBD[-7]

  //inline uint toUint      ( )       const {return 0;}

  inline void freeMemory        ( );
  inline int  getSize           ( )       const { assert(mem); return mem[-1]; }
  inline void setSize           (int size)      { assert(mem); mem[-1] = size; }
  inline int  getIthLiteral     (int i)   const { assert(i >= 0 and i < getSize()); return mem[i]; }  // 0 <= i < getSize()
  inline void setIthLiteral     (int i, int lit){ assert(i >= 0 and i < getSize()); mem[i] = lit; }  // 0 <= i < getSize()
  inline int  getDegree         (     )   const { return mem[-2];}
  inline void setDegree         (int c)         { mem[-2] = c;}
  inline int  getActivity       (     )   const { return mem[-5];}
  inline void setActivity       (int a)         { mem[-5] = a;}
  inline void increaseActivity  (int amount)    { mem[-5] += amount;}
  inline bool isInitial         (     )   const { return mem[-6];}
  inline void setInitial        (bool i)        { mem[-6] = i;}
  inline int  getLBD            (     )   const { return mem[-7];}
  inline void setLBD            (int LBD)       { mem[-7] = LBD;}
  inline int  getNumInts        (     )   const { return getSize() + INTS_MEM;}
  
  inline int  getWatchIdx       (     )   const { return mem[-3];}
  inline void setWatchIdx       (int idx)       { mem[-3] = idx;}
  inline int  getNumBackjump    (     )   const { return mem[-4];}
  inline void setNumBackjump    (int n)         { mem[-4] = n;}
  
  inline iterator begin() const {return mem;}
  inline iterator end()   const {return mem + mem[-1];}

  inline friend ostream& operator<<(ostream& os, const Cardinality& c) {
    for (auto& e:c) os << e << " ";
    os << "  [rhs = " << c.getDegree() << ", watchIdx " << c.getWatchIdx() << ", numBackjump " << c.getNumBackjump() << ", act " << c.getActivity() << ", isInitial " << c.isInitial() << ", LBD " << c.getLBD() << ", size " << c.getSize() << "]";
    return os;
  }  

  inline Cardinality operator= (const Cardinality& c) { mem = c.mem; return *this;}
 //private:
  inline int* longPointer() const;
};

#include "WConstraint.h"

inline Cardinality::Cardinality ( ) {}

inline Cardinality::Cardinality (const Cardinality& c) {
  assert(c.mem != 0);
  mem = c.mem;
}

inline Cardinality::Cardinality (const vector<int>& lits, int rhs, bool isInit, int activity, int LBD) {
  // size[-1], rhs[-2], watchIdx[-3], numBackjump[-4], activity[-5], isInit[-6], LBD[-7]
  mem = new int[lits.size()+7];
  mem += 7;
  
  setSize((int)lits.size());
  setDegree(rhs);
  setWatchIdx(rhs+1);
  setNumBackjump(0);
  setActivity(activity);
  setInitial(isInit);
  setLBD(LBD);
  
  for (uint i = 0; i < lits.size(); ++i) mem[i] = lits[i];
}

inline Cardinality::Cardinality (const WConstraint& wc, bool isInit, int activity, int LBD) { // two first lits will be watched
  assert(wc.isCardinality());
  vector<int> lits;
  for (int i = 0; i < wc.getSize(); ++i) lits.push_back(wc.getIthLiteral(i));
  *this = Cardinality(lits, wc.getConstant(),isInit,activity,LBD);
}

inline void Cardinality::freeMemory ( ) {
  if (mem) {
    mem -= 7;
    delete[] mem;
  }
}


inline int* Cardinality::longPointer() const {
  assert(mem);
  return mem;
}

#endif
