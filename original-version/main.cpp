#include <stdlib.h>
#include <sstream>
#include <string.h>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <iostream>
#include <vector>
#include <assert.h>
#include <set>
#include <cfloat>
#include <fstream>
#include <algorithm>
#include <queue>
#include <signal.h>
#include <limits.h>

#include "MaxHeap.h"
#include "Model.h"
#include "WConstraint.h"
#include "Strategy.h"
#include "Functions.h"
#include "Solver.h"

using namespace std;

map<string, int> variables;
vector<string> varNames(1); // name for varNum 0, which is a non-used varNum
int nextVarID = 1;
vector<int> varNums, coeffs, objCoeffs;
vector<string> objVarNames;
bool minimizing = false;
vector<WConstraint> constraints;
vector<string> words; 
string tmp;  
int wordsIndex;
string varString;
int coef, sign;

char* inputReadCommandLineArg(int argc, char** argv, const char* name) 
// Retrieves a command line argument by its name
{
  int argIndex;
  char* argName;

  argIndex = 1;  // skip executable name
  while(argIndex < argc) {
    if ( argv[argIndex][0] != '-' )
      argIndex++;
    else {
      argName = &argv[argIndex][1];
      if (*argName=='-') argName++;   // allow --name
      if (strcmp(argName,name)==0) {  // found the sought arg
        if (string(name) == "help") return argName;
        argIndex++;
        if (argIndex < argc)
          return(argv[argIndex]);
        else
          return(NULL);
      }
      argIndex = argIndex + 2;
    }
  }
  return NULL;
}

vector<string> split (const string& s) {
  vector<string> vec;
  istringstream in(s);
  string str;
  while (in >> str)
    vec.push_back(str);
  return vec;
}

void getMonomial(){ // gets coef and varString from words and advances wordsIndex
  if      (words[wordsIndex] == "-") { sign = -1; wordsIndex++; }
  else if (words[wordsIndex] == "+") { sign =  1; wordsIndex++; }
  else     sign = 1;  // words[wordsIndex] is coeff of varname (no + or - sign; e.g., the first monomial)               
  if (wordsIndex+1 >= (int)words.size()   or words[wordsIndex+1] == "="
      or words[wordsIndex+1] == "<=" or words[wordsIndex+1] == ">=" 
      or words[wordsIndex+1] == "<"  or words[wordsIndex+1] == ">" 
      or words[wordsIndex+1] == "+"  or words[wordsIndex+1] == "-") {
    varString = words[wordsIndex];  // there is no coefficient and words[wordsIndex] is a variable name
    coef = sign;
    wordsIndex += 1;
  } else {  // words[wordsIndex] is a coefficient and words[wordsIndex+1] is the variable name
    varString = words[wordsIndex+1];
    coef = stoi(words[wordsIndex]) * sign;
    wordsIndex += 2;
  }
}

void getMonomialOPB() {
  string s = words[wordsIndex];
  assert(s.size() >= 2);
  
  long long int c = stoll(s.substr(1, s.length()-1), nullptr, 10);
  
  if (abs(c) >= INT_MAX) {cout << "input coef " << c << " is >= INT_MAX " << INT_MAX << ", int64? " << (abs(c) >= LLONG_MAX) << endl << endl; assert(false); exit(0);}
  
  coef = stoi(s.substr(1, s.length()-1));
  
  if      (s.substr(0,1) == "-") coef = -coef;
  else assert(s.substr(0,1) == "+");
  varString = words[wordsIndex+1];
  wordsIndex += 2;
}

//int getVarNum(string varStr) { // re-number the vars
  //int& n = variables[varStr];
  //if (n == 0) {
    //n = varNames.size();
    //varNames.push_back(varStr);
  //}
  //return n;
//}

int getVarNum(string varStr) { // keep using the original varStr num
  int& n = variables[varStr];
  string str = varStr.substr(1);
  assert(str[0] != '~');  // not in the form x~325
  if (n == 0) {
    n = stoi(str);
    assert(n > 0);
    varNames.push_back(varStr);
  }
  return n;
}
      
inline void addConstraintToDB(vector<int>& coefficients, vector<int>& literals, int rhs, bool isGeq) {
  if (not isGeq) rhs = -rhs;
  for (int i=0; i < (int)coeffs.size(); ++i) {
    if (not isGeq) coeffs[i] = -coeffs[i];
    int coef = abs(coeffs[i]);
    int lit  = varNums[i];
    if (coeffs[i]<0) { rhs+=coef; lit = -lit; }

    if (coef != 0) {
      coefficients.push_back(coef);
      literals.push_back(lit);
    }
  }
  if (rhs >= 1) {
    constraints.push_back(WConstraint(coefficients,literals,rhs));
  }
  coefficients.clear(); literals.clear();
}

void readLP(string filename) {  // warning: very naive lp format parser
  fstream input(filename.c_str(), fstream::in);
  if (not input) {cout << "Input file " << filename << " does not exist" << endl; exit(1);}
  int varNum=0;
  enum Modes { OBJECTIVE, CONSTRAINTS, BOUNDS, GENERALS, BINARIES, END  };
  Modes mode=END;
  while (!input.eof()) { // treat one line of input
    getline(input,tmp); 
    words = split(tmp);  
    wordsIndex = 0;
    if (tmp[0] == '*') continue;
    if (tmp[0] == '\\') continue;
    if (tmp == "") continue;
    if (tmp == "Minimize")   { mode = OBJECTIVE;   minimizing=true;  continue; }
    if (tmp == "Maximize")   { mode = OBJECTIVE;   minimizing=false; continue; }
    if (tmp == "Subject To") { mode = CONSTRAINTS; continue; }
    if (tmp == "Bounds")     { mode = BOUNDS;      continue; }
    if (tmp == "Binaries")   { mode = BINARIES;    continue; }
    if (tmp == "Generals")   { mode = GENERALS;    continue; }
    if (tmp == "End")        { mode = END;         continue; }
    if ( mode==BOUNDS or mode==BINARIES or mode==GENERALS or mode==END ) break; // exit while !input.eof()) loop
    if ( mode==OBJECTIVE ) {
      if (words.size()!=0) {
        if (words[0].substr(words[0].size()-1) == ":") wordsIndex++; // ignore label
        while (wordsIndex < (int)words.size()) { // keep adding monomials to the objective polynomial
          getMonomial();
          getVarNum(varString); 
          if (minimizing) objCoeffs.push_back(coef); else objCoeffs.push_back(-coef);
          objVarNames.push_back(varString);
        }
      }
    }
    if (mode==CONSTRAINTS) {
      vector<int> coefficients;
      vector<int> literals;
      int rhs;

      while (wordsIndex < (int)words.size()) {
        if (words[wordsIndex].substr(words[wordsIndex].size()-1) == ":") ++wordsIndex;
        if (words[wordsIndex] == "<" or words[wordsIndex] == ">") 
          { cout << "Error: strict inequality constraint " << tmp << endl; assert(false); }

        if (words[wordsIndex] == ">=") {
          rhs = stoi(words[wordsIndex+1]);
          addConstraintToDB(coefficients, literals, rhs, true);
          coeffs.clear(); varNums.clear();
          wordsIndex += 2;
          continue;
        }
        if (words[wordsIndex] == "<=") {
          rhs = stoi(words[wordsIndex+1]);
          addConstraintToDB(coefficients, literals, rhs, false);
          coeffs.clear(); varNums.clear();
          wordsIndex += 2;
          continue;
        }
        if (words[wordsIndex] == "=") {
          rhs = stoi(words[wordsIndex+1]);
          addConstraintToDB(coefficients, literals, rhs, true);
          addConstraintToDB(coefficients, literals, rhs, false);
          coeffs.clear(); varNums.clear();
          wordsIndex += 2;
          continue;
        }
        getMonomial();
        varNum = getVarNum(varString); 
        //cout << "1st " << varNum << "  , " << varNames.size()<< endl;
        //exit(0);
        if (coef == 0) { cout << "Error: zero or non-integer coefficient: " << tmp << endl; assert(false); }
        coeffs.push_back(coef);
        varNums.push_back(varNum);
      }
    }
  }
  input.close();
}

void readOPB(string filename) {  // warning: very naive lp format parser
  fstream input(filename.c_str(), fstream::in);
  if (not input) {cout << "Input file " << filename << " does not exist" << endl; exit(1);}
  int varNum=0;
  
  while (!input.eof()) { // treat one line of input
    getline(input,tmp);
    if (tmp[0] == '*') continue;
    if (tmp[0] == '\\') continue;
    if (tmp == "") continue; 
    words = split(tmp);  
    wordsIndex = 0;
    if (words[0] == "min:") {  
      minimizing = true;
      assert(tmp.substr(tmp.size()-1) == ";");
      wordsIndex++;
      while (wordsIndex < (int)words.size()) { // keep adding monomials to the objective polynomial
        getMonomialOPB();
        objCoeffs.push_back(coef);
        //if (minimizing) objCoeffs.push_back(coef); else objCoeffs.push_back(-coef);
        getVarNum(varString); 
        objVarNames.push_back(varString);
        if(words[wordsIndex] == ";") break;
      }
    }
    else if (words[0] == "max:") {
      cout << "objective is to maximize..." << endl;
      exit(0);
    }
    else {
      vector<int> coefficients;
      vector<int> literals;
      int rhs;
      assert(words[0].substr(words[0].size()-1) != ":");
      
      while (wordsIndex < (int)words.size()) {
        
        if (words[wordsIndex] == "<" or words[wordsIndex] == ">") 
          { cout << "Error: strict inequality constraint " << tmp << endl; assert(false); exit(0); }

        if (words[wordsIndex] == ">=") {
          rhs = stoi(words[wordsIndex+1]);
          addConstraintToDB(coefficients, literals, rhs, true);
          coeffs.clear(); varNums.clear();
          wordsIndex += 2;
          assert(words[wordsIndex] == ";");
          ++wordsIndex; assert(wordsIndex == (int)words.size());
          continue;
        }
        if (words[wordsIndex] == "<=") {
          rhs = stoi(words[wordsIndex+1]);
          addConstraintToDB(coefficients, literals, rhs, false);
          coeffs.clear(); varNums.clear();
          wordsIndex += 2;
          assert(words[wordsIndex] == ";");
          ++wordsIndex; assert(wordsIndex == (int)words.size());
          continue;
        }
        if(words[wordsIndex] == "=") {
          rhs = stoi(words[wordsIndex+1]);
          addConstraintToDB(coefficients, literals, rhs, true);
          addConstraintToDB(coefficients, literals, rhs, false);
          coeffs.clear(); varNums.clear();
          wordsIndex += 2;
          assert(words[wordsIndex] == ";");
          ++wordsIndex; assert(wordsIndex == (int)words.size());
          continue;
        }
        getMonomialOPB();
        varNum = getVarNum(varString);
        if (coef == 0) { cout << "Error: zero or non-integer coefficient: " << tmp << endl; assert(false); exit(0);}
        coeffs.push_back(coef);
        varNums.push_back(varNum);
      }
    }
  }
  input.close();
  
}


void showUsage(char* exec) {
  cout << exec << " [-help] [-seed int] [-tlimit int] [-id int] [-wperc double] [-card bool] [-prior bool] [-bt0 bool] [-multiobj bool] [-w executionInfo.txt] [-r executionInfo.txt] [-d decisionsLimit] [-c conflictsLimit] [-strategy file.txt] [-decision file.txt] [-iniSol file.txt]  *.lp/opb" << endl << endl;
  
  cout << "strategy --> specify the search strategies if it exists (default empty)" << endl;
  cout << "decision --> specify the decision literals if it exists (default empty)" << endl;
  cout << "iniSol   --> specify the initial solution if it exists  (default empty)" << endl;
  cout << "r        --> specify an input file to be read, and solver set readInfo to true." << endl;
  cout << "w        --> specify an output file to be wrote, and solver set writeInfo to true." << endl;
  cout << "id       --> (integer) the ID of solver" << endl;
  cout << "d        --> (integer) the decison limit" << endl;
  cout << "c        --> (integer) the conflict limit" << endl;
  cout << "seed     --> (integer) the seed used by solver for decision making" << endl;
  cout << "tlimit   --> (double)  the time limit 't' (t >= 0, 0:unlimited(default))" << endl;
  cout << "wperc    --> (double)  use watched propagation if the percentage of smallest number of watched literal \n                       is smaller than this percentage (0 <= x <= 1, default 0:only counting propagation, 1:only watched propagation)" << endl;
  cout << "card     --> (bool)    use cardinality constraints or not (default is true)" << endl;
  cout << "prior    --> (bool)    propagate different watch lists by priority or not (default is true)" << endl;
  cout << "bt0      --> (bool)    always backjump to decision level 0 when a new solution is found or not (default is true)" << endl;
  cout << "multiobj --> (bool)    always create a new objective constraint after a new solution is found or not (default is false)" << endl;
}

Solver* s;
clock_t beginTime;


void printFinalMessage (Solver::StatusSolver ans) {

  if      (ans == Solver::INFEASIBLE) cout << "RESULT: Infeasible" << endl;
  else if (ans == Solver::NO_SOLUTION_FOUND) cout << "RESULT: No_solution_found" << endl;
  else if (ans == Solver::SOME_SOLUTION_FOUND) cout << "RESULT: Some_solution_found" << endl;
  else if (ans == Solver::OPTIMUM_FOUND) cout << "RESULT: Optimum_found" << endl;
  else {cout << "Unexpected answer from solver." << endl; exit(1);}

  cout << "TIME:                  " << double(clock()-beginTime)/CLOCKS_PER_SEC << " s " << endl; 
  cout << "Process time:                  " << s->process_time() << endl;  
  cout << "Real    time:                  " << s->real_time() << endl;   
}

void finalMessage ( ){
  s->printStats(); cout << endl << endl;
  Solver::StatusSolver ans = s->currentStatus();
  printFinalMessage(ans);  
}

void terminateSolver(int sig){ // can be called asynchronously
  finalMessage();
  exit(1);
}

int main (int argc, char *argv[]) {  
  
  char* arg;
  if (argc <= 1) {
    showUsage(argv[0]);
    exit(0);
  }
  
  bool printUsage = false;
  arg = inputReadCommandLineArg(argc,argv,"help");
  if (arg) printUsage = true;
  if (printUsage) {
    showUsage(argv[0]);
    exit(0);
  }
  
  string stratFile = "";
  arg = inputReadCommandLineArg(argc,argv,"strategy");
  if (arg) stratFile = string(arg);

  string decisionFile = "";
  arg = inputReadCommandLineArg(argc,argv,"decision");
  if (arg) decisionFile = string(arg);

  string initialSolutionFile = "";
  arg = inputReadCommandLineArg(argc, argv, "iniSol");
  if (arg) initialSolutionFile = string(arg);

  int seed = 1;
  arg = inputReadCommandLineArg(argc,argv,"seed");
  if (arg) seed = atoi(arg);

  int tlimit = 0;
  arg = inputReadCommandLineArg(argc,argv,"tlimit");
  if (arg) tlimit = atoi(arg);

  int id = 0;
  arg = inputReadCommandLineArg(argc,argv,"id");
  if (arg) id = atoi(arg);
  
  int nDecs = INT_MAX;
  arg = inputReadCommandLineArg(argc,argv,"d");
  if (arg) nDecs = atoi(arg);
  
  int nConfs = INT_MAX;
  arg = inputReadCommandLineArg(argc,argv,"c");
  if (arg) nConfs = atoi(arg);
  
  string readInfoFile = "";
  arg = inputReadCommandLineArg(argc,argv,"r");
  if (arg) readInfoFile = string(arg);
  
  string writeInfoFile = "";
  arg = inputReadCommandLineArg(argc,argv,"w");
  if (arg) writeInfoFile = string(arg);
  
  double watchPercent = 0;
  arg = inputReadCommandLineArg(argc,argv,"wperc");
  if (arg) watchPercent = stod(arg);
  
  bool useCardinality = true;
  arg = inputReadCommandLineArg(argc,argv,"card");
  if (arg) useCardinality = (string(arg) == "false"? false: (atoi(arg)==0)? false: true);
  
  bool propagate_by_priority = true;
  arg = inputReadCommandLineArg(argc,argv,"prior");
  if (arg) propagate_by_priority = (string(arg) == "false"? false: (atoi(arg)==0)? false: true);
  
  bool bt0 = true;
  arg = inputReadCommandLineArg(argc,argv,"bt0");
  if (arg) bt0 = (string(arg) == "false"? false: (atoi(arg)==0)? false: true);
  
  bool multiObj = false;
  arg = inputReadCommandLineArg(argc,argv,"multiobj");
  if (arg) multiObj = (string(arg) == "false"? false: (atoi(arg)==0)? false: true);
  
  cout << "Time limit:                  " << tlimit << endl;
  cout << "Initial seed:                " << seed << endl;
  cout << "r/w log file?                " << (writeInfoFile != ""? "-w": readInfoFile != ""? "-r":"NO") << endl;
  cout << "Allowed watch percents?      " << watchPercent << endl;
  if(nDecs != INT_MAX) cout << "Decisions limit:        " << nDecs << endl;
  if(nConfs != INT_MAX) cout << "Conflicts limit:       " << nConfs << endl;
  
  srand ( seed );
  string filename = argv[argc-1];
  cout << endl << endl << "Input problem:  " <<  filename << endl << endl;
  
  if (filename.size() >= 3 and filename.substr(filename.size()-3) == ".lp")
    readLP(filename);
  else if (filename.size() >= 4 and filename.substr(filename.size()-4) == ".opb")
    readOPB(filename);
  else {cout << "This version of intsat only admits (very naive) .lp or .opb input format." << endl;    exit(1);}
  
  assert(objCoeffs.size() == objVarNames.size());
  assert(varNames.size()-1 == variables.size());
  
  int numVars = varNames.size() - 1;  // minus 1 because varNum 0 is not used
  int numConstraints = constraints.size();
  cout << "read "<< numVars << " variables in " << numConstraints << " constraints.   numVarsInOBJ " << objCoeffs.size() << endl;
  beginTime=clock();

  if (debug) {  cout << "create solver: " << endl;      }

  Solver solver(numVars,beginTime,minimizing,filename);
  s = &solver;
  signal(SIGINT, terminateSolver);
  solver.setId(id);
  solver.setWatchPercent(watchPercent);
  solver.setUseCardinality(useCardinality);
  solver.setBT0(bt0);
  solver.setMultipleObj(multiObj);
  solver.setPropagatebyPriority(propagate_by_priority);
  
  if(nDecs != INT_MAX) solver.setDecisionLimit(nDecs);
  if(nConfs != INT_MAX) solver.setConflictLimit(nConfs);
  
  if (debug) {  cout << "created " << endl;      }
  for (int varNum=1; varNum<=numVars; varNum++)
    solver.addVarName( varNum, varNames[varNum] );

  if (stratFile != "")           solver.readStrategy(stratFile);
  if (decisionFile != "")        solver.readDecision(decisionFile);
  if (initialSolutionFile != "") solver.readInitialSolution(initialSolutionFile);
  solver.checkInitialInputSolutionNeeded();
  
  ofstream* einfo = 0;
  if(writeInfoFile != "") {
    einfo = new ofstream(writeInfoFile);
    solver.setExecuteInfoFileStream(einfo);
    solver.setWriteInfo(true);
  }
  if (readInfoFile != "") {
    solver.setReadInfo(true);
  }
  
  cout << "took time " << double((clock() - beginTime)/CLOCKS_PER_SEC) << "s" << endl;
  
  if (debug) {  cout << "varnames added " << endl;      }

  for (int i = 0; i < (int)constraints.size(); i++) {
    constraints[i].sortByIncreasingVariable();
    constraints[i].removeDuplicates();
    constraints[i].sortByDecreasingCoefficient();
    solver.addAndPropagatePBConstraint(constraints[i],true,0,0); 
  }
  
  cout << "constraints added, took " << double((clock() - beginTime)/CLOCKS_PER_SEC) << "s" << endl;
  
  for (int i = 0; i < (int)objCoeffs.size(); ++i) {
    solver.addObjectiveMonomial( objCoeffs[i], getVarNum( objVarNames[i] ) ); 
  }
  
  if (debug) {  cout << " objective monomials addded" << endl;      }
  
  solver.solve(tlimit);
  
  uint64_t m = solver.maximum_resident_set_size ();
  cout << endl;
  printf("maximum resident set size of process:    %12.2f    MB", m/(double)(1l<<20));

  finalMessage();
  exit(0);
}
