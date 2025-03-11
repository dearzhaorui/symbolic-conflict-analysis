CC              = g++
#CFLAGS          = -std=c++17 -pg -O3 -Wall
#CFLAGS          = -std=c++17 -O3 -g -D_GLIBCXX_DEBUG
#CFLAGS          = -std=c++17 -g -O3 -Wall -D_GLIBCXX_DEBUG #-DNDEBUG 
#CFLAGS          = -std=c++17 -g -pg -O3 -Wall -DNDEBUG 
#CFLAGS          = -std=c++17 -g -O0 -fno-inline -Wall -D_GLIBCXX_DEBUG
#the following is for valgrind --leak-check=yes intsat c.lp
#CFLAGS          = -g -O0 -Wall

# use a gcc version >= c++17
CFLAGS          = -std=c++17 -O3 -Wall -static -DNDEBUG


SRCS = 	main.cpp \
	PBConstraint.cpp \
	WConstraint.cpp \
	Model.cpp \
	MaxHeap.cpp \
	Solver.cpp

OBJS = $(addsuffix .o, $(basename $(SRCS) .cpp))

all: pbsat #mydiff

pbsat: $(OBJS)
	$(CC) $(CFLAGS) $(OBJS) -o pbsat

mydiff: mydiff.cpp
	$(CC) $(CFLAGS) mydiff.cpp -o mydiff

%.o: %.cpp
	$(CC) $(CFLAGS) -c $*.cpp

clean:
	rm -f *.o intsatSolution.lp intsatSolution.pl 

depend:
	makedepend -Y $(SRCS)


# DO NOT DELETE

main.o: MaxHeap.h Model.h Reason.h Clause.h WConstraint.h
main.o: Constraint.h Functions.h PBConstraint.h Strategy.h Statistics.h
main.o: Solver.h OccurListVector.h
PBConstraint.o: Functions.h PBConstraint.h Constraint.h WConstraint.h
PBConstraint.o: Clause.h Model.h Reason.h
WConstraint.o: WConstraint.h Constraint.h Functions.h PBConstraint.h Clause.h
WConstraint.o: Model.h Reason.h
Model.o: Model.h Reason.h Clause.h WConstraint.h Constraint.h
Model.o: Functions.h PBConstraint.h
MaxHeap.o: MaxHeap.h
Solver.o: Solver.h PBConstraint.h Constraint.h Functions.h WConstraint.h
Solver.o: Clause.h Model.h Reason.h Strategy.h Statistics.h
Solver.o: MaxHeap.h OccurListVector.h
