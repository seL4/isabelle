OPTIONS= -DDEBUG
CC = g++ $(OPTIONS)
OBJS = qed.o

.SUFFIXES: .cc .o

.cc.o:
	$(CC) -c $<

qed:	$(OBJS)
	g++ -o qed $(OBJS)

qed.o: qed.cc
