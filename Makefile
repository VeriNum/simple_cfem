OBJS=	fem1d.o \
	bandmat.o \
	assemble.o \
	gaussquad.o \
	shapes1d.o

all: tests.x 

%.o: %.c
	gcc -Wall -c $<

tests.x: tests.o $(OBJS)
	gcc -Wall -o $@ $^

test: tests.x
	./tests.x

clean:
	rm -f *.o *~ tests.x
