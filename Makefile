all: tests.x 

%.o: %.c
	gcc -Wall -c $<

tests.x: tests.o cholesky.o band_assemble.o gaussquad.o shapes1d.o
	gcc -Wall -o $@ $^

test: tests.x
	./tests.x

clean:
	rm -f *.o *~ tests.x
