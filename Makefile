all: tests.x 

%.o: %.c
	gcc -Wall -c $<

tests.x: tests.o cholesky.o band_assemble.o
	gcc -Wall -o $@ $^

clean:
	rm -f *.o *~ tests.x
