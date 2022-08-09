all: c0c

c0c: ../bin/c0c
../bin/c0c: always
	dune build
	mkdir -p ../bin
	install ../_build/default/lab3/bin/c0c.exe $@
	cp ../bin/c0c bin/

always:

clean:
	dune clean
	rm ../bin
	rm bin/c0c


.PHONY: c0c clean native
