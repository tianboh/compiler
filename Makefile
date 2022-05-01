all: c0c

c0c: ../bin/c0c
../bin/c0c: always
	dune build
	mkdir -p ../bin
	install _build/default/bin/c0c.exe $@

always:

clean:
	dune clean


.PHONY: c0c clean native
