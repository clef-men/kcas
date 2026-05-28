.PHONY : all
all : build

.PHONY : build
build :
	@ dune build

.PHONY : test
test :
	@ dune runtest

.PHONY : bench
bench :
	@ dune exec --release -- bench/main.exe -budget 1

.PHONY : top
top :
	@ dune utop .

.PHONY : clean
clean :
	@ dune clean
