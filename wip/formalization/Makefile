all: Makefile.coq
	+make -f Makefile.coq all


Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq


clean:
	rm -f *~
	rm -f *.vo*
	rm -f *.glob
	rm -f */~
	rm -f */*.vo*
	rm -f */*.glob
	rm -f */.*.aux
	rm -f */*/*.vo*
	rm -f */*/*.glob
	rm -f */*/.*.aux
	rm -f .*.aux
	rm -f .*.d
	rm -f Makefile.coq
	rm -f Makefile.coq.conf


website: Makefile.coq
	+make -f Makefile.coq html
	mv html/*html website
	rm -rf html
