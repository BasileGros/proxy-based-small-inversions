MAKEFILECOQ=Makefile.rocq
VERSION := $(shell grep depends small-inversions*opam | sed -e 's/.*{= .//' -e 's/"}//')
%: $(MAKEFILECOQ)

$(MAKEFILECOQ): _RocqProject
	rocq makefile -f _RocqProject -o $(MAKEFILECOQ)

-include $(MAKEFILECOQ)

check-version:
	@echo "Expecting MetaRocq+Rocq version $(VERSION)"
	@echo "You have"
	@rocq --version
	@opam list | grep metarocq-template

examples:
	make
	make install
	cd ./Examples; make

cleanmake:
	rm -f Makefile.rocq
	rm -f Makefile.rocq.conf
	rm -f .Makefile.rocq.d
	cd ./Examples; make cleanmake

allclean:
	make clean
	make uninstall
	cd ./tests; make clean
	cd ./Examples; make clean
	cd ./tests; make cleanmake
	cd ./Examples; make cleanmake
	-cd ./Examples; rm -f *~
	-cd ./Examples; rm -f *.aux
	-cd ./SmallInversion; rm -f *~
	-cd ./SmallInversion; rm -f *.aux
	make cleanmake
	find . -name "*.aux" -type f -delete


.PHONY: examples clean allclean all cleanall install cleanmake
