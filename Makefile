MAKEFILECOQ=Makefile.rocq
%: $(MAKEFILECOQ)

$(MAKEFILECOQ): _RocqProject
	rocq makefile -f _RocqProject -o $(MAKEFILECOQ)

-include $(MAKEFILECOQ)

examples:
	make
	make install
	cd ./Examples; make

cleanmake:
	rm Makefile.rocq
	rm Makefile.rocq.conf
	rm .Makefile.rocq.d
	cd ./Examples; make cleanmake

allclean:
	make clean
	make uninstall
	cd ./tests; make clean
	cd ./Examples; make clean
	cd ./tests; make cleanmake
	cd ./Examples; make cleanmake
	-cd ./Examples; rm *~
	-cd ./Examples; rm *.aux
	-cd ./SmallInversion; rm *~
	-cd ./SmallInversion; rm *.aux
	make cleanmake
	find . -name "*.aux" -type f -delete


.PHONY: examples clean allclean all cleanall install cleanmake
