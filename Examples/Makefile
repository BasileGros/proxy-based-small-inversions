MAKEFILECOQ=Makefile.rocq
%: $(MAKEFILECOQ)

$(MAKEFILECOQ): _RocqProject
	rocq makefile -f _RocqProject -o $(MAKEFILECOQ)

-include $(MAKEFILECOQ)

cleanmake:
	-rm Makefile.rocq
	-rm Makefile.rocq.conf
	-rm .Makefile.rocq.d