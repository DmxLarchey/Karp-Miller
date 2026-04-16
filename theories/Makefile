all: Makefile.rocq
	@+$(MAKE) -f Makefile.rocq all

clean: Makefile.rocq
	@+$(MAKE) -f Makefile.rocq cleanall
	@rm -f Makefile.rocq Makefile.rocq.conf
	find \( -name "*.aux" -o -name "*.vo*" -o -name "*.glob" \) -exec rm -f {} \;

Makefile.rocq: _CoqProject
	$(COQBIN)rocq makefile -f _CoqProject -o Makefile.rocq

whitespaces: force
	find . -type f -name "*.v" -exec sed --in-place 's/[[:space:]]\+$$//' {} \+

wc:
	$(COQBIN)rocq wc `find . -name "*.v"`

force _CoqProject Makefile: ;

%: Makefile.rocq force
	@+$(MAKE) -f Makefile.rocq $@

.PHONY: all clean force
