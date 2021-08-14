all: smedlmon

smedlmon: dist/build/smedlmon/smedlmon
	echo smedlmon built

dist/build/smedlmon/smedlmon: smedlmon.hs	\
	HString.hs				\
	Setup.hs				\
	default.nix				\
	smedlmon.cabal
	cabal build

smedlmon.hs: Makefile.coq			\
	Extract.v				\
        Monitor_oni.v                           \
        determinism.v                           \
	Refinement.v				\
	aux_monitor.v				\
	wellForm.v			\
        deter_definition.v                      \
	smedlDef/SMEDL_helper.v			\
	smedlDef/SmedlAST_submission.v		\
	smedlDef/semantic_rules.v		\
	smedlDef/smedl_common_lemmas.v			\
	wellFormScenario.v				\
	well_decision_proc.v			\
	fixcode.pl
	make -f Makefile.coq
	perl -i fixcode.pl $@

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -f *.glob *.v.d *.vo *.hi *.o Main result *.hp .*.aux
	rm -f smedlmon smedlmon.hs
