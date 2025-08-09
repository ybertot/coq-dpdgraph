#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#            This file is part of the DpdGraph tools.
#  Copyright (C) 2009-2025 Anne Pacalet (Anne.Pacalet@free.fr)
#                      and Yves Bertot (Yves.Bertot@inria.fr)
#      This file is distributed under the terms of the
#       GNU Lesser General Public License Version 2.1
#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

NAME=coq-dpdgraph
VERSION=1.0-9.0

clean : clean_coq clean_test

all install uninstall test test-suite clean_test : Make_coq
	make -f $< $@

Make_coq : Make
	rocq makefile -f $< -o $@

#-------------------------------------------------------------------------------
DISTRIBUTED+=Makefile LICENSE README.md configure Makefile.in

distrib : $(NAME)-$(VERSION).tgz

%.tgz : clean
	$(ECHO_CIBLE)
	rm -rf $* $@
	mkdir $*
	cp --parents $(DISTRIBUTED) $*
	tar zcvf $@ $*
	rm -rf $*
	$(ECHO) "Don't forget to copy README.md and $@ on the server if needed"


#-------------------------------------------------------------------------------
# testing


#-------------------------------------------------------------------------------
clean_coq : Make_coq
	$(MAKE) -f $< clean

clean_config:
	rm -rf autom4te.cache
	rm -f configure config.log config.status
	rm -r Makefile

clean : clean_coq clean_test
	rm -f $(GENERATED)
	rm -f $(CMOS_DPDUSAGE) $(CMOS_DPD2DOT) $(CMXS) $(ML_ALL:%.ml=%.o) *.cmi
	rm -f $(ML_ALL:%.ml=%.annot)
	rm -f $(DPD2DOT) $(DPDUSAGE) $(DPDPLUGIN)
	$(ECHO) "Use: make clean_config to remove configuration generated files"

archi_clean: clean clean_config

#-------------------------------------------------------------------------------
