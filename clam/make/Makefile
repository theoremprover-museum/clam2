# Oyster/Clam Makefile

# Top of the Oyster/Clam distribution.  In the standard Oyster/Clam
# distribution, this directory contains the clam/ and oyster/
# directories. 

SRC=${PWD}/../..

# Only direct reference to clam version
CLAMVERSION=2.8.4

CLAMSRC=${SRC}/clam
CLAMLIB=${CLAMSRC}/lib
CLAMSAVE=${CLAMSRC}/lib-save
CLAM_META=${CLAMSRC}/meta-level-support
CLAM_OBJ=${CLAMSRC}/object-level-support
CLAM_PLANNING=${CLAMSRC}/proof-planning
CLAM_LOW_LEVEL=${CLAMSRC}/low-level-code
CLAM_INTERFACE=${CLAMSRC}/interface-code

# Prolog dialect to compile for:
# only sicstus is supported.
#
# DIA = sic - Sicstus 

DIA=sic
DIADIR= ${CLAMSRC}/dialect-support
DIALECT=$(DIADIR)/$(DIA)
# where to find the Oyster source
OYSTERSRC=${SRC}/oyster

# Interface support code.   Set SOCKET_SUPPORT=yes if you want it
SOCKET_SUPPORT=no

# names of various Prologs
SICSTUS=sicstus

CC=gcc

# how to save a prolog image in DIA prolog
SAVE_PROGRAM=save_program

.SUFFIXES:

LOWLEV=	$(CLAM_LOW_LEVEL)/lowlev.pl 	\
	$(CLAM_LOW_LEVEL)/noise.pl 	\
	$(CLAM_LOW_LEVEL)/nested_ops.pl	\
	$(CLAM_LOW_LEVEL)/free_vars.pl 	\
	$(CLAM_LOW_LEVEL)/nuprlterm.pl 	\
	$(CLAM_LOW_LEVEL)/guess_type.pl	\
	$(CLAM_LOW_LEVEL)/instan.pl 	\
	$(CLAM_LOW_LEVEL)/sub_term.pl 	\
	$(CLAM_LOW_LEVEL)/one_way.pl

INTERFACE=${CLAM_INTERFACE}/socket_server.pl

PLANUTIL=$(CLAM_PLANNING)/util.pl 	\
	$(CLAM_PLANNING)/portrayTeX.pl	\
	$(CLAM_PLANNING)/applicable.pl

PLANENG=$(CLAM_PLANNING)/library.pl 	\
	$(CLAM_PLANNING)/method_db.pl 	\
	$(CLAM_PLANNING)/plan_bf.pl 	\
	$(CLAM_PLANNING)/plan_df.pl 	\
	$(CLAM_PLANNING)/plan_gdf.pl 	\
	$(CLAM_PLANNING)/plan_id.pl 	\
	$(CLAM_PLANNING)/plan_vi.pl 	\
	$(CLAM_PLANNING)/plan_dht.pl 	\
	$(CLAM_PLANNING)/plan_gdht.pl 	\
	$(CLAM_PLANNING)/plan_idht.pl 	\
	$(CLAM_PLANNING)/writef.pl

METAPREDS=$(CLAM_META)/elementary.pl 	\
	$(CLAM_META)/propositional.pl 	\
	$(CLAM_META)/reduction.pl 	\
	$(CLAM_META)/cancellation.pl 	\
	$(CLAM_META)/schemes.pl  	\
	$(CLAM_META)/wave_rules.pl 	\
	$(CLAM_META)/annotations.pl 	\
	$(CLAM_META)/so.pl		\
	$(CLAM_META)/method_pre.pl 	\
	$(CLAM_OBJ)/oyster-theory.pl 	\
	$(CLAM_META)/method_con.pl 	\
	$(CLAM_META)/methodical.pl 	\
	$(CLAM_META)/methods.pl 	\
	$(CLAM_META)/dp/cm1.pl 		\
	$(CLAM_META)/dp/cm2.pl 		\
	$(CLAM_META)/dp/cm3.pl 		\
	$(CLAM_META)/dp/cooper.pl	\
	$(CLAM_META)/dp/dnf.pl		\
	$(CLAM_META)/hint_context.pl 	\
	$(CLAM_META)/hint_pre.pl        \
        $(CLAM_META)/tactics.pl         \
        $(CLAM_META)/tactics_wf.pl 
#	$(CLAM_META)/dp/hodes.pl

LIBNEEDS=${CLAMLIB}/needs.pl

TACTICS=$(CLAM_META)/tactics.pl 	\
	$(CLAM_META)/tactics_wf.pl

CONFIGS=${CLAMSRC}/config/tactics.pl 	\
	${CLAMSRC}/config/methods.pl 	\
	${CLAMSRC}/config/hints.pl

# these files are loaded atop Clam to drive the 
# X interface.  THIS IS NOT SUPPORTED, and is UNDOCUMENTED
XINTERFACE=${CLAMSRC}/x-support/prolog-src/xutil.pl	\
	${CLAMSRC}/x-support/prolog-src/xeval.pl	\
	${CLAMSRC}/x-support/prolog-src/xplan.pl 	\
	${CLAMSRC}/x-support/prolog-src/xapplicable.pl

SOURCES=$(PLANUTIL) $(PLANENG) $(METAPREDS) $(LIBNEEDS) $(TACTICS)

BMRA=	${CLAMSRC}/bmra/bmra_in		\
	${CLAMSRC}/bmra/rawsugg		\
	${CLAMSRC}/bmra/merge 		\
	${CLAMSRC}/bmra/extension	\
	${CLAMSRC}/bmra/flaw_check 	\
	${CLAMSRC}/bmra/select
DATA_TYPE_SHELL=${CLAMSRC}/data-type-shell/sh

RASRC=$(DATA_TYPE_SHELL)/nested_ops.pl 	\
	$(DATA_TYPE_SHELL)/nuprlterm.pl	\
	$(DATA_TYPE_SHELL)/shell_indl 	\
	$(DATA_TYPE_SHELL)/shell_meas 	\
	$(DATA_TYPE_SHELL)/def_rec 	\
	$(DATA_TYPE_SHELL)/shell_prin	\
	$(DATA_TYPE_SHELL)/io_rec 	\
	$(DATA_TYPE_SHELL)/def_synth  	\
	$(DATA_TYPE_SHELL)/shell_strc 	\
	$(DATA_TYPE_SHELL)/define  	\
	$(DATA_TYPE_SHELL)/rec_eqns 	\
	$(DATA_TYPE_SHELL)/template 	\
	$(DATA_TYPE_SHELL)/ind_lemmas 	\
	$(DATA_TYPE_SHELL)/measures  	\
	$(DATA_TYPE_SHELL)/shell_decl 

# COMPCLAM='[makeclam]. compile_and_save_clam(clam). halt.'
COMPCLAM = "restore('clamlib.sic'). [makeclam]. compile_and_save_clam(clam). halt."
COMPCLAMLIB="restore('oyster.sic'). [makeclam]. compile_and_save_clam(clamlib). halt."
# easy-to-use wrappers
clam:		clam.v${CLAMVERSION}.${DIA}
	./makescript
clamlib:	clamlib.v${CLAMVERSION}.${DIA}
oyster:		oyster.${DIA}

#clam.$(DIA) clam.v${CLAMVERSION}.$(DIA): loadfile makeclam.pl \
#					 clamlib.v${CLAMVERSION}.$(DIA) \
#					 $(INTERFACE) $(SOURCES) $(CONFIGS)
#	@rm -f clam.$(DIA) .sourcelist
#	@echo 'files_to_load([' > .sourcelist
#	@if [ "${DIA}" = "sic" -a "${SOCKET_SUPPORT}" = "yes" ]; \
#	  then (./loadfile $(INTERFACE) >> .sourcelist; \
#	       echo ',' >> .sourcelist); \
#	fi
#	@./loadfile $(SOURCES) $(CONFIGS) >> .sourcelist
#	@echo ']).' >> ./.sourcelist	
#	echo ${COMPCLAM} | ./clamlib.v${CLAMVERSION}.$(DIA)
#	ln -s clam.v${CLAMVERSION}.$(DIA) clam.$(DIA)

clam.sic clam.v${CLAMVERSION}.sic: loadfile makeclam.pl \
					 clamlib.v${CLAMVERSION}.sic \
					 $(INTERFACE) $(SOURCES) $(CONFIGS)
	@rm -f clam.sic .sourcelist
	@echo 'files_to_load([' > .sourcelist
	@if [ "${DIA}" = "sic" -a "${SOCKET_SUPPORT}" = "yes" ]; \
	  then (./loadfile $(INTERFACE) >> .sourcelist; \
	       echo ',' >> .sourcelist); \
	fi
	@./loadfile $(SOURCES) $(CONFIGS) >> .sourcelist
	@echo ']).' >> ./.sourcelist	
	echo ${COMPCLAM} | ${SICSTUS} 
	ln -s clam.v${CLAMVERSION}.sic clam.sic

clamlib.$(DIA) clamlib.v${CLAMVERSION}.$(DIA): 	loadfile makeclam.pl oyster.$(DIA) \
		                               	sysdep.pl $(DIALECT)/libs.pl \
						$(LOWLEV) 
	@rm -f clamlib.$(DIA) .sourcelist
	@echo 'files_to_load([' > .sourcelist
	@./loadfile sysdep.pl $(LOWLEV) >> .sourcelist
	@echo ']).' >> .sourcelist	
	echo ${COMPCLAMLIB} | ${SICSTUS}
	ln -s clamlib.v${CLAMVERSION}.$(DIA) clamlib.$(DIA)

oyster.sic: ${DIADIR}/sic/boot.pl ${OYSTERSRC}/sicstus.pl ${OYSTERSRC}/oyster.pl ${OYSTERSRC}/oylibs.pl
	echo "[ '${DIALECT}/boot.pl', '${OYSTERSRC}/sicstus.pl']," \
	"consult( '${OYSTERSRC}/oyster.pl' ), ${SAVE_PROGRAM}('oyster.sic')." \
	| ${SICSTUS}

sysdep.pl:	Makefile
	@rm -f sysdep.pl 
	@echo "source_dir('${CLAMSRC}')." 	>  sysdep.pl
	@echo "clam_version('${CLAMVERSION}')." >> sysdep.pl
	@echo "lib_dir(['*'])." 		>> sysdep.pl
	@echo "lib_dir_system('${CLAMLIB}')." 	>> sysdep.pl
	@echo "saving_dir('${CLAMSAVE}')." 	>> sysdep.pl

loadfile: loadfile.c 
	$(CC) -o loadfile loadfile.c
clean:
	rm -f  *~  *.sic *.o *.qui loadfile clam \
		sysdep.pl .sourcelist .configs.pl \
                ../lib-save/thm/????* ../lib-save/plan/????*


