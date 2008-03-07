##########################################################################
##  v      #                  The Coq Proof Assistant                   ##
## <O___,, # CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud ##
##   \VV/  #                                                            ##
##    //   #   Makefile automagically generated by coq_makefile V8.2    ##
##########################################################################

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

#
# This Makefile was generated by the command line :
# coq_makefile -f Make -o Makefile 
#

##########################
#                        #
# Variables definitions. #
#                        #
##########################

CAMLP4LIB:=+camlp4
CAMLP4:=/home/notin/exec/ocaml-3.09.3/bin/camlp4
COQSRC:=-I $(COQTOP)/kernel -I $(COQTOP)/lib \
  -I $(COQTOP)/library -I $(COQTOP)/parsing \
  -I $(COQTOP)/pretyping -I $(COQTOP)/interp \
  -I $(COQTOP)/proofs -I $(COQTOP)/syntax -I $(COQTOP)/tactics \
  -I $(COQTOP)/toplevel -I $(COQTOP)/contrib/correctness \
  -I $(COQTOP)/contrib/extraction -I $(COQTOP)/contrib/field \
  -I $(COQTOP)/contrib/fourier -I $(COQTOP)/contrib/graphs \
  -I $(COQTOP)/contrib/interface -I $(COQTOP)/contrib/jprover \
  -I $(COQTOP)/contrib/omega -I $(COQTOP)/contrib/romega \
  -I $(COQTOP)/contrib/ring -I $(COQTOP)/contrib/xml \
  -I $(CAMLP4LIB)
ZFLAGS:=$(OCAMLLIBS) $(COQSRC)
OPT:=
COQFLAGS:=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)
COQC:=$(COQBIN)coqc
COQDEP:=$(COQBIN)coqdep -c
GALLINA:=$(COQBIN)gallina
COQDOC:=$(COQBIN)coqdoc
CAMLC:=/home/notin/exec/ocaml-3.09.3/bin/ocamlc -rectypes -c
CAMLOPTC:=/home/notin/exec/ocaml-3.09.3/bin/ocamlopt -c
CAMLLINK:=/home/notin/exec/ocaml-3.09.3/bin/ocamlc
CAMLOPTLINK:=/home/notin/exec/ocaml-3.09.3/bin/ocamlopt
GRAMMARS:=grammar.cma
CAMLP4EXTEND:=pa_extend.cmo pa_macro.cmo q_MLast.cmo
PP:=-pp "$(CAMLP4)o -I . -I $(COQTOP)/parsing $(CAMLP4EXTEND) $(GRAMMARS) -impl"

#########################
#                       #
# Libraries definition. #
#                       #
#########################

OCAMLLIBS:=
COQLIBS:= -R . pautomata
COQDOCLIBS:=-R . pautomata

###################################
#                                 #
# Definition of the "all" target. #
#                                 #
###################################

VFILES:=Transitions.v\
  Time.v\
  TimeSyntax.v\
  Timebase.v\
  PAutomata.v\
  PAuto.v\
  Properties.v\
  Coercions.v\
  AutoL.v\
  LList.v\
  Trace.v\
  ABRdef.v\
  Evenements.v\
  ABRgen.v\
  GAutomata.v\
  AutoLMod.v\
  PAutomataMod.v\
  TransMod.v\
  PAutoMod.v\
  PGAuto.v\
  Extract.v\
  gCSMA_CD/Sender.v\
  gCSMA_CD/Contexte.v\
  gCSMA_CD/Bus.v\
  gCSMA_CD/Block_gCSMA_CD.v\
  gCSMA_CD/preambule.v\
  PGM/String.v\
  PGM/Map.v\
  PGM/Pgm.v\
  PGM/Queue.v\
  PGM/Var.v\
  PGM/Comp.v\
  PGM/Vpauto.v
VOFILES:=$(VFILES:.v=.vo)
GLOBFILES:=$(VFILES:.v=.glob)
VIFILES:=$(VFILES:.v=.vi)
GFILES:=$(VFILES:.v=.g)
HTMLFILES:=$(VFILES:.v=.html)
GHTMLFILES:=$(VFILES:.v=.g.html)

all: Transitions.vo\
  Time.vo\
  TimeSyntax.vo\
  Timebase.vo\
  PAutomata.vo\
  PAuto.vo\
  Properties.vo\
  Coercions.vo\
  AutoL.vo\
  LList.vo\
  Trace.vo\
  ABRdef.vo\
  Evenements.vo\
  ABRgen.vo\
  PGM\
  GAutomata.vo\
  AutoLMod.vo\
  PAutomataMod.vo\
  TransMod.vo\
  PAutoMod.vo\
  PGAuto.vo\
  gCSMA_CD\
  Extract.vo\
  gCSMA_CD/Sender.vo\
  gCSMA_CD/Contexte.vo\
  gCSMA_CD/Bus.vo\
  gCSMA_CD/Block_gCSMA_CD.vo\
  gCSMA_CD/preambule.vo\
  PGM/String.vo\
  PGM/Map.vo\
  PGM/Pgm.vo\
  PGM/Queue.vo\
  PGM/Var.vo\
  PGM/Comp.vo\
  PGM/Vpauto.vo

spec: $(VIFILES)

gallina: $(GFILES)

html: $(GLOBFILES) $(VFILES)
	- mkdir html
	$(COQDOC) -toc -html $(COQDOCLIBS) -d html $(VFILES)

gallinahtml: $(GLOBFILES) $(VFILES)
	- mkdir html
	$(COQDOC) -toc -html -g $(COQDOCLIBS) -d html $(VFILES)

all.ps: $(VFILES)
	$(COQDOC) -toc -ps $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`

all-gal.ps: $(VFILES)
	$(COQDOC) -toc -ps -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`



###################
#                 #
# Subdirectories. #
#                 #
###################

PGM:
	cd PGM ; $(MAKE) all

gCSMA_CD:
	cd gCSMA_CD ; $(MAKE) all

####################
#                  #
# Special targets. #
#                  #
####################

.PHONY: all opt byte archclean clean install depend html PGM gCSMA_CD

.SUFFIXES: .v .vo .vi .g .html .tex .g.tex .g.html

%.vo %.glob: %.v
	$(COQC) $(COQLIBS) -dump-glob $*.glob $(COQDEBUG) $(COQFLAGS) $*

%.vi: %.v
	$(COQC) -i $(COQDEBUG) $(COQFLAGS) $*

%.g: %.v
	$(GALLINA) $<

%.tex: %.v
	$(COQDOC) -latex $< -o $@

%.html: %.v %.glob
	$(COQDOC) -glob-from $*.glob  -html $< -o $@

%.g.tex: %.v
	$(COQDOC) -latex -g $< -o $@

%.g.html: %.v %.glob
	$(COQDOC) -glob-from $*.glob -html -g $< -o $@

%.v.d.raw: %.v
	$(COQDEP) -slash $(COQLIBS) "$<" > "$@"\
	  || ( RV=$$?; rm -f "$@"; exit $${RV} )

%.v.d: %.v.d.raw
	$(HIDE)sed 's/\(.*\)\.vo[[:space:]]*:/\1.vo \1.glob:/' < "$<" > "$@" \
	  || ( RV=$$?; rm -f "$@"; exit $${RV} )

byte:
	$(MAKE) all "OPT:=-byte"

opt:
	$(MAKE) all "OPT:=-opt"

install:
	mkdir -p `$(COQC) -where`/user-contrib
	cp -f $(VOFILES) `$(COQC) -where`/user-contrib
	(cd PGM ; $(MAKE) install)
	(cd gCSMA_CD ; $(MAKE) install)

Makefile: Make
	mv -f Makefile Makefile.bak
	$(COQBIN)coq_makefile -f Make -o Makefile

	(cd PGM ; $(MAKE) Makefile)
	(cd gCSMA_CD ; $(MAKE) Makefile)

clean:
	rm -f *.cmo *.cmi *.cmx *.o $(VOFILES) $(VIFILES) $(GFILES) *~
	rm -f all.ps all-gal.ps all.glob $(VFILES:.v=.glob) $(HTMLFILES) $(GHTMLFILES) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) $(VFILES:.v=.v.d)
	- rm -rf html
	(cd PGM ; $(MAKE) clean)
	(cd gCSMA_CD ; $(MAKE) clean)

archclean:
	rm -f *.cmx *.o
	(cd PGM ; $(MAKE) archclean)
	(cd gCSMA_CD ; $(MAKE) archclean)


-include $(VFILES:.v=.v.d)
.SECONDARY: $(VFILES:.v=.v.d)

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

