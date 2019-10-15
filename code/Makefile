CURRENT_DIR=.
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

INCLUDE_DEMO = -R $(CURRENT_DIR)/ AB
COQ_FLAG = $(INCLUDE_DEMO)
DEP_DEMO = -R $(CURRENT_DIR) AB
DEP_FLAG = $(DEP_DEMO) 

CourseLibrary_FILES = Imp9.v

Project_FILES = \
	PolyAB.v Denotation.v HoareLogic.v Soundness.v Demos.v

FILES = \
	$(CourseLibrary_FILES) \
	$(Project_FILES)

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) -w "none" $(COQ_FLAG) $(CURRENT_DIR)/$*.v

all: $(FILES:%.v=%.vo)

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm *.vo *.glob .*.aux

.DEFAULT_GOAL := all

include .depend
