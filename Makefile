.PHONY: default genarm unzip archive all clean realclean deepclean
default: all

ASL_PARSER = ./submodules/arm-asl-parser
PARSED = ./data/parsed

HS_SOURCES := $(shell find ./lib ./exe -name '*.hs' -not -path '*/\.*') $(shell find . -name '*.cabal')

cabal.project: cabal.project.newbuild
	cp $< $@

.PRECIOUS: ${PARSED}/%.sexpr ./data/%.asl ${ASL_PARSER}/asl/%.asl ${ASL_PARSER}/asl-parsed/%.sexpr

${PARSED}/%.sexpr: ${ASL_PARSER}/asl-parsed/%.sexpr ./data/%.asl
	cp $< $@

./data/%.asl: ${ASL_PARSER}/asl/%.asl
	cp $< $@

${PARSED}/extra_defs.sexpr: ./data/extra_defs.asl
	cd ${ASL_PARSER}/asl-parser-java && \
	./gradlew -q run --args="defs $(abspath $<)" > $(abspath $@) && \
	[[ -s $(abspath $@) ]] || (rm -f $(abspath $@) && exit 1)

${ASL_PARSER}/asl/%.asl:
	$(MAKE) --directory=${ASL_PARSER} ./asl/$(@F)

${ASL_PARSER}/asl-parsed/%.sexpr:
	$(MAKE) --directory=${ASL_PARSER} ./asl-parsed/$(@F)

SPEC_FILES = arm_defs.sexpr arm_instrs.sexpr support.sexpr arm_regs.sexpr extra_defs.sexpr
SOURCE_FILES = $(SPEC_FILES:%.sexpr=${PARSED}/%.sexpr)

./output/formulas.what4: ${SOURCE_FILES} ${HS_SOURCES}
	cabal v2-build asl-translator-lib
	cabal v2-run asl-translator-exec -- --output-formulas="./output/formulas.what4" --asl-spec="${PARSED}/" --parallel

./output/testformula.what4: ${SOURCE_FILES} ${HS_SOURCES}
	cabal v2-build asl-translator-lib
	cabal v2-run asl-translator-exec -- --output-formulas="$@" --asl-spec="${PARSED}/" --parallel --translation-mode=aarch32_ADC_i_A/aarch32_ADC_i_A1_A

unzip: ./archived/formulas.what4.gz
	gzip --uncompress --stdout $< > ./output/formulas.what4
	touch $@

./archived/formulas.what4.gz:
	gzip --best --stdout ./output/formulas.what4 > $@

genarm: ./output/formulas.what4

archive: ./archived/formulas.what4.gz

all:
	cabal v2-build asl-translator

test: ./output/testformula.what4

clean:
	rm -f ./output/*.what4

realclean: clean
	mv ./data/extra_defs.asl . ; rm -rf ./data/*.asl ; mv ./extra_defs.asl ./data/
	rm -f ./data/Parsed/*

deepclean: realclean
	$(MAKE) --directory=${ASL_PARSER} realclean
