.PHONY: default genarm genarm-lite archive archive-lite all tests clean realclean deepclean
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


./output/instructions.what4 ./output/functions.what4 &:: ${SOURCE_FILES} ${HS_SOURCES}
	cabal v2-build dismantle-arm-xml -f -asl-lite
	cabal v2-run asl-translator-exec -f -asl-lite -- --output-functions="./output/functions.what4" --output-instructions="./output/instructions.what4" --asl-spec="${PARSED}/" --parallel


./output/instructions-lite.what4 ./output/functions-lite.what4 &:: ${SOURCE_FILES} ${HS_SOURCES}
	cabal v2-build --builddir=asl-lite-build dismantle-arm-xml -f asl-lite
	cabal v2-run --builddir=asl-lite-build asl-translator-exec -f asl-lite -- --output-functions="./output/functions-lite.what4" --output-instructions="./output/instructions-lite.what4" --asl-spec="${PARSED}/" --parallel


./output/instructions-norm.what4 ./output/functions-norm.what4 &:: ./output/instructions.what4 ./output/functions.what4
	cabal v2-build dismantle-arm-xml -f -asl-lite
	cabal v2-run asl-translator-exec -f -asl-lite -- --output-norm-functions="./output/functions-norm.what4" --output-norm-instructions="./output/instructions-norm.what4" --output-instructions="./output/instructions.what4" --output-functions="./output/functions.what4" --normalize-mode=all

./output/instructions-norm-lite.what4 ./output/functions-norm-lite.what4 &:: ./output/instructions-lite.what4 ./output/functions-lite.what4
	cabal v2-build --builddir=asl-lite-build dismantle-arm-xml -f asl-lite
	cabal v2-run --builddir=asl-lite-build asl-translator-exec -f asl-lite -- --output-norm-functions="./output/functions-norm-lite.what4" --output-norm-instructions="./output/instructions-norm-lite.what4" --output-instructions="./output/instructions-lite.what4" --output-functions="./output/functions-lite.what4" --normalize-mode=all

./archived/%.what4.gz: ./output/%.what4
	gzip --best --stdout $< > $@

genarm: ./output/instructions-norm.what4 ./output/functions-norm.what4

genarm-lite: ./output/instructions-norm-lite.what4 ./output/functions-norm-lite.what4

archive: ./archived/instructions-norm.what4.gz ./archived/functions-norm.what4.gz

archive-lite: ./archived/instructions-norm-lite.what4.gz ./archived/functions-norm-lite.what4.gz

all:
	cabal v2-build asl-translator

tests:
	rm -f ./archived/formulas.what4.gz
	rm -f ./output/formulas.what4
	cabal v2-test asl-translator-genarm-test
	cabal v2-test asl-translator-formula-test

clean:
	rm -f ./output/*.what4

realclean: clean
	mv ./data/extra_defs.asl . ; rm -rf ./data/*.asl ; mv ./extra_defs.asl ./data/
	rm -f ./data/Parsed/*

deepclean: realclean
	$(MAKE) --directory=${ASL_PARSER} realclean
