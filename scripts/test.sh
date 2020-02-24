#!/usr/bin/env bash

set -euo pipefail

export PATH=/opt/ghc/bin:/opt/cabal/bin:$PATH
cp ./cabal.project.newbuild ./cabal.project
cabal v2-update

rm -f ./archived/formulas.what4.gz
rm -f ./output/formulas.what4
cabal v2-test asl-translator-genarm-test
cabal v2-test asl-translator-formula-test
