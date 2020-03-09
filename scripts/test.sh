#!/usr/bin/env bash

set -euo pipefail

export PATH=/opt/ghc/bin:/opt/cabal/bin:$PATH

if [[ -f "./cabal.project.newbuild" && ! -f "./cabal.project" ]]; then
    cp ./cabal.project.newbuild ./cabal.project
fi

cabal v2-update

# First check that we can parse in the archived 
# formulas
cabal v2-test asl-translator-formula-test

# For the sake of making CI work, we
# reduce the set of instructions here
./submodules/dismantle/scripts/minify-asl.sh

cabal v2-build asl-translator-exec

rm -f ./archived/formulas.what4.gz
rm -f ./output/formulas.what4

cabal v2-run asl-translator-exec
cabal v2-test asl-translator-formula-test

./submodules/dismantle/scripts/deminify-asl.sh
git checkout ./archived/
