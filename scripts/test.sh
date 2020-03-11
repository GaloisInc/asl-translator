#!/usr/bin/env bash

set -euo pipefail

export PATH=/opt/ghc/bin:/opt/cabal/bin:$PATH

if [[ -f "./cabal.project.newbuild" && ! -f "./cabal.project" ]]; then
    cp ./cabal.project.newbuild ./cabal.project
fi

cabal v2-update
cabal v2-build dismantle-arm-xml -f asl-lite

cabal v2-test asl-translator-formula-test

rm -f ./archived/instructions-norm-lite.what4.gz
touch ./archived/instructions-norm-lite.what4.gz

make genarm-lite

cabal v2-test asl-translator-formula-test -f asl-lite
