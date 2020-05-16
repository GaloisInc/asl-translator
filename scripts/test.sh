#!/usr/bin/env bash

set -euo pipefail

export PATH=/opt/ghc/bin:/opt/cabal/bin:$PATH

if [[ -f "./cabal.project.newbuild" && ! -f "./cabal.project" ]]; then
    #cp ./cabal.project.newbuild ./cabal.project
    echo "foo"
fi

cabal v2-configure -f asl-lite
cabal v2-update
cabal v2-build dismantle-arm-xml


rm -f ./archived/instructions-norm-lite.what4.gz

cabal v2-test asl-translator-genarm-test
cabal v2-test asl-translator-formula-test
