#!/usr/bin/env bash

set -euo pipefail

ghc --version
cabal v2-configure --project-file=cabal.project.newbuild -f asl-lite
cabal v2-update --project-file=cabal.project.newbuild 
cabal v2-build --project-file=cabal.project.newbuild dismantle-arm-xml

rm -f ./archived/instructions-norm-lite.what4.gz

cabal v2-test --project-file=cabal.project.newbuild asl-translator-genarm-test
cabal v2-test --project-file=cabal.project.newbuild asl-translator-formula-test
