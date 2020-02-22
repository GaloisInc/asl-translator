#!/usr/bin/env bash

set -euo pipefail

export STACK_YAML=stack-ghc-8.0.2.yaml
export PATH=/opt/cabal/bin:$PATH
cabal v2-update

rm -f ./archived/formulas.what4.gz
rm -f ./output/formulas.what4
cabal v2-test asl-translator-genarm-test
cabal v2-test asl-translator-formula-test
