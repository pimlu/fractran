#!/bin/sh
set -e

# https://stackoverflow.com/a/246128
DIR="$(dirname $(readlink -f $0))"

cd "$DIR"

if [ "$1" = '--browser' ]; then
  if [ "$2" = 'clean' ]; then
    rm -rf web/gen;
    rm -f src/*.hi src/*.o
    exit 0
  fi
  mkdir -p web/gen
  docker run --rm -it -v $DIR:/mirror -w /mirror terrorjack/asterius \
    ahc-link --browser --no-main --ghc-option -O2 --input-hs src/Browser.hs \
    --output-directory web/gen --export-function=hsRunDynamic
else
  if [ "$1" = 'clean' ]; then
    rm -rf out;
    rm -f fractran fractran-bench
    exit 0
  fi
  mkdir -p out
  GHC_FLAGS="-dynamic"
  if [ "$1" = '--profile' ]; then
    GHC_FLAGS="-prof -fprof-auto"
  fi
  ghc --make $GHC_FLAGS src/main.hs -isrc -odir out -hidir out -o fractran
  ghc --make $GHC_FLAGS src/bench_main.hs -isrc -odir out -hidir out -o fractran-bench
fi
