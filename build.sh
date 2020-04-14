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
    exit 0
  fi
  mkdir -p out
  ghc --make -prof -fprof-auto src/main.hs -isrc -odir out -hidir out -o fractran
fi
