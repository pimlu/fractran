#!/bin/sh
set -e

# https://stackoverflow.com/a/246128
DIR="$(dirname $(readlink -f $0))"

cd "$DIR"

if [ "$1" = '--browser' ]; then
  if [ "$2" = 'clean' ]; then
    rm -rf browser_test;
    rm -f src/*.hi src/*.o
    exit 0
  fi
  mkdir -p browser_test
  docker run --rm -it -v $DIR:/mirror -w /mirror terrorjack/asterius \
    ahc-link --browser --input-hs src/main.hs --output-directory browser_test --debug
else
  if [ "$1" = 'clean' ]; then
    rm -r out;
    exit 0
  fi
  mkdir -p out
  ghc --make -O2 src/main.hs -isrc -odir out -hidir out -o fractran
fi
