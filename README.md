# Cycle Detecting FRACTRAN Evaluator
###### Or, How I Evaluated my FRACTRAN Programs 10x Faster Using this One Weird Trick

Try it out here: [pimlu.github.io/fractran](https://pimlu.github.io/fractran/)

It's actually over 30x faster than the [fastest interpreter I could find online](https://stackoverflow.com/a/1780262) for my standard benchmark (PRIMEGAME, first 100 primes).  Better yet, some FRACTRAN programs/input combinations run billions of times faster or more (like the Hamming weight calculator).

It works by detecting repeating cycles of fractions that are being multiplied by and "fast forwarding" until some register depletes.  It doesn't output intermediate states that it skips, but in my experience programs that indicate meaningful intermediate state always do so at "boundaries" where the logic progression changes, which can't get skipped.  So PRIMEGAME still outputs the primes on its own.

Here's the implementation with some demo (hard coded) FRACTRAN programs called inside main to get you started.  The code was primarily written a few days before a deadline so it's kind of sad-looking.  I cleaned it up a little bit - the better methods of evaluating used to be called `smart`, `smarter`, and `smartest`...

## Building and running the code

You need an installation of GHC. Then run `./build.sh` to compile, or run `./build.sh clean` to remove the build products.  Then to run the demo, run `./fractran`.

## Whitepaper with proofs, benchmarks
[Here.](termpd.pdf)

## License
This code is useless anyway, it's MIT.  Would be nice to get attribution if something interesting were to (somehow) happen though.
