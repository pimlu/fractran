# Cycle Detecting FRACTRAN Evaluator
###### Or, How I Evaluated my FRACTRAN Programs 10x Faster Using this One Weird Trick

Try it out here: [pimlu.github.io/fractran](https://pimlu.github.io/fractran/)

It's actually over 30x faster than the [fastest interpreter I could find online](https://stackoverflow.com/a/1780262) for my standard benchmark (PRIMEGAME, first 100 primes).  Better yet, some FRACTRAN programs/input combinations run billions of times faster or more (like the Hamming weight calculator).

It works by detecting repeating cycles of fractions that are being multiplied by and "fast forwarding" until some register depletes.  It doesn't output intermediate states that it skips, but in my experience programs that indicate meaningful intermediate state always do so at "boundaries" where the logic progression changes, which can't get skipped.  So PRIMEGAME still outputs the primes on its own.

Here's the implementation with some demo (hard coded) FRACTRAN programs called inside main to get you started.  The code was primarily written a few days before a deadline so it's kind of sad-looking.  I cleaned it up a little bit - the better methods of evaluating used to be called `smart`, `smarter`, and `smartest`...

## Building and running the code

You need an installation of GHC. Then run `./build.sh` to compile, or run `./build.sh clean` to remove the build products.  Then to run the demo, run `./fractran`.

To build for the browser, there are more steps. You need to install docker and run `./build.sh --browser` to first populate `web/gen`. Webpack depends on the JS output from Asterius which gets dumped to that directory. Then cd into `web` and run `yarn` which will install the NPM package dependencies.  You then should be able to run `yarn run serve`.

There are some optional mods you can make to the Asterius build to improve the result: a) You can put a proper polyfill of `setImmediate` in `gen/rts.setImmediate.js` to greatly increase the running speed and b) Remove `import('fs')` from `gen/rts.node.mjs` which gets rid of an empty bundle in the webpack output.

## Whitepaper with proofs, benchmarks
[Here.](termpd.pdf) It's not human readable though.

## License
MIT.  Would be nice to get attribution if something interesting were to (somehow) happen though.
