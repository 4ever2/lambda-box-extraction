# Agda frontend tests
These tests are Agda programs compiled to $\lambda_\square$ with the [agda2lambox](https://github.com/agda/agda2lambox/tree/master) tool.
The tests are from the [agda2lambox test suite](https://github.com/agda/agda2lambox/tree/master/test).

The untyped programs (`*.ast`) were compiled with default configuration.

The type programs (`*.tast`) were compiled with `--typed --no-block` flags.

To reproduce the files run:
```bash
#!/bin/bash
git clone git@github.com:omelkonian/agda2lambox.git
cd agda2lambox
cabal install

for f in test/*.agda; do
  agda2lambox $f -o dist/
  agda2lambox --typed --no-block $f -o dist-typed/
done

for f in dist-typed/*.ast; do
    mv "$f" "${f%.ast}.tast"
done

find dist/. -type f -name "*.txt" -delete
find dist-typed/. -type f -name "*.txt" -delete
```
