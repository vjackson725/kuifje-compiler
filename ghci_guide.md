# A Tutorial to run Kuifje with ghci 

## Loading modules

To load ghci with the Kuifje compiler loaded, run
```bash
cabal repl
```

The first step is to run ghci, which can be done by:
```bash
ghci
```

Then, we need to directly import some files

```bash
import Text.PrettyPrint.Boxes
import Language.Kuifje.Distribution
import Language.Kuifje.PrettyPrint
:l Kuifje.Env
:l Kuifje.Value
:l Kuifje.Run
```

## Running an example

To run the "Monty" example, please, run the follwing commands:

```bash
hyperOut <- runFile "Examples/Monty.kf" [] (point (E.envFromList [("x", R 0)]))
printBox . toBox $ hyperOut
```
