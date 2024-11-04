# Kuifje

A prototype for a Quantitative Information Flow aware programming language.

Based on the paper: "Quantitative Information Flow with Monads in Haskell" by Jeremy Gibbons, Annabelle McIver, Carroll Morgan, and Tom Schrijvers.

## Generating documentation

The important functions in the code are documented using Haddock notation.

To generate the documentation in HTML format, run `cabal haddock`.

## Defining a program

The syntax of the language is defined in the `src/Syntax.hs` file. You can use the predefined constructor functions and the combinator `<>` to define programs. Using the `Control.Lens` library and helper functions for the syntax can simplify the implementation.

A brief example:

```hs
-- | State space for the program.
data SE = SE {
  _x :: Integer,
  _y :: Integer
  } deriving (Eq, Ord)
makeLenses ''SE

-- | Initialize the state by giving a value to x and setting y to 0.
initSE :: Integer -> SE
initSE x = SE { _x = x, _y = 0 }

program :: Kuifje SE
program
  = update (\s -> return (s.^y $ 0)) <>                 -- y := 0
    while (\s -> return (s^.x > 0)) (                   -- while (x > 0) {
      update (\s -> return (s.^y $ (s^.x + s^.y))) <>   --     y := x + y
      update (\s -> return (s.^x $ (s^.x - 1)))         --     x := x - 1
    )                                                   -- }
```

For more elaborate syntax, see the examples.

## Running the analysis

The function `hysem` from the `Semantics` module can be used to calculate the hyper-distributions based on a program and the input distributions.

The `Semantics` module offers the `bayesVuln` function to calculate the Bayes Vulnerability of distributions, this can be combined with the `condEntropy` function to calculate the average entropy over a hyper-distribution.

Continuing the above example:

```hs
-- | Extract the meaningful variable from the state space.
project :: Dist (Dist SE) -> Dist (Dist Integer)
project = fmap (fmap (\s -> s^.y))

-- | Generate the hyper-distribution for an input of x : [5..8]
-- with uniform distribution.
hyper :: Dist (Dist Integer)
hyper = project $ hysem program (uniform [initSE x | x <- [5..8]])

run :: IO ()
run = do
  putStrLn "> hyper"
  print hyper
  putStrLn "> condEntropy bayesVuln hyper"
  print $ condEntropy bayesVuln hyper

-- > hyper
-- 1 % 4   1 % 1   15
-- 1 % 4   1 % 1   21
-- 1 % 4   1 % 1   28
-- 1 % 4   1 % 1   36

-- > condEntropy bayesVuln hyper
-- 1 % 1
```

## Examples

The following examples are implemented in this repository:

- The Monty-Hall problem: `Monty.hs`
- Defence against side-channels: `SideChannel.hs`
- Password checker: `Password.hs`
