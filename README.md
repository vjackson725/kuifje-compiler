# Kuifje
An imperative language for quantitative information flow. 

## Dependences

- [GHC](https://www.haskell.org/ghc/) 8.10.4 or later
- [CABAL](https://www.haskell.org/cabal/) 3.4.0.0 or later

The process was tested on ubuntu 20.04.

## Setup

To set up the Kuifje compiler, run the following commands:
```
git submodule init
git submodule update
cabal new-build
```

This build process has been checked to run with ghc 8.10.4 and cabal 3.4.0.0.

## Usage
To run the file, you can use cabal. For example, you can run `Examples\BiasCoin.kf` by using 
```
cabal new-run Kuifje-compiler Examples\BiasCoin.kf
```

## Example
There are some examples under the drectory of `Examples`

A brief example `Examples\BiasCoin.kf`:
```c
p <- uniform [0.3, 0.7];
i = 0;
while i < 2:
  result <- 0 [p] 1;
  leak(result);
  i = i + 1;
```

This example demonstrates that there is a biased coin that you do not know which side bias to. It may 0.7 bias toward the head or 0.3 bias toward the head. By flipping the coin twice and leak the coin flip result, how much information you adversary would know about which way the coin bias toward. 

## Running the compiler interactively using GHCI

[Interactive compilation guide using GHCI](https://github.com/gleisonsdm/kuifje-compiler/blob/master/ghci_guide.md)
