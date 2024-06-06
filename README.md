# Kuifje
An imperative language for quantitative information flow. 

## Dependences

- [GHC](https://www.haskell.org/ghc/) 8.10.4 or later
- [CABAL](https://www.haskell.org/cabal/) 3.4.0.0 or later

The process was tested on Ubuntu 22.04.4 LTS.

## Setup

To set up the Kuifje repository, and then build the compiler,
run the following commands:
```sh
git submodule init
git submodule update
cabal build
```

This build process has been checked to run with ghc 9.6.2 and cabal 3.6.2.0.

## Usage
To run the file, you can use cabal. For example, you can run
`Examples\BiasCoin.kf` by executing the command

```sh
cabal run -- Kuifje-compiler Examples\BiasCoin.kf
```

## Example
There are some examples under the drectory of `Examples`

A brief example `Examples\BiasCoin.kf`:
```kf
p <- uniform [0.3, 0.7]
i = 0
while i < 2:
  result <- 0 [p] 1
  print(result)
  i = i + 1
```

This example demonstrates that there is a biased coin that you do not know which side bias to. It may 0.7 bias toward the head or 0.3 bias toward the head. By flipping the coin twice and leak the coin flip result, how much information you adversary would know about which way the coin bias toward. 

## Running the compiler interactively using GHCI

[Interactive compilation guide using GHCI](https://github.com/gleisonsdm/kuifje-compiler/blob/master/ghci_guide.md)
