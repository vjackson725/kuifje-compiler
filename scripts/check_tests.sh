#!/bin/bash

RED='\033[0;31m'
BLUE='\033[0;34m'
GRAY='\033[0;37m'
NC='\033[0m'

this=$(pwd)
cd ../
compilerDir=$(pwd)
cd "tests/"
testsDir=$(pwd)
testsFiles=$(ls *.kf | sort)

cd "$compilerDir"
for f in $testsFiles; do
    output=$(cabal new-run Kuifje-compiler "$testsDir/$f" 2>&1)
    if echo "$output" | grep -q "CallStack"; then
        echo -e "Error in program ${RED}$testsDir/$f${NC}."
    else
        echo -e "Program ${GRAY}$testsDir/$f${NC} does not break the compiler."
    fi
    echo "- - - - - - - - - - - - - - - - - - - -"
done

cd "$this"
