#!/bin/bash

DIR="${1}"
FLAG="${2}"

RED='\033[0;31m'
BLUE='\033[0;34m'
GRAY='\033[0;37m'
NC='\033[0m'

if [ $# -ne 2 ]; then
    echo -e "${RED}This script should be run as follows:${NC}"
    echo -e "${RED}    bash check.sh \"dir\"${NC}"
    echo -e "${RED}the \"dir\" is the directory where the \".kf\" programs are.${NC}"
    echo -e "${RED}  Options are:${NC}"
    echo -e "${RED}    -c => Check the outputs and warns suspicious cases.${NC}"
    echo -e "${RED}    -p => Print the output and possible errors.${NC}"
fi

this=$(pwd)
cd ../
compilerDir=$(pwd)
cd "${this}"
cd "${DIR}"
testsDir=$(pwd)
testsFiles=$(ls *.kf | sort)

cd "$compilerDir"
for f in $testsFiles; do
    if [ "$FLAG" == "-c" ]; then
        output=$(cabal new-run Kuifje-compiler "$testsDir/$f" 2>&1)
        if echo "$output" | grep -q "hyper"; then
	    echo -e "Program ${GRAY}$testsDir/$f${NC} does not break the compiler."
	else
            echo -e "Error in program ${RED}$testsDir/$f${NC}."
        fi
        echo "- - - - - - - - - - - - - - - - - - - -"
    fi
    if [ "$FLAG" == "-p" ]; then
        output=$(cabal new-run Kuifje-compiler "$testsDir/$f" 2>&1)
	echo "======================================="
	echo "FILE: $testsDir/$f"
	echo "======================================="
	cat "$testsDir/$f"
	echo "- - - - - - - - - - - - - - - - - - - -"
	echo "${output}"
        echo "- - - - - - - - - - - - - - - - - - - -"
    fi
done

cd "$this"
