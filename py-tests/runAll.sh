#!/bin/bash

THIS=$(pwd)
progs=$(ls *.kf)
cd "${THIS}/../"
for i in $progs; do
  prog="py-tests/$i"
  echo "Running program: ${prog}"
  cat "${prog}"
  echo "=========="
  cabal new-run Kuifje-compiler "${prog}" 1> /dev/null
  echo "=========="
done
cd "${THIS}"
