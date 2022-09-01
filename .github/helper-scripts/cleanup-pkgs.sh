#!/bin/bash

for PKG in chop-esop-supplementary; do
  echo Checking $PKG
  raco pkg show "$PKG" | grep "$PKG"
  if [[ $? -eq 0 ]]; then
    raco pkg remove "$PKG"
  fi
done
