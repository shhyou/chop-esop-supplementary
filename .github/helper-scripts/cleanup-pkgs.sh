#!/bin/bash

for PKG in concolic-hop-model concolic-hop-prototype; do
  echo Checking $PKG
  raco pkg show "$PKG" | grep "$PKG"
  if [[ $? -eq 0 ]]; then
    raco pkg remove "$PKG"
  fi
done
