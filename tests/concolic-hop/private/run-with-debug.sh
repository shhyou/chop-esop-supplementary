#!/bin/bash
if [[ $# -eq 0 ]]; then
  echo Usage: $0 [-v] commands ...
fi

VERBOSE_LEVEL='info@concolic:status debug@concolic:inputs debug@concolic:adjacent info@concolic:test'
if [[ "$1" == "-v" ]]; then
  shift
  VERBOSE_LEVEL='debug@concolic:status debug@concolic:adjacent debug@concolic:inputs debug@concolic:constraint debug@concolic:pathkey debug@concolic:test'
fi

PLTSTDERR="$VERBOSE_LEVEL" "$@"
