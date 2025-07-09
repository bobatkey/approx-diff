#!/usr/bin/env bash
set -xe

AGDA_FLAGS="--ignore-interfaces"

ENTRYPOINTS=(
  src/example.agda
)

for file in "${ENTRYPOINTS[@]}"; do
  agda $AGDA_FLAGS "$file"
done
