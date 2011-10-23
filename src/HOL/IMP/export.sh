#!/bin/bash
#
# Author: Gerwin Klein
#
#  make a copy of IMP with isaverbatimwrite lines in thy files removed

## diagnostics

function fail()
{
  echo "$1" >&2
  exit 2
}

## main

EXPORT=IMP

rm -rf "$EXPORT"

# make directories

DIRS=$(find . -type d)
for D in $DIRS; do
    mkdir -p "$EXPORT/$D" || fail "could not create directory $EXPORT/$D"
done

# filter thy files

FILES=$(find . -name "*.thy")
for F in $FILES; do
    grep -v isaverbatimwrite "$F" > "$EXPORT/$F"
done

# copy rest

cp ROOT.ML "$EXPORT"
cp -r document "$EXPORT"

# tar and clean up
tar cvzf "$EXPORT.tar.gz" "$EXPORT"
rm -r "$EXPORT"
