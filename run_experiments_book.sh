#!/bin/bash
set -e

# This is a script for the book Automated Verification of Concurrent Search Structures


# Assumes template proofs are in ~/templates

pushd ./templates/
echo ""
echo "Checking template proofs using Iris/Coq:"
echo ""
./xp_book.sh
popd

# Assumes GRASShopper is in ~/grasshopper

pushd ./implementations/
echo ""
echo "Checking implementation proofs using GRASShopper:"
echo ""
./xp_book.sh
popd
