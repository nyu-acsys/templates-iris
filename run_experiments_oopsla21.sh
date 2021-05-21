#!/bin/bash
set -e

# This is a script for the OOPSLA'21 artifact


# Assumes template proofs are in ~/templates

pushd ./templates/
echo ""
echo "Checking template proofs using Iris/Coq:"
echo ""
./xp_oopsla21.sh
popd

# Assumes GRASShopper is in ~/grasshopper

pushd ./implementations/
echo ""
echo "Checking implementation proofs using GRASShopper:"
echo ""
./xp_oopsla21.sh
popd
