#!/bin/bash
set -e -x

[ -d "./oopsla21_artifact" ] && rm -rf oopsla21_artifact
mkdir oopsla21_artifact
cd oopsla21_artifact

cp ../README_oopsla21.md .
mv README_oopsla21.md README.md
cp ../run_experiments_oopsla21.sh .
mv run_experiments_oopsla21.sh run_experiments.sh
cp ../setup.sh .

mkdir implementations
mkdir templates
mkdir templates/flows
mkdir templates/util
mkdir templates/multicopy

files=(
"implementations/xp_oopsla21.sh" 
"implementations/array_basic.spl"
"implementations/array_map.spl"
"implementations/ordered_type.spl"
"implementations/multicopy_lsm.spl"
"templates/xp_oopsla21.sh"
"templates/_CoqProject_oopsla21"
"templates/flows/gmap_more.v"
"templates/flows/ccm.v"
"templates/flows/flows.v"
"templates/flows/multiset_flows.v"
"templates/util/auth_ext.v"
"templates/util/lock.v"
"templates/util/one_shot_proph.v"
"templates/util/typed_proph.v"
"templates/multicopy/multicopy.v"
"templates/multicopy/multicopy_util.v"
"templates/multicopy/multicopy_client_level.v"
"templates/multicopy/multicopy_lsm.v"
"templates/multicopy/multicopy_lsm_util.v"
"templates/multicopy/multicopy_lsm_search.v"
"templates/multicopy/multicopy_lsm_upsert.v"
"templates/multicopy/multicopy_lsm_compact.v"
"templates/multicopy/multicopy_df.v"
"templates/multicopy/multicopy_df_search.v"
"templates/multicopy/multicopy_df_upsert.v"
)

for t in ${files[@]}; do
  cp ../$t $t
done

mv templates/_CoqProject_oopsla21 templates/_CoqProject

cd ..

zip -r oopsla21_artifact.zip oopsla21_artifact/

# rm -rf oopsla21_artifact/
