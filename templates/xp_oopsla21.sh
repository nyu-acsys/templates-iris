#!/bin/bash

timesfile=/tmp/times-iris
timestotalfile=/tmp/times-total-iris
locfile=/tmp/loc-iris
loctotalfile=/tmp/loc-total-iris
outputfile=/tmp/templates-table

fail=0

run()
{
    name="${1}"
    tabs=$((2 - ${#name} / 8))
    echo "\\hline" >> $outputfile
    echo -n "$name" >> $outputfile
    perl -E "print \"\t\" x $tabs" >> $outputfile
    shift
    rm -f $timesfile $locfile
    for f in $@ ; do
        # ignore comments and blank lines for line counting
        grep -v -e '^[[:space:]]*$' $f.v | grep -v -e "^[[:space:]]*(\*" | wc -l >> $locfile
        { TIMEFORMAT=%3R; time make $f.vo 2>&1 ; } 2>> $timesfile
        retcode=$?
        if [ $retcode -ne 0 ]; then
            fail=1
            echo -e "\nCoq exited with errors in file $f.v.\n"
        fi
        echo 1 >> $timesfile
    done
    awk '{sum+=$1;} END{printf("\t& ?\t& ?\t& %d", sum);}' $locfile >> $outputfile
    awk '{sum+=$1;} END{print sum;}' $locfile >> $loctotalfile
    awk '{sum+=$1;} END{printf("\t& %d\\\\\n", int(sum+0.5));}' $timesfile >> $outputfile
    awk '{sum+=$1;} END{printf("%d\n", int(sum+0.5));}' $timesfile >> $timestotalfile
}

eval $(opam env)
coq_makefile -f _CoqProject -o Makefile
make clean
rm -f $loctotalfile $timestotalfile $outputfile

echo -e "% Module\t\t& Code\t& Proof\t& Total\t& Time" >> $outputfile
run "Flow Library" "flows/gmap_more flows/ccm flows/flows flows/multiset_flows"
run "Lock Implementation" "util/auth_ext util/lock util/one_shot_proph util/typed_proph"
run "Client-level Spec" "multicopy/multicopy multicopy/multicopy_util multicopy/multicopy_client_level"
run "DF Template" "multicopy/multicopy_df multicopy/multicopy_df_search multicopy/multicopy_df_upsert"
run "LSM DAG Template" "multicopy/multicopy_lsm multicopy/multicopy_lsm_util multicopy/multicopy_lsm_search multicopy/multicopy_lsm_upsert multicopy/multicopy_lsm_compact"

echo -e "\\hline" >> $outputfile
echo -n -e "Total\t\t" >> $outputfile
awk '{sum+=$1;} END{printf("\t& ?\t& ?\t& %d", sum);}' $loctotalfile >> $outputfile
awk '{sum+=$1;} END{printf("\t& %d\\\\\n", int(sum+0.5));}' $timestotalfile >> $outputfile

echo ""
cat $outputfile

if [ $fail -ne 0 ]; then
    exit 1
fi
