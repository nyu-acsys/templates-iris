#!/bin/bash

[[ $OSTYPE =~ "darwin" ]] && {
  alias time=gtime
  alias date=gdate
  alias sed=gsed
  shopt -s expand_aliases
}

#echo "Building Grasshopper"
#./build.sh

timesfile=/tmp/times-grasshopper
locfile=/tmp/loc-grasshopper
timestotalfile=/tmp/times-total-grasshopper
loctotalfile=/tmp/loc-total-grasshopper
outputfile=/tmp/implementations-table

SPLPATH=.

fail=0

run()
{
    name="${1}"
    tabs=$((2 - ${#name} / 8))
    echo  "\\hline" >> $outputfile
    echo -n "$name" >> $outputfile
    perl -E "print \"\t\" x $tabs" >> $outputfile
    shift
    rm -f $timesfile $locfile
    for f in $@ ; do
        #echo "processessing $f"
        python ../grasshopper/bin/line-counter.py $SPLPATH/$f.spl >> $locfile
        echo "../grasshopper/grasshopper.native $SPLPATH/$f.spl -module $f"
        { TIMEFORMAT=%3R; time ../grasshopper/grasshopper.native $SPLPATH/$f.spl -module $f 2>&1 ; } 2>> $timesfile
        retcode=$?
        if [ $retcode -ne 0 ]; then
            fail=1
            echo -e "\nGrasshopper exited with errors on file $f.spl.\n"
        fi
    done
    awk -F "\t" '{specs+=$1; progs+=$2; total+=$3} END{printf("\t& %d\t& %d\t& %d", progs, specs, total);}' $locfile >> $outputfile
    awk -F "\t" '{specs+=$1; progs+=$2; total+=$3} END{printf("%d\t%d\t%d\n", progs, specs, total);}' $locfile >> $loctotalfile
    awk '{sum+=$1;} END{printf("\t& %d\\\\\n", int(sum+0.5));}' $timesfile >> $outputfile
    awk '{sum+=$1;} END{printf("%d\n", int(sum+0.5));}' $timesfile >> $timestotalfile
}

rm -f $loctotalfile $timestotalfile $outputfile

echo -e "; Module\t\t& Code\t& Proof\t& Total\t& Time" >> $outputfile
run "Flow library" "flows ccm multiset-ccm inset-flows lock-coupling"
run "Array Library" "ordered_type array_basic array_map"
echo -e "Single-copy:"
run "B+ tree" "b+-tree"
run "B-link (core)" "b-link-core"
run "B-link (half split)" "b-link-half"
run "B-link (full split)" "b-link-full"
run "Hash table (link)" "hashtbl-give-up"
run "Hash table (give-up)" "hashtbl-link"
run "Lock-coupling list" "list-coupling"
echo -e "Multicopy:"
run "LSM Implementation" "multicopy-lsm"

echo -n -e "Total\t\t" >> $outputfile
awk -F "\t" '{progs+=$1; specs+=$2; total+=$3} END{printf("\t& %d\t& %d\t& %d", progs, specs, total);}' $loctotalfile >> $outputfile
awk '{sum+=$1;} END{printf("\t& %d\n", int(sum+0.5));}' $timestotalfile >> $outputfile

echo ""
cat $outputfile

if [ $fail -ne 0 ]; then
    exit 1
fi
