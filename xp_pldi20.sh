#!/bin/bash

FILES1="ccm flows inset_flows linkset_flows keyset_ra"
FILES2="give_up"
FILES3="link"

timesfile=/tmp/times-iris
timestotalfile=/tmp/times-total-iris
locfile=/tmp/loc-iris
loctotalfile=/tmp/loc-total-iris

run()
{
    name="${1}"
    tabs=$((2 - ${#name} / 8))
    echo -n "$name"
    perl -E "print \"\t\" x $tabs"
    shift
    rm -f $timesfile $locfile
    for f in $@ ; do
        # ignore comments and blank lines for line counting
        grep -v -e '^[[:space:]]*$' $f.v | grep -v -e "^[[:space:]]*(\*" | wc -l >> $locfile
        { TIMEFORMAT=%3R; time make $f.vo > /dev/null ; } 2>> $timesfile
        echo 1 >> $timesfile
    done
    awk '{sum+=$1;} END{printf("\t& ?\t& ?\t& %d", sum);}' $locfile
    awk '{sum+=$1;} END{print sum;}' $locfile >> $loctotalfile
    awk '{sum+=$1;} END{printf("\t& %d\n", int(sum+0.5));}' $timesfile
    awk '{sum+=$1;} END{printf("%d\n", int(sum+0.5));}' $timesfile >> $timestotalfile
}

make clean
rm -f $loctotalfile $timestotalfile

echo -e "; Module\t\t& Code\t& Proof\t& Total\t& Time"
run "Flow library" $FILES1
run "Link template" $FILES3
run "Give-up template" $FILES2

echo -n -e "Total\t\t"
awk '{sum+=$1;} END{printf("\t& ?\t& ?\t& %d", sum);}' $loctotalfile
awk '{sum+=$1;} END{printf("\t& %d\n", int(sum+0.5));}' $timestotalfile
    