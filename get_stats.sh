#!/bin/bash

./linismt.py --csvheader

shortcuts=$(./linismt.py --shortlist)

for s in $shortcuts; do 
    ./linismt.py --nocheck --csv $s
done
