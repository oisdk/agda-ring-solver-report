#!/bin/bash
find . -type f -name '*.lagda' | while read -r code ; do
    dir=$(dirname "$code")
    file=$(basename "$code" .lagda).tex
    if [ ! -e "$dir/$file" ]
    then
        agda --latex --latex-dir=. "$code"
    fi
done
