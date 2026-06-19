#!/bin/bash

for example in alternating div7 mod3; do
    echo "== $example =="
    mapfile -t dot_files < <(dune exec "lstar.$example" | grep -o "/tmp/[^ ]*")
    count=1
    for file in "${dot_files[@]}"; do
        if [ -f "$file" ]; then
            dot -Tpng "$file" -o "./examples/images/${example}_${count}.png"
            rm "$file"
            ((count++))
        fi
    done
done
