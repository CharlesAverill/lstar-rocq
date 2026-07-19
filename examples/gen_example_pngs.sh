#!/bin/bash

for example in dfa.alternating dfa.div7 dfa.mod3 moore.traffic mealy.vending nfa.suffix; do
    echo "== $example =="
    mapfile -t dot_files < <(dune exec "$example" | grep -o "/tmp/[^ ]*")
    count=1
    for file in "${dot_files[@]}"; do
        if [ -f "$file" ]; then
            fn=$(echo $example | sed 's/.*\.//g')
            dot -Tpng "$file" -o "./examples/images/${fn}_${count}.png"
            rm "$file"
            ((count++))
        fi
    done
done
