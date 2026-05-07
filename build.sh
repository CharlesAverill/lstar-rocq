dune clean
echo "[*] Building lstar-rocq"
dune build -p lstar-rocq
cp _build/default/bin/*.ml bin
rm bin/Bin*.ml bin/PosDef.ml
grep "^From lstar Require Import ExtrOptimizations" theories/Extraction.v > /dev/null
if [ $? ]; then
	rm bin/Bool.ml bin/ListDef.ml bin/PeanoNat.ml
fi
echo "[*] Building lstar"
dune build -p lstar
echo "[*] Done"
