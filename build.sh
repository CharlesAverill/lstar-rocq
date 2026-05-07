dune clean
echo "[*] Building lstar-rocq"
dune build -p lstar-rocq
cp _build/default/lib/*.ml lib
rm lib/Bin*.ml lib/PosDef.ml
grep "^From lstar Require Import ExtrOptimizations" theories/Extraction.v > /dev/null
if [ $? ]; then
	rm lib/Bool.ml lib/ListDef.ml lib/PeanoNat.ml
fi
echo "[*] Building lstar"
dune build -p lstar
echo "[*] Done"
