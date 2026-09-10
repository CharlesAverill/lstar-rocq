(** Trie caches for equivalence checking *)

From Stdlib Require Import List.
Import ListNotations.

Section Trie.

Variable K : Type.
Variable K_eq_dec : forall x y : K, {x = y} + {x <> y}.
Variable A : Type.

Inductive trie : Type :=
  | Node : option A -> list (K * trie) -> trie.

Definition empty : trie := Node None nil.

Fixpoint lookup (t : trie) (k : list K) {struct t} : option A :=
    match t with
    | Node v kids =>
        match k with
        | nil => v
        | c :: rest =>
            (fix look (l : list (K * trie)) : option A :=
                 match l with
                 | nil => None
                 | (c', t') :: tl =>
                     if K_eq_dec c c' then lookup t' rest else look tl
                 end) kids
        end
    end.

Fixpoint insert (t : trie) (k : list K) (x : A) {struct k} : trie :=
    match t with
    | Node v kids =>
        match k with
        | nil => Node (Some x) kids
        | c :: rest =>
            Node v
              ((fix upd (l : list (K * trie)) : list (K * trie) :=
                    match l with
                    | nil => cons (c, insert (Node None nil) rest x) nil
                    | (c', t') :: tl =>
                        if K_eq_dec c c' then (c', insert t' rest x) :: tl
                        else (c', t') :: upd tl
                    end) kids)
        end
    end.

End Trie.

Arguments Node {K A}.
Arguments empty {K A}.
Arguments lookup {K} K_eq_dec {A}.
Arguments insert {K} K_eq_dec {A}.
