(** Kearns-Vazirani automata learning
    https://doi.org/10.7551/mitpress%2F3897.001.0001 
    
    Reuses the results of TTT.v, which is the same algorithm with
    an extra step. This file removes that step. *)

From Stdlib Require Import Lia PeanoNat.
From lstar Require Import DFA Teacher TTT.
Import ListNotations.

Module KV (s : Symbol) (L : RegularLanguage s) (Tch : Teacher s L).

(** Instantiate the TTT development *)
Module T := TTT s L Tch.
Import s L Tch D.

(** The KV learner *)
Fixpoint kv_learn (fuel : nat) (t : T.ttree)
                  (LE : L.num_states_in_minimal - List.length (T.leaves t) <= fuel)
                  (Hwf : T.wf t)
  : { St : Type & {d : D.t St | minimal d} }.
Proof.
  destruct (equiv_query _ (T.make_dfa t)) eqn:Heq.
  - destruct fuel as [| n].
    + assert (forall x y, x - y <= 0 -> x - y = 0) by lia.
      apply H in LE. clear H.
      apply Nat.sub_0_le, T.full_states_no_ce in LE; auto.
      now rewrite Heq in LE.
    + assert (Hce : accept_string (T.make_dfa t) s <> member s)
        by now apply equiv_query_ce.
      pose proof Hwf as Hwf'.
      destruct Hwf' as (Hwf' & Heps).
      destruct (T.find_split t s Heps
                  (T.wf_consistent t Hwf)
                  (T.wf_NoDup t Hwf)
                  Hce)
          as (target & e & q_new &
              HinT & Hfresh & Hdiff &
              Hwf'' & Heps').
      enough (L.num_states_in_minimal -
              List.length (T.leaves (T.split_leaf t target e q_new)) <= n).
      eapply (kv_learn n (T.split_leaf t target e q_new) H (conj Hwf'' Heps')).
      pose proof
        (T.split_leaf_count t target e q_new
            (T.wf_NoDup t Hwf) HinT Hfresh) as Hcount.
      rewrite Hcount. lia.
  - eexists. exists (T.make_dfa t). now apply T.make_dfa_minimal.
Defined.

(** Seeded with the trivially well-formed singleton tree. *)
Definition kv (_ : unit) : { St : Type & {d : D.t St | minimal d} } :=
  kv_learn num_states_in_minimal (T.Leaf nil) ltac:(lia) (conj I (or_introl eq_refl)).

End KV.
