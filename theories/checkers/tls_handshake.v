(* tls_handshake.v

   Uses TTT to build a DFA encoding a black-box TLS server, then runs a 
   verified bounded model checker to find state machine vulnerabilities.

   Security Property:
   The server must not accept `ApplicationData` if it has not yet received 
   a `Certificate` or `ClientKeyExchange` (Authentication Bypass).

	Provides:
	- [AuthBypass] : a formal definition of authentication bypass
	- [check_upto] : an executable bounded search
	- [checker_correct] : a proof that finding a sequence using `check_upto`
	  is logically equivalent to a vulnerability existing in the black box.
*)

From lstar Require Import TTT_DFA automata.DFA Teacher ListLemmas.
From Stdlib Require Import List Bool PeanoNat Lia.
Import ListNotations.

Inductive TLSMsg :=
	| ClientHello
	| ServerHello
	| Certificate
	| ClientKeyExchange
	| ChangeCipherSpec
	| Finished
	| ApplicationData
	| Alert.

Module S <: Symbol.
	Definition t := TLSMsg.
	Definition str := list TLSMsg.

	Definition eq_dec (x y : t) : {x = y} + {x <> y}.
	Proof. decide equality. Defined.

	Definition enum := [
		ClientHello; ServerHello; Certificate; ClientKeyExchange; 
		ChangeCipherSpec; Finished; ApplicationData; Alert
	].

	Theorem t_enumerable : forall (x : t), In x enum.
	Proof. destruct x; simpl; intuition. Qed.

	Open Scope string_scope.
	Definition string_of_t t :=
		match t with
		| ClientHello => "chello"
		| ServerHello => "shello"
		| Certificate => "cert"
		| ClientKeyExchange => "key"
		| ChangeCipherSpec => "cipher"
		| Finished => "done"
		| ApplicationData => "data"
		| Alert => "alert"
		end.

	Definition t_of_string s :=
		match s with
		| "chello" => Ok ClientHello
		| "shello" => Ok ServerHello
		| "cert" => Ok Certificate
		| "key" => Ok ClientKeyExchange
		| "cipher" => Ok ChangeCipherSpec
		| "done" => Ok Finished
		| "data" => Ok ApplicationData
		| "alert" => Ok Alert
		| _ => Error "t_of_string"
		end.
	Close Scope string_scope.
End S.

(* A TLS server takes a packet sequence and returns true if accepted *)
Axiom tls_server_accepts : list TLSMsg -> bool.

Module TLSLang <: RegularLanguage S.
	Module D := DFA S.
	Definition member : S.str -> bool := tls_server_accepts.

	Definition encodes {state : Type} (dfa : D.t state) : Prop :=
		forall s, member s = true <-> D.accept_string dfa s = true.

	Definition minimal {state : Type} (dfa : D.t state) : Prop :=
		encodes dfa /\
		forall (state' : Type) (dfa' : D.t state'),
			encodes dfa' ->
			length (D.states state dfa) <= length (D.states state' dfa').

	Parameter num_states_in_minimal : nat.
	Parameter exists_dfa : exists state (d : D.t state),
		minimal d /\ length (D.states state d) <= num_states_in_minimal.
End TLSLang.

(* Assume a teacher oracle exists for the black box *)
Declare Module TLSTeacher : DFATeacher S TLSLang.
Module Learner := TTT S TLSLang TLSTeacher.

Import TLSLang.

(* Extract the learned DFA and its minimality proof *)
Definition learned : { St : Type & { d : D.t St | minimal d } } := 
	Learner.ttt tt.
Definition LSt : Type := projT1 learned.
Definition learned_dfa : D.t LSt := proj1_sig (projT2 learned).

Lemma learned_encodes : forall s,
	tls_server_accepts s = true <-> D.accept_string learned_dfa s = true.
Proof. 
	intros. destruct (proj2_sig (projT2 learned)) as [Henc _]. apply Henc. 
Qed.

(* A trace bypasses auth if ApplicationData appears before any valid Auth step *)
Definition AuthBypass (l : list TLSMsg) : Prop :=
  exists d_i,
    nth_error l d_i = Some ApplicationData /\
    forall a_i, a_i < d_i ->
      nth_error l a_i <> Some Certificate /\
      nth_error l a_i <> Some ClientKeyExchange.

(* Decide whether a trace includes an auth bypass *)
Fixpoint is_auth_bypass (trace : list TLSMsg) : bool :=
  match trace with
  | [] => false
  | ApplicationData :: _ => true
  | Certificate :: _ => false
  | ClientKeyExchange :: _ => false
  | _ :: rest => is_auth_bypass rest
  end.

(* Prove the executable boolean check perfectly reflects the Prop *)
Lemma is_auth_bypass_correct : forall trace,
  is_auth_bypass trace = true <-> AuthBypass trace.
Proof.
  induction trace; split; intro H.
  - discriminate.
  - destruct H as (d_i & Nth & _). 
    rewrite nth_error_nil in Nth. discriminate.
  - destruct a; simpl in *; try discriminate;
    try match goal with
    | [ H : is_auth_bypass trace = true |- _ ] =>
        apply IHtrace in H;
        destruct H as (d_i & Nth & Forall);
        exists (S d_i); split; [exact Nth | ];
        intros a_i Lt; destruct a_i;
        [ split; discriminate | apply Forall; lia ]
    end.
    exists 0. split.
      reflexivity.
    intros. inversion H0.
  - destruct a; simpl in *; auto;
    destruct H as (d_i & Nth & Forall);
    try match goal with
    | [ |- is_auth_bypass trace = true ] =>
        apply IHtrace; destruct d_i; [discriminate | ];
        exists d_i; split; [exact Nth | ];
        intros a_i Lt; apply (Forall (S a_i)); lia
    end;
    assert (0 < d_i) by (destruct d_i; [discriminate | lia]);
      destruct (Forall 0 H); auto.
Qed.

(* Generate all possible TLS traces of exactly length n *)
Fixpoint all_traces (n : nat) : list (list TLSMsg) :=
	match n with
	| O => [[]]
	| S m =>
			let prev := all_traces m in
			flat_map (fun sym => map (cons sym) prev) S.enum
	end.

(* Generate all possible TLS traces up to length n *)
Fixpoint all_traces_upto (n : nat) : list (list TLSMsg) :=
	match n with
	| O => [[]]
	| S m => all_traces (S m) ++ all_traces_upto m
	end.

Lemma all_traces_complete : forall s, In s (all_traces (length s)).
Proof.
	induction s.
	  now left.
	cbn [length all_traces].
	apply in_flat_map.
	exists a. split.
	  apply S.t_enumerable.
	now apply in_map.
Qed.

Lemma all_traces_upto_complete : forall n s,
	length s <= n -> In s (all_traces_upto n).
Proof.
  induction n; intros.
    destruct s. now left. inversion H.
  cbn [all_traces_upto].
	apply in_or_app. destruct (Nat.eq_dec (length s) (S n)).
	  left. rewrite <- e. apply all_traces_complete.
	  right. apply IHn. lia.
Qed.

(* Checks if the learned DFA accepts ANY sequence that triggers the bypass *)
Definition check_upto (n : nat) : bool :=
	existsb (fun s => is_auth_bypass s && D.accept_string learned_dfa s)
					(all_traces_upto n).

Definition vulnerability_exists : Prop :=
	exists s, AuthBypass s /\ tls_server_accepts s = true.

(* The boolean search on the extracted DFA is formally equivalent to finding 
	 a vulnerability in the black box. *)
Theorem checker_correct :
	vulnerability_exists <-> exists n, check_upto n = true.
Proof.
	split.
	- intros (s & Hbad & Hs).
		exists (length s). unfold check_upto.
		apply existsb_exists. exists s. split.
		  apply all_traces_upto_complete; lia.
		apply andb_true_intro. split.
			now apply is_auth_bypass_correct.
	  now apply learned_encodes.
	- intros (n & Hn). unfold check_upto in Hn.
		apply existsb_exists in Hn. destruct Hn as (s & Hin & HAcc).
		apply andb_prop in HAcc. destruct HAcc.
		exists s. split.
		  now apply is_auth_bypass_correct.
		now apply learned_encodes.
Qed.
