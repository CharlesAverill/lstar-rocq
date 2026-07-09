(* only_http.v

   Uses TTTto build a minimal DFA encoding a black-box packet firewall, then
   decides whether the firewall ever forwards a "bad" packet: an HTTP request whose
   destination port is not 80

   Provides:
     - [learned_dfa] : a DFA equivalent to [firewall]
     - [check_upto] : a verified executable decision procedure searching all
       packets up to a given length for a DFA-accepted bad packet

   Assumptions and limitations:
     - [firewall] is an arbitrary boolean packet classifier
     - A [FirewallTeacher] exists providing correct membership/equivalence
       oracles for [firewall] to the TTT learner
     - A minimal DFA recognizing the language of [firewall] exists within a
       known state bound
     - [is_http] detects only five literal ASCII method tokens
       ("GET ", "POST ", "HEAD ", "PUT ", "DELETE ") at the payload start, and
       is therefore not a general HTTP parser.
     - Packet validity is defined in terms of the HTTP parsing functions *)

From lstar Require Import TTT Automata Teacher.
From Stdlib Require Import Bool String List PeanoNat Lia.
Import ListNotations.

Definition Bit := bool.
Definition BitSequence := list Bit.
Definition Port := nat.

Module S <: Symbol.
    Definition t := Bit.
    Definition str := BitSequence.
    Definition eq_dec := bool_dec.

    Definition enum := [true; false].

    Theorem t_enumerable : forall (x : t), In x enum.
    Proof.
        intros. unfold enum. destruct x; compute; auto.
    Qed.

    Open Scope string_scope.
    Definition string_of_t t : String.string :=
        match t with
        | true => "true"
        | false => "false"
        end.
    Definition t_of_string (s : String.string) :=
        match s with
        | "true" => Ok true
        | "false" => Ok false
        | _ => Error s
        end.
    Close Scope string_scope.
End S.

Fixpoint bit_inc (bits : BitSequence) : BitSequence :=
  match bits with
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs  => false :: bit_inc bs
  end.

Fixpoint nat_to_bits_le (n : nat) : BitSequence :=
  match n with
  | O => []
  | S m => bit_inc (nat_to_bits_le m)
  end.

Definition nat_to_bits (n : nat) : BitSequence :=
  match n with
  | O => [false]
  | S _ => rev (nat_to_bits_le n)
  end.

Fixpoint bits_to_nat_le (bits : BitSequence) : nat :=
  match bits with
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bits_to_nat_le bs
  end.

Fixpoint bits_to_nat_acc (bits : BitSequence) (acc : nat) : nat :=
  match bits with
  | [] => acc
  | b :: bs => bits_to_nat_acc bs ((acc * 2) + (if b then 1 else 0))
  end.

Definition bits_to_nat (bits : BitSequence) : nat :=
  bits_to_nat_acc bits 0.

Lemma bits_to_nat_le_inc : forall bits,
    bits_to_nat_le (bit_inc bits) = S (bits_to_nat_le bits).
Proof.
    induction bits.
        reflexivity.
    destruct a; simpl; lia.
Qed.

Lemma nat_to_bits_le_correct : forall n,
    bits_to_nat_le (nat_to_bits_le n) = n.
Proof.
    induction n.
        reflexivity.
    simpl. rewrite bits_to_nat_le_inc. now rewrite IHn.
Qed.

Lemma bits_to_nat_acc_rev : forall bits acc,
    bits_to_nat_acc (rev bits) acc = acc * (2 ^ length bits) + bits_to_nat_le bits.
Proof.
    induction bits; intros; simpl in *.
        lia.
    assert (H_app : forall l x a, bits_to_nat_acc (l ++ [x]) a = 
                        bits_to_nat_acc l a * 2 + (if x then 1 else 0)).
        clear. induction l; intros; simpl. lia. now rewrite IHl.
    rewrite H_app, IHbits. lia.
Qed.

Theorem nat_to_bits_correct : forall n,
    bits_to_nat (nat_to_bits n) = n.
Proof.
    intros. destruct n.
        reflexivity.
    unfold bits_to_nat, nat_to_bits.
    rewrite bits_to_nat_acc_rev, nat_to_bits_le_correct.
    lia.
Qed.

Definition take {X} := @firstn X.
Definition drop {X} := @skipn X.

Definition get_port_from_packet (packet : BitSequence) : option Port :=
  (* Skip the Ethernet Header (14 bytes) *)
  let ip_packet := drop 112 packet in
  
  (* Parse the IPv4 Header Length *)
  let version_ihl := take 8 ip_packet in
  match length version_ihl with
  | 8 =>
      (* Extract the lower 4 bits of the first byte for IHL *)
      let ihl_bits := drop 4 version_ihl in
      
      (* Convert 4-bit IHL to a number of 32-bit words *)
      let ihl_words := bits_to_nat ihl_bits in
      (* Enforce valid IPv4 bounds: IHL must be between 5 and 15 words *)
      if (5 <=? ihl_words) && (ihl_words <=? 15) then
        let ip_header_bits := ihl_words * 32 in
        let transport_layer := drop ip_header_bits ip_packet in
        let dest_port_bits := take 16 (drop 16 transport_layer) in
        if Nat.eqb (length dest_port_bits) 16 then
          Some (bits_to_nat dest_port_bits)
        else None (* packet too short *)
      else None (* invalid header *)
  | _ => None
  end.

(* A firewall takes a packet and returns

   [true]  : the packet is forwarded
   [false] : the packet is dropped *)
Axiom firewall : BitSequence -> bool.

Module FirewallLang <: RegularLanguage S.
    Module D := DFA S.
    Definition member : S.str -> bool := firewall.

    Definition encodes {state : Type} (dfa : D.t state) : Prop :=
        forall s, member s = true <-> D.accept_string dfa s = true.
    Definition minimal {state : Type} (dfa : D.t state) : Prop :=
        encodes dfa /\
        forall (state' : Type) (dfa' : D.t state'),
            encodes dfa' ->
            List.length (D.states state dfa) <= List.length (D.states state' dfa').

    Parameter num_states_in_minimal : nat.
    Parameter exists_dfa : exists state (d : D.t state),
        minimal d /\ List.length (D.states state d) <= num_states_in_minimal.
End FirewallLang.

(* Assume that a teacher exists *)
Declare Module FirewallTeacher : DFATeacher S FirewallLang.

Module Learner := TTT S FirewallLang FirewallTeacher.

Import FirewallLang.

Definition learned : { St : Type & { d : D.t St | minimal d } } :=
    Learner.ttt tt.

Definition LSt : Type := projT1 learned.
Definition learned_dfa : D.t LSt := proj1_sig (projT2 learned).

Lemma learned_minimal : minimal learned_dfa.
Proof. exact (proj2_sig (projT2 learned)). Qed.

(* The learned DFA accepts exactly the forwarded packets. *)
Lemma learned_encodes : forall s,
    firewall s = true <-> D.accept_string learned_dfa s = true.
Proof. intros. destruct learned_minimal as (Henc & _). apply (Henc s). Qed.

(* Decide whether a packet is an HTTP packet *)
Section IsHTTP.
    Definition byte_at (bits : BitSequence) (n : nat) : option nat :=
        let b := take 8 (drop n bits) in
        if Nat.eqb (length b) 8 then Some (bits_to_nat b) else None.

    (* Read k bytes starting at bit offset [off] *)
    Fixpoint bytes_at (bits : BitSequence) (off k : nat) : option (list nat) :=
        match k with
        | O => Some []
        | S k' =>
            match byte_at bits off with
            | None => None
            | Some c =>
                match bytes_at bits (off + 8) k' with
                | None => None
                | Some cs => Some (c :: cs)
                end
            end
        end.

    (* ASCII codes. *)
    Definition ascii_G := 71.  Definition ascii_E := 69.  Definition ascii_T := 84.
    Definition ascii_P := 80.  Definition ascii_O := 79.  Definition ascii_S := 83.
    Definition ascii_H := 72.  Definition ascii_A := 65.  Definition ascii_D := 68.
    Definition ascii_U := 85.  Definition ascii_L := 76.  Definition ascii_SP := 32.

    Definition list_nat_eqb l1 l2 :=
        if list_eq_dec Nat.eq_dec l1 l2 then true else false.

    Definition http_tokens : list (list nat) :=
        [ [ascii_G; ascii_E; ascii_T; ascii_SP] ;                           (* "GET "    *)
        [ascii_P; ascii_O; ascii_S; ascii_T; ascii_SP] ;                    (* "POST "   *)
        [ascii_H; ascii_E; ascii_A; ascii_D; ascii_SP] ;                    (* "HEAD "   *)
        [ascii_P; ascii_U; ascii_T; ascii_SP] ;                             (* "PUT "    *)
        [ascii_D; ascii_E; ascii_L; ascii_E; ascii_T; ascii_E; ascii_SP]    (* "DELETE " *)
        ].

    (* Does the payload beginning at bit offset [off] start with an HTTP method token? *)
    Definition payload_is_http (bits : BitSequence) (off : nat) : bool :=
        existsb (fun tok =>
                match bytes_at bits off (length tok) with
                | Some cs => list_nat_eqb cs tok
                | None => false
                end)
                http_tokens.

    (* Locate the payload and test it *)
    Definition is_http (packet : BitSequence) : bool :=
        let ip_packet := drop 112 packet in
        let version_ihl := take 8 ip_packet in
        match length version_ihl with
        | 8 =>
            let ihl_words := bits_to_nat (drop 4 version_ihl) in
            if (5 <=? ihl_words) && (ihl_words <=? 15) then
            let ip_header_bits := ihl_words * 32 in
            let tcp := drop ip_header_bits ip_packet in
            let doff_bits := take 4 (drop 96 tcp) in
            if Nat.eqb (length doff_bits) 4 then
                let doff_words := bits_to_nat doff_bits in
                if (5 <=? doff_words) && (doff_words <=? 15) then
                let tcp_header_bits := doff_words * 32 in
                let payload_off := ip_header_bits + tcp_header_bits in
                payload_is_http ip_packet payload_off
                else false
            else false
            else false
        | _ => false
        end.
End IsHTTP.

Section BadPackets.
    (* A packet is "bad" if it is an HTTP request whose destination port is not 80 *)
    Definition bad_packet (s : BitSequence) : Prop :=
        is_http s = true /\ get_port_from_packet s <> Some 80.

    (* Decide whether a packet is bad *)
    Definition bad_packet_dec (s : BitSequence) : bool :=
        is_http s &&
        (match get_port_from_packet s with
        | Some p => negb (Nat.eqb p 80)
        | None => true
        end).

    Lemma bad_packet_dec_correct : forall s,
        bad_packet_dec s = true <-> bad_packet s.
    Proof.
        intros. unfold bad_packet_dec, bad_packet. split.
        - intros. apply andb_prop in H. destruct H.
        split. assumption.
        destruct get_port_from_packet eqn:E; [|discriminate].
            intro Contra. inversion Contra; subst.
            now rewrite Nat.eqb_refl in H0.
        - intros. destruct H. rewrite H. simpl.
        destruct get_port_from_packet eqn:E; [|reflexivity].
        apply Bool.negb_true_iff, Nat.eqb_neq. intro. subst. contradiction.
    Qed.

    (* [firweall] allows bad packets through *)
    Definition firewall_allows_bad : Prop :=
        exists s, bad_packet s /\ firewall s = true.
End BadPackets.

Section AnalyzeDFA.
    (* All bit sequences of length exactly n *)
    Fixpoint all_bitseqs (n : nat) : list BitSequence :=
        match n with
        | O => [[]]
        | S m => let prev := all_bitseqs m in
                map (cons true) prev ++ map (cons false) prev
        end.

    (* All bit sequences of length at most n *)
    Fixpoint all_bitseqs_upto (n : nat) : list BitSequence :=
        match n with
        | O => [[]]
        | S m => all_bitseqs (S m) ++ all_bitseqs_upto m
        end.

    Lemma all_bitseqs_complete : forall s, In s (all_bitseqs (length s)).
    Proof.
        induction s; simpl.
            now left.
        apply in_or_app. destruct a; [left|right];
            now apply in_map.
    Qed.

    Lemma all_bitseqs_upto_complete : forall n s,
        length s <= n -> In s (all_bitseqs_upto n).
    Proof.
        induction n; intros.
            destruct s. now left. inversion H.
        cbn [all_bitseqs_upto]. apply in_or_app.
        destruct (Nat.eq_dec (length s) (S n)).
            left. rewrite <- e. apply all_bitseqs_complete.
            right. apply IHn. lia.
    Qed.

    (* Decide if there exists a bad packet of length <= n accepted by the DFA? *)
    Definition check_upto (n : nat) : bool :=
        existsb (fun s => bad_packet_dec s && D.accept_string learned_dfa s)
                (all_bitseqs_upto n).

    (* A firewall vulnerability always yields a positive verdict for large-engouh [n] *)
    Theorem checker_correct :
        firewall_allows_bad <-> exists n, check_upto n = true.
    Proof.
        split.
        - intros (s & Hbad & Hfw).
          exists (length s). unfold check_upto.
          apply existsb_exists. exists s. split.
            apply all_bitseqs_upto_complete. lia.
          apply andb_true_intro. split.
            now apply bad_packet_dec_correct.
          now apply learned_encodes.
        - intros (n & Hbad). unfold check_upto in Hbad.
          apply existsb_exists in Hbad. destruct Hbad as (s & Ins & BPDs).
          exists s. apply andb_prop in BPDs. destruct BPDs. split.
            now apply bad_packet_dec_correct.
          now apply learned_encodes. 
    Qed.
End AnalyzeDFA.
