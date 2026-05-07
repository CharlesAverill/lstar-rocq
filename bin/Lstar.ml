open Bool
open Datatypes
open Language
open List
open ListDef
open Nat
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Lstar =
 functor (Coq_s:Symbol) ->
 functor (L:sig
  val member : Coq_s.string -> bool
 end) ->
 functor (T:sig
  module DFA :
   sig
    type t = { transition : (__ -> Coq_s.t -> __); initial : __;
               accept : (__ -> bool) }

    type state = __

    val transition : t -> state -> Coq_s.t -> state

    val initial : t -> state

    val accept : t -> state -> bool

    val run : t -> Coq_s.string -> state

    val accept_string : t -> Coq_s.string -> bool
   end

  val equiv_query : DFA.t -> Coq_s.string option
 end) ->
 struct
  type 'a coq_InS = __

  (** val coq_In_to_InS :
      'a1 -> 'a1 list -> ('a1 -> 'a1 -> sumbool) -> 'a1 coq_InS **)

  let rec coq_In_to_InS a l dec =
    match l with
    | Coq_nil -> assert false (* absurd case *)
    | Coq_cons (y, l0) ->
      let iHl = fun _ -> coq_In_to_InS a l0 dec in
      let s = dec y a in
      (match s with
       | Coq_left -> Obj.magic (Coq_inl __)
       | Coq_right -> Obj.magic (Coq_inr (iHl __)))

  type finite = Coq_s.string list

  (** val coq_T_equiv_dec :
      (Coq_s.string -> bool) -> Coq_s.string -> Coq_s.string -> finite ->
      sumbool **)

  let coq_T_equiv_dec _ u v x =
    let b =
      forallb (fun t0 -> eqb (L.member (app u t0)) (L.member (app v t0))) x
    in
    (match b with
     | Coq_true -> Coq_left
     | Coq_false -> Coq_right)

  type separable = __

  type closed = Coq_s.string -> Coq_s.t -> __ -> Coq_s.string

  (** val existsb_exists_set : ('a1 -> bool) -> 'a1 list -> 'a1 **)

  let rec existsb_exists_set f = function
  | Coq_nil -> assert false (* absurd case *)
  | Coq_cons (y, l0) ->
    let b = f y in
    (match b with
     | Coq_true -> y
     | Coq_false -> existsb_exists_set f l0)

  (** val closed_dec_witness :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> finite -> finite ->
      (closed, (Coq_s.string, (Coq_s.t, __) sigT) sigT) sum **)

  let closed_dec_witness _ t0 finQ finT =
    let o =
      find (fun pat ->
        let Coq_pair (q, a) = pat in
        negb
          (existsb (fun q' ->
            match coq_T_equiv_dec t0 (app q (Coq_cons (a, Coq_nil))) q' finT with
            | Coq_left -> Coq_true
            | Coq_right -> Coq_false) finQ))
        (list_prod finQ Coq_s.enum)
    in
    (match o with
     | Some p ->
       let Coq_pair (l, t1) = p in
       Coq_inr (Coq_existT (l, (Coq_existT (t1, __))))
     | None ->
       Coq_inl (fun q a _ ->
         existsb_exists_set (fun q' ->
           match coq_T_equiv_dec t0 (app q (Coq_cons (a, Coq_nil))) q' finT with
           | Coq_left -> Coq_true
           | Coq_right -> Coq_false) finQ))

  (** val closed_dec :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> finite -> finite ->
      (closed, __) sum **)

  let closed_dec q t0 x x0 =
    let s = closed_dec_witness q t0 x x0 in
    (match s with
     | Coq_inl c -> Coq_inl c
     | Coq_inr _ -> Coq_inr __)

  (** val delta :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> closed ->
      Coq_s.string -> Coq_s.t -> Coq_s.string **)

  let delta _ _ c q a =
    c q a __

  type coq_HypothesisDFA = { coq_Q : (Coq_s.string -> bool);
                             coq_T : (Coq_s.string -> bool); clos : closed;
                             fin_Q : finite; fin_T : finite }

  (** val coq_Q : coq_HypothesisDFA -> Coq_s.string -> bool **)

  let coq_Q h =
    h.coq_Q

  (** val coq_T : coq_HypothesisDFA -> Coq_s.string -> bool **)

  let coq_T h =
    h.coq_T

  (** val clos :
      coq_HypothesisDFA -> Coq_s.string -> Coq_s.t -> Coq_s.string **)

  let clos h q a =
    h.clos q a __

  (** val fin_Q : coq_HypothesisDFA -> finite **)

  let fin_Q h =
    h.fin_Q

  (** val fin_T : coq_HypothesisDFA -> finite **)

  let fin_T h =
    h.fin_T

  (** val make_dfa : coq_HypothesisDFA -> T.DFA.t **)

  let make_dfa h =
    let initial0 = Coq_nil in
    let transition0 = fun q a ->
      delta h.coq_Q h.coq_T (fun x x0 _ -> clos h x x0) q a
    in
    { T.DFA.transition = (Obj.magic transition0); T.DFA.initial =
    (Obj.magic initial0); T.DFA.accept = (Obj.magic L.member) }

  (** val str_upd :
      (Coq_s.string -> bool) -> Coq_s.string -> bool -> Coq_s.string -> bool **)

  let str_upd s k b s0 =
    match Coq_s.str_eq s0 k with
    | Coq_left -> b
    | Coq_right -> s s0

  (** val find_separable :
      coq_HypothesisDFA -> Coq_s.string -> (Coq_s.string, (Coq_s.string, (__,
      ((separable, finite) prod, finite) prod) prod) sigT) sigT **)

  let find_separable h w =
    let p = fun i -> T.DFA.run (make_dfa h) (firstn i w) in
    let exK =
      let correct_dec = fun i ->
        let b = L.member w in
        (match b with
         | Coq_true ->
           let b0 = L.member (app (Obj.magic p i) (skipn i w)) in
           (match b0 with
            | Coq_true -> Coq_left
            | Coq_false -> Coq_right)
         | Coq_false ->
           let b0 = L.member (app (Obj.magic p i) (skipn i w)) in
           (match b0 with
            | Coq_true -> Coq_right
            | Coq_false -> Coq_left))
      in
      let n = length w in
      let rec f = function
      | O -> assert false (* absurd case *)
      | S n1 ->
        let s = correct_dec n1 in
        (match s with
         | Coq_left -> n1
         | Coq_right -> f n1)
      in f n
    in
    let x =
      let o = nth_error w exK in
      (match o with
       | Some t0 -> t0
       | None -> assert false (* absurd case *))
    in
    Coq_existT ((app (Obj.magic p exK) (Coq_cons (x, Coq_nil))), (Coq_existT
    ((skipn (S exK) w), (Coq_pair (__, (Coq_pair ((Coq_pair (__,
    (let f = h.fin_Q in
     Coq_cons ((app (Obj.magic p exK) (Coq_cons (x, Coq_nil))), f)))),
    (let f = h.fin_T in Coq_cons ((skipn (S exK) w), f)))))))))

  (** val find_representative :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> finite -> finite ->
      Coq_s.string -> Coq_s.string sumor **)

  let find_representative q t0 finQ finT u =
    let o =
      find (fun q0 ->
        match bool_dec (q q0) Coq_true with
        | Coq_left ->
          (match coq_T_equiv_dec t0 u q0 finT with
           | Coq_left -> Coq_true
           | Coq_right -> Coq_false)
        | Coq_right -> Coq_false) finQ
    in
    (match o with
     | Some s -> Coq_inleft s
     | None -> Coq_inright)

  (** val close_step :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> Coq_s.t list ->
      Coq_s.t -> finite -> finite -> (Coq_s.string -> bool, (((((__, __) sum,
      separable) prod, finite) prod, __) prod, Coq_s.string) prod) sigT **)

  let close_step q t0 q0 a finQ finT =
    let s =
      find_representative q t0 finQ finT (app q0 (Coq_cons (a, Coq_nil)))
    in
    (match s with
     | Coq_inleft s0 ->
       Coq_existT (q, (Coq_pair ((Coq_pair ((Coq_pair ((Coq_pair ((Coq_inr
         __), __)), finQ)), __)), s0)))
     | Coq_inright ->
       Coq_existT ((str_upd q (app q0 (Coq_cons (a, Coq_nil))) Coq_true),
         (Coq_pair ((Coq_pair ((Coq_pair ((Coq_pair ((Coq_inl __), __)),
         (Coq_cons ((app q0 (Coq_cons (a, Coq_nil))), finQ)))), __)),
         (app q0 (Coq_cons (a, Coq_nil)))))))

  (** val not_closed_impl_distinguishable :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> finite -> finite ->
      (Coq_s.string, Coq_s.t) sigT **)

  let not_closed_impl_distinguishable q t0 qfin tfin =
    let s = closed_dec_witness q t0 qfin tfin in
    (match s with
     | Coq_inl _ -> assert false (* absurd case *)
     | Coq_inr s0 ->
       let Coq_existT (x, s1) = s0 in
       let Coq_existT (x0, _) = s1 in Coq_existT (x, x0))

  (** val union_closed_loop :
      nat -> (Coq_s.string -> bool) -> (Coq_s.string -> bool) ->
      (Coq_s.string -> bool) -> finite -> finite -> (Coq_s.string -> bool,
      (((closed, separable) prod, finite) prod, __) prod) sigT option **)

  let rec union_closed_loop n q q' t0 finT finQ' =
    match n with
    | O -> None
    | S n0 ->
      let s = closed_dec_witness q' t0 finQ' finT in
      (match s with
       | Coq_inl c ->
         Some (Coq_existT (q', (Coq_pair ((Coq_pair ((Coq_pair (c, __)),
           finQ')), __))))
       | Coq_inr s0 ->
         let Coq_existT (x, s1) = s0 in
         let Coq_existT (x0, _) = s1 in
         let s2 = close_step q' t0 x x0 finQ' finT in
         let Coq_existT (x1, p) = s2 in
         let Coq_pair (p0, _) = p in
         let Coq_pair (p1, _) = p0 in
         let Coq_pair (_, f) = p1 in
         let o = union_closed_loop n0 q x1 t0 finT f in
         (match o with
          | Some s3 ->
            let Coq_existT (x2, p2) = s3 in
            let Coq_pair (p3, _) = p2 in
            let Coq_pair (p4, f0) = p3 in
            let Coq_pair (c, _) = p4 in
            Some (Coq_existT (x2, (Coq_pair ((Coq_pair ((Coq_pair (c, __)),
            f0)), __))))
          | None -> None))

  (** val loop_terminates :
      nat -> (Coq_s.string -> bool) -> (Coq_s.string -> bool) ->
      (Coq_s.string -> bool) -> finite -> Coq_s.string list -> (Coq_s.string
      -> bool, (((closed, separable) prod, finite) prod, __) prod) sigT **)

  let rec loop_terminates n q q' t0 finQ' tl =
    match n with
    | O -> assert false (* absurd case *)
    | S n0 ->
      let s = closed_dec_witness q' t0 finQ' tl in
      (match s with
       | Coq_inl c ->
         Coq_existT (q', (Coq_pair ((Coq_pair ((Coq_pair (c, __)), finQ')),
           __)))
       | Coq_inr s0 ->
         let Coq_existT (x, s1) = s0 in
         let Coq_existT (x0, _) = s1 in
         let s2 = close_step q' t0 x x0 finQ' tl in
         let Coq_existT (x1, p) = s2 in
         let Coq_pair (p0, _) = p in
         let Coq_pair (p1, _) = p0 in
         let Coq_pair (_, f) = p1 in
         let s3 = loop_terminates n0 q x1 t0 f tl in
         let Coq_existT (x2, p2) = s3 in
         let Coq_pair (p3, _) = p2 in
         let Coq_pair (p4, f0) = p3 in
         let Coq_pair (c, _) = p4 in
         Coq_existT (x2, (Coq_pair ((Coq_pair ((Coq_pair (c, __)), f0)), __))))

  (** val union_closed :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> finite -> finite ->
      (Coq_s.string -> bool, (((closed, separable) prod, finite) prod, __)
      prod) sigT **)

  let union_closed q t0 finQ finT =
    let fuel = S (pow (S (S O)) (length finT)) in
    let s = loop_terminates fuel q q t0 finQ finT in
    let Coq_existT (x, p) = s in
    let Coq_pair (p0, _) = p in
    let Coq_pair (p1, f) = p0 in
    let Coq_pair (c, _) = p1 in
    Coq_existT (x, (Coq_pair ((Coq_pair ((Coq_pair (c, __)), f)), __)))

  (** val lstar : nat -> coq_HypothesisDFA -> T.DFA.t option **)

  let rec lstar fuel h =
    match fuel with
    | O -> None
    | S n ->
      let o = T.equiv_query (make_dfa h) in
      (match o with
       | Some s ->
         let s0 = find_separable h s in
         let Coq_existT (x, s1) = s0 in
         let Coq_existT (x0, p) = s1 in
         let Coq_pair (_, p0) = p in
         let Coq_pair (p1, f) = p0 in
         let Coq_pair (_, f0) = p1 in
         let q' = str_upd h.coq_Q x Coq_true in
         let t' = str_upd h.coq_T x0 Coq_true in
         let s2 = union_closed q' t' f0 f in
         let Coq_existT (x1, p2) = s2 in
         let Coq_pair (p3, _) = p2 in
         let Coq_pair (p4, f1) = p3 in
         let Coq_pair (c, _) = p4 in
         lstar n { coq_Q = x1; coq_T = t'; clos = c; fin_Q = f1; fin_T = f }
       | None -> Some (make_dfa h))
 end
