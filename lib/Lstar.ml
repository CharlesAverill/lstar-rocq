open Datatypes
open Language
open List
open ListLemmas
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
    type 'state t = { transition : ('state -> Coq_s.t -> 'state);
                      initial : 'state; accept : ('state -> bool) }

    val transition : 'a1 t -> 'a1 -> Coq_s.t -> 'a1

    val initial : 'a1 t -> 'a1

    val accept : 'a1 t -> 'a1 -> bool

    val run : 'a1 t -> Coq_s.string -> 'a1

    val accept_string : 'a1 t -> Coq_s.string -> bool
   end

  val equiv_query : 'a1 DFA.t -> Coq_s.string option
 end) ->
 struct
  type 'a coq_InS = __

  (** val coq_In_to_InS :
      'a1 -> 'a1 list -> ('a1 -> 'a1 -> sumbool) -> 'a1 coq_InS **)

  let coq_In_to_InS a l dec =
    let rec f = function
    | [] -> (fun _ _ -> assert false (* absurd case *))
    | y::l1 ->
      (fun dec0 _ ->
        match dec0 y a with
        | Coq_left -> Obj.magic (Coq_inl __)
        | Coq_right -> Obj.magic (Coq_inr (f l1 dec0 __)))
    in f l dec __

  type finite = Coq_s.string list

  (** val coq_T_equiv_dec :
      (Coq_s.string -> bool) -> Coq_s.string -> Coq_s.string -> finite ->
      sumbool **)

  let coq_T_equiv_dec _ u v x =
    (if Stdlib.List.for_all (fun t0 ->
          if (=) (L.member ((@) u t0)) (L.member ((@) v t0))
          then true
          else false) x
     then (fun _ -> Coq_left)
     else (fun _ -> Coq_right)) __

  type separable = __

  type closed = Coq_s.string -> Coq_s.t -> __ -> Coq_s.string

  (** val closed_dec_witness :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> finite -> finite ->
      (closed, (Coq_s.string, (Coq_s.t, __) sigT) sigT) sum **)

  let closed_dec_witness _ t0 finQ finT =
    (match Stdlib.List.find_opt (fun pat ->
             let q,a = pat in
             not
               (Stdlib.List.exists (fun q' ->
                 match coq_T_equiv_dec t0 ((@) q (a::[])) q' finT with
                 | Coq_left -> true
                 | Coq_right -> false) finQ))
             (list_prod finQ Coq_s.enum) with
     | Some p ->
       (fun _ ->
         (let l,t1 = p in
          (fun _ -> Coq_inr (Coq_existT (l, (Coq_existT (t1, __)))))) __)
     | None ->
       (fun _ -> Coq_inl (fun q a _ ->
         existsb_exists_set (fun q' ->
           match coq_T_equiv_dec t0 ((@) q (a::[])) q' finT with
           | Coq_left -> true
           | Coq_right -> false) finQ)))
      __

  (** val closed_dec :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> finite -> finite ->
      (closed, closed -> coq_Empty_set) sum **)

  let closed_dec q t0 x x0 =
    match closed_dec_witness q t0 x x0 with
    | Coq_inl c -> Coq_inl c
    | Coq_inr s ->
      Coq_inr (fun _ ->
        let Coq_existT (_, s0) = s in
        let Coq_existT (_, _) = s0 in assert false (* absurd case *))

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

  (** val make_dfa : coq_HypothesisDFA -> Coq_s.string T.DFA.t **)

  let make_dfa h =
    { T.DFA.transition = (fun q a ->
      delta h.coq_Q h.coq_T (fun x x0 _ -> clos h x x0) q a); T.DFA.initial =
      []; T.DFA.accept = L.member }

  (** val str_upd :
      (Coq_s.string -> bool) -> Coq_s.string -> bool -> Coq_s.string -> bool **)

  let str_upd s k b s0 =
    match Coq_s.str_eq s0 k with
    | Coq_left -> b
    | Coq_right -> s s0

  (** val find_separable :
      coq_HypothesisDFA -> Coq_s.string -> (Coq_s.string, (Coq_s.string,
      __*((separable*finite)*finite)) sigT) sigT **)

  let find_separable h w =
    let p = fun i -> T.DFA.run (make_dfa h) (Stdlib.List.take i w) in
    let exK =
      let rec f n =
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ _ -> assert false (* absurd case *))
          (fun n0 _ ->
          match (if L.member w
                 then (fun _ _ _ ->
                        if L.member ((@) (p n0) (Stdlib.List.drop n0 w))
                        then (if true
                              then (fun x ->
                                     if x then Coq_left else Coq_right)
                              else (fun x ->
                                     if x then Coq_right else Coq_left))
                               true
                        else (if false
                              then (fun x ->
                                     if x then Coq_left else Coq_right)
                              else (fun x ->
                                     if x then Coq_right else Coq_left))
                               true)
                 else (fun _ _ _ ->
                        if L.member ((@) (p n0) (Stdlib.List.drop n0 w))
                        then (if true
                              then (fun x ->
                                     if x then Coq_left else Coq_right)
                              else (fun x ->
                                     if x then Coq_right else Coq_left))
                               false
                        else (if false
                              then (fun x ->
                                     if x then Coq_left else Coq_right)
                              else (fun x ->
                                     if x then Coq_right else Coq_left))
                               false))
                  __ __ __ with
          | Coq_left -> n0
          | Coq_right -> f n0 __)
          n
      in f (Stdlib.List.length w) __
    in
    let x =
      (match Stdlib.List.nth_opt w exK with
       | Some t0 -> (fun _ -> t0)
       | None -> (fun _ -> assert false (* absurd case *))) __
    in
    Coq_existT (((@) (p exK) (x::[])), (Coq_existT
    ((Stdlib.List.drop (succ exK) w),
    (let Coq_existT (_, _) = nth_error_split_sig w exK x in
     __,((__,(((@) (p exK) (x::[]))::h.fin_Q)),((Stdlib.List.drop (succ exK)
                                                  w)::h.fin_T))))))

  (** val find_representative :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> finite -> finite ->
      Coq_s.string -> Coq_s.string sumor **)

  let find_representative q t0 finQ finT u =
    (match Stdlib.List.find_opt (fun q0 ->
             if (=) (q q0) true
             then (match coq_T_equiv_dec t0 u q0 finT with
                   | Coq_left -> true
                   | Coq_right -> false)
             else false) finQ with
     | Some s -> (fun _ -> Coq_inleft s)
     | None -> (fun _ -> Coq_inright)) __

  (** val close_step :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> Coq_s.t list ->
      Coq_s.t -> finite -> finite -> (Coq_s.string -> bool, ((((__, __)
      sum*separable)*finite)*__)*Coq_s.string) sigT **)

  let close_step q t0 q0 a finQ finT =
    match find_representative q t0 finQ finT ((@) q0 (a::[])) with
    | Coq_inleft s -> Coq_existT (q, (((((Coq_inr __),__),finQ),__),s))
    | Coq_inright ->
      Coq_existT ((str_upd q ((@) q0 (a::[])) true), (((((Coq_inl
        __),__),(((@) q0 (a::[]))::finQ)),__),((@) q0 (a::[]))))

  (** val not_closed_impl_distinguishable :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> finite -> finite ->
      (Coq_s.string, Coq_s.t) sigT **)

  let not_closed_impl_distinguishable q t0 qfin tfin =
    match closed_dec_witness q t0 qfin tfin with
    | Coq_inl _ -> assert false (* absurd case *)
    | Coq_inr s ->
      let Coq_existT (x, s0) = s in
      let Coq_existT (x0, _) = s0 in Coq_existT (x, x0)

  (** val union_closed_loop :
      int -> (Coq_s.string -> bool) -> (Coq_s.string -> bool) ->
      (Coq_s.string -> bool) -> finite -> finite -> (Coq_s.string -> bool,
      ((closed*separable)*finite)*__) sigT option **)

  let union_closed_loop n q q' t0 finT finQ' =
    let rec f n0 =
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ _ _ _ _ _ _ _ -> None)
        (fun n1 q0 q'0 t1 _ finT0 finQ'0 _ ->
        match closed_dec_witness q'0 t1 finQ'0 finT0 with
        | Coq_inl c -> Some (Coq_existT (q'0, (((c,__),finQ'0),__)))
        | Coq_inr s ->
          let Coq_existT (x, s0) = s in
          let Coq_existT (x0, _) = s0 in
          let Coq_existT (x1, p) = close_step q'0 t1 x x0 finQ'0 finT0 in
          let p0,s1 = p in
          (let p1,_ = p0 in
           (let p2,f0 = p1 in
            (let _,_ = p2 in
             (fun finQ'' _ _ ->
             match f n1 q0 x1 t1 __ finT0 finQ'' __ with
             | Some s2 ->
               let Coq_existT (x2, p3) = s2 in
               let p4,_ = p3 in
               (let p5,f1 = p4 in
                (let c,_ = p5 in
                 (fun finQ''' _ -> Some (Coq_existT (x2,
                 (((c,__),finQ'''),__))))) f1) __
             | None -> None)) f0) __)
            s1)
        n0
    in f n q q' t0 __ finT finQ' __

  (** val loop_terminates :
      int -> (Coq_s.string -> bool) -> (Coq_s.string -> bool) ->
      (Coq_s.string -> bool) -> finite -> Coq_s.string list -> (Coq_s.string
      -> bool, ((closed*separable)*finite)*__) sigT **)

  let loop_terminates n q q' t0 finQ' tl =
    let rec f n0 =
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ _ _ _ _ _ _ _ _ -> assert false
        (* absurd case *))
        (fun n1 q0 q'0 _ q'l _ _ _ _ ->
        match closed_dec_witness q'0 t0 q'l tl with
        | Coq_inl c -> Coq_existT (q'0, (((c,__),q'l),__))
        | Coq_inr s ->
          let Coq_existT (x, s0) = s in
          let Coq_existT (x0, _) = s0 in
          let Coq_existT (x1, p) = close_step q'0 t0 x x0 q'l tl in
          let p0,s1 = p in
          (let p1,_ = p0 in
           (let p2,f0 = p1 in
            (let _,_ = p2 in
             (fun finQ'' _ _ ->
             (let Coq_existT (x2, p3) = f n1 q0 x1 __ finQ'' __ __ __ __ in
              let p4,_ = p3 in
              (let p5,f1 = p4 in
               (let c,_ = p5 in
                (fun fin''' _ _ -> Coq_existT (x2, (((c,__),fin'''),__)))) f1)
                __)
               __))
              f0)
             __)
            s1)
        n0
    in f n q q' __ finQ' __ __ __ __

  (** val union_closed :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> finite -> finite ->
      (Coq_s.string -> bool, ((closed*separable)*finite)*__) sigT **)

  let union_closed q t0 finQ finT =
    (let Coq_existT (x, p) =
       loop_terminates (succ
         (let rec pow x n =
    if n = 0 then 1
    else x * pow x (n - 1)
   in pow
           (succ (succ 0)) (Stdlib.List.length finT)))
         q q t0 finQ finT
     in
     let p0,_ = p in
     (let p1,f = p0 in
      (let c,_ = p1 in (fun finQ' _ _ -> Coq_existT (x, (((c,__),finQ'),__))))
        f)
       __)
      __

  (** val lstar_opt :
      int -> coq_HypothesisDFA -> ((__, __ T.DFA.t) sigT, (__, __ T.DFA.t)
      sigT) result **)

  let rec lstar_opt fuel h =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Error (Coq_existT (__, (Obj.magic make_dfa h))))
      (fun n ->
      (match T.equiv_query (make_dfa h) with
       | Some s ->
         (fun _ ->
           let Coq_existT (x, s0) = find_separable h s in
           let Coq_existT (x0, p) = s0 in
           let _,p0 = p in
           let p1,f = p0 in
           (let _,f0 = p1 in
            (fun finT' ->
            let t' = str_upd h.coq_T x0 true in
            let Coq_existT (x1, p2) =
              union_closed (str_upd h.coq_Q x true) t' f0 finT'
            in
            let p3,_ = p2 in
            (let p4,f1 = p3 in
             (let c,_ = p4 in
              (fun finQ'' _ ->
              lstar_opt n { coq_Q = x1; coq_T = t'; clos = c; fin_Q = finQ'';
                fin_T = finT' }))
               f1)
              __))
             f)
       | None -> (fun _ -> Ok (Coq_existT (__, (Obj.magic make_dfa h))))) __)
      fuel
 end
