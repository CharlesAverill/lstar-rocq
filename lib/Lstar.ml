open Datatypes
open Language
open List
open ListLemmas
open Specif

type __ = Obj.t

let __ =
  let rec f _ = Obj.repr f in
  Obj.repr f

module Lstar =
functor
  (Coq_s : Symbol)
  (L : sig
     val member : Coq_s.string -> bool
   end)
  (T : sig
     module DFA : sig
       type 'state t =
         { transition: 'state -> Coq_s.t -> 'state
         ; initial: 'state
         ; accept: 'state -> bool }

       val transition : 'a1 t -> 'a1 -> Coq_s.t -> 'a1

       val initial : 'a1 t -> 'a1

       val accept : 'a1 t -> 'a1 -> bool

       val run : 'a1 t -> Coq_s.string -> 'a1

       val accept_string : 'a1 t -> Coq_s.string -> bool
     end

     val equiv_query : 'a1 DFA.t -> Coq_s.string option
   end)
  ->
  struct
    type 'a coq_InS = __

    (** val coq_In_to_InS :
      'a1 -> 'a1 list -> ('a1 -> 'a1 -> sumbool) -> 'a1 coq_InS **)

    let rec coq_In_to_InS a l dec =
      match l with
      | [] ->
          assert false (* absurd case *)
      | y :: l0 -> (
          let iHl = fun _ -> coq_In_to_InS a l0 dec in
          let s = dec y a in
          match s with
          | Coq_left ->
              Obj.magic (Coq_inl __)
          | Coq_right ->
              Obj.magic (Coq_inr (iHl __)) )

    type finite = Coq_s.string list

    (** val coq_T_equiv_dec :
      (Coq_s.string -> bool) -> Coq_s.string -> Coq_s.string -> finite ->
      sumbool **)

    let coq_T_equiv_dec _ u v x =
      let b =
        Stdlib.List.for_all (fun t0 -> L.member (u @ t0) = L.member (v @ t0)) x
      in
      if b then
        Coq_left
      else
        Coq_right

    type separable = __

    type closed = Coq_s.string -> Coq_s.t -> __ -> Coq_s.string

    (** val closed_dec_witness :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> finite -> finite ->
      (closed, (Coq_s.string, (Coq_s.t, __) sigT) sigT) sum **)

    let closed_dec_witness _ t0 finQ finT =
      let o =
        Stdlib.List.find_opt
          (fun pat ->
            let q, a = pat in
            not
              (Stdlib.List.exists
                 (fun q' ->
                   match coq_T_equiv_dec t0 (q @ (a :: [])) q' finT with
                   | Coq_left ->
                       true
                   | Coq_right ->
                       false )
                 finQ ) )
          (list_prod finQ Coq_s.enum)
      in
      match o with
      | Some p ->
          let l, t1 = p in
          Coq_inr (Coq_existT (l, Coq_existT (t1, __)))
      | None ->
          Coq_inl
            (fun q a _ ->
              existsb_exists_set
                (fun q' ->
                  match coq_T_equiv_dec t0 (q @ (a :: [])) q' finT with
                  | Coq_left ->
                      true
                  | Coq_right ->
                      false )
                finQ )

    (** val closed_dec :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> finite -> finite ->
      (closed, closed -> coq_Empty_set) sum **)

    let closed_dec q t0 x x0 =
      let s = closed_dec_witness q t0 x x0 in
      match s with
      | Coq_inl c ->
          Coq_inl c
      | Coq_inr _ ->
          Coq_inr (fun _ -> assert false (* absurd case *))

    (** val delta :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> closed ->
      Coq_s.string -> Coq_s.t -> Coq_s.string **)

    let delta _ _ c q a = c q a __

    type coq_HypothesisDFA =
      { coq_Q: Coq_s.string -> bool
      ; coq_T: Coq_s.string -> bool
      ; clos: closed
      ; fin_Q: finite
      ; fin_T: finite }

    (** val coq_Q : coq_HypothesisDFA -> Coq_s.string -> bool **)

    let coq_Q h = h.coq_Q

    (** val coq_T : coq_HypothesisDFA -> Coq_s.string -> bool **)

    let coq_T h = h.coq_T

    (** val clos :
      coq_HypothesisDFA -> Coq_s.string -> Coq_s.t -> Coq_s.string **)

    let clos h q a = h.clos q a __

    (** val fin_Q : coq_HypothesisDFA -> finite **)

    let fin_Q h = h.fin_Q

    (** val fin_T : coq_HypothesisDFA -> finite **)

    let fin_T h = h.fin_T

    (** val make_dfa : coq_HypothesisDFA -> Coq_s.string T.DFA.t **)

    let make_dfa h =
      let initial0 = [] in
      let transition0 =
       fun q a -> delta h.coq_Q h.coq_T (fun x x0 _ -> clos h x x0) q a
      in
      { T.DFA.transition= transition0
      ; T.DFA.initial= initial0
      ; T.DFA.accept= L.member }

    (** val str_upd :
      (Coq_s.string -> bool) -> Coq_s.string -> bool -> Coq_s.string -> bool **)

    let str_upd s k b s0 =
      match Coq_s.str_eq s0 k with Coq_left -> b | Coq_right -> s s0

    (** val find_separable :
      coq_HypothesisDFA -> Coq_s.string -> (Coq_s.string, (Coq_s.string,
      __*((separable*finite)*finite)) sigT) sigT **)

    let find_separable h w =
      let p = fun i -> T.DFA.run (make_dfa h) (Stdlib.List.take i w) in
      let exK =
        let correct_dec =
         fun i ->
          let b = L.member w in
          if b then
            let b0 = L.member (p i @ Stdlib.List.drop i w) in
            if b0 then
              Coq_left
            else
              Coq_right
          else
            let b0 = L.member (p i @ Stdlib.List.drop i w) in
            if b0 then
              Coq_right
            else
              Coq_left
        in
        let n = Stdlib.List.length w in
        let rec f n0 =
          (fun fO fS n ->
            if n = 0 then
              fO ()
            else
              fS (n - 1) )
            (fun _ -> assert false (* absurd case *))
            (fun n1 ->
              let s = correct_dec n1 in
              match s with Coq_left -> n1 | Coq_right -> f n1 )
            n0
        in
        f n
      in
      let x =
        let o = Stdlib.List.nth_opt w exK in
        match o with Some t0 -> t0 | None -> assert false (* absurd case *)
      in
      Coq_existT
        ( p exK @ (x :: [])
        , Coq_existT
            ( Stdlib.List.drop (succ exK) w
            , ( __
              , ( ( __
                  , let f = h.fin_Q in
                    (p exK @ (x :: [])) :: f )
                , let f = h.fin_T in
                  Stdlib.List.drop (succ exK) w :: f ) ) ) )

    (** val find_representative :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> finite -> finite ->
      Coq_s.string -> Coq_s.string sumor **)

    let find_representative q t0 finQ finT u =
      let o =
        Stdlib.List.find_opt
          (fun q0 ->
            if q q0 = true then
              match coq_T_equiv_dec t0 u q0 finT with
              | Coq_left ->
                  true
              | Coq_right ->
                  false
            else
              false )
          finQ
      in
      match o with Some s -> Coq_inleft s | None -> Coq_inright

    (** val close_step :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> Coq_s.t list ->
      Coq_s.t -> finite -> finite -> (Coq_s.string -> bool, ((((__, __)
      sum*separable)*finite)*__)*Coq_s.string) sigT **)

    let close_step q t0 q0 a finQ finT =
      let s = find_representative q t0 finQ finT (q0 @ (a :: [])) in
      match s with
      | Coq_inleft s0 ->
          Coq_existT (q, ((((Coq_inr __, __), finQ), __), s0))
      | Coq_inright ->
          Coq_existT
            ( str_upd q (q0 @ (a :: [])) true
            , ( (((Coq_inl __, __), (q0 @ (a :: [])) :: finQ), __)
              , q0 @ (a :: []) ) )

    (** val not_closed_impl_distinguishable :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> finite -> finite ->
      (Coq_s.string, Coq_s.t) sigT **)

    let not_closed_impl_distinguishable q t0 qfin tfin =
      let s = closed_dec_witness q t0 qfin tfin in
      match s with
      | Coq_inl _ ->
          assert false (* absurd case *)
      | Coq_inr s0 ->
          let (Coq_existT (x, s1)) = s0 in
          let (Coq_existT (x0, _)) = s1 in
          Coq_existT (x, x0)

    (** val union_closed_loop :
      int -> (Coq_s.string -> bool) -> (Coq_s.string -> bool) ->
      (Coq_s.string -> bool) -> finite -> finite -> (Coq_s.string -> bool,
      ((closed*separable)*finite)*__) sigT option **)

    let rec union_closed_loop n q q' t0 finT finQ' =
      (fun fO fS n ->
        if n = 0 then
          fO ()
        else
          fS (n - 1) )
        (fun _ -> None)
        (fun n0 ->
          let s = closed_dec_witness q' t0 finQ' finT in
          match s with
          | Coq_inl c ->
              Some (Coq_existT (q', (((c, __), finQ'), __)))
          | Coq_inr s0 -> (
              let (Coq_existT (x, s1)) = s0 in
              let (Coq_existT (x0, _)) = s1 in
              let s2 = close_step q' t0 x x0 finQ' finT in
              let (Coq_existT (x1, p)) = s2 in
              let p0, _ = p in
              let p1, _ = p0 in
              let _, f = p1 in
              let o = union_closed_loop n0 q x1 t0 finT f in
              match o with
              | Some s3 ->
                  let (Coq_existT (x2, p2)) = s3 in
                  let p3, _ = p2 in
                  let p4, f0 = p3 in
                  let c, _ = p4 in
                  Some (Coq_existT (x2, (((c, __), f0), __)))
              | None ->
                  None ) )
        n

    (** val loop_terminates :
      int -> (Coq_s.string -> bool) -> (Coq_s.string -> bool) ->
      (Coq_s.string -> bool) -> finite -> Coq_s.string list -> (Coq_s.string
      -> bool, ((closed*separable)*finite)*__) sigT **)

    let rec loop_terminates n q q' t0 finQ' tl =
      (fun fO fS n ->
        if n = 0 then
          fO ()
        else
          fS (n - 1) )
        (fun _ -> assert false (* absurd case *))
        (fun n0 ->
          let s = closed_dec_witness q' t0 finQ' tl in
          match s with
          | Coq_inl c ->
              Coq_existT (q', (((c, __), finQ'), __))
          | Coq_inr s0 ->
              let (Coq_existT (x, s1)) = s0 in
              let (Coq_existT (x0, _)) = s1 in
              let s2 = close_step q' t0 x x0 finQ' tl in
              let (Coq_existT (x1, p)) = s2 in
              let p0, _ = p in
              let p1, _ = p0 in
              let _, f = p1 in
              let s3 = loop_terminates n0 q x1 t0 f tl in
              let (Coq_existT (x2, p2)) = s3 in
              let p3, _ = p2 in
              let p4, f0 = p3 in
              let c, _ = p4 in
              Coq_existT (x2, (((c, __), f0), __)) )
        n

    (** val union_closed :
      (Coq_s.string -> bool) -> (Coq_s.string -> bool) -> finite -> finite ->
      (Coq_s.string -> bool, ((closed*separable)*finite)*__) sigT **)

    let union_closed q t0 finQ finT =
      let fuel =
        succ
          (let rec pow x n =
             if n = 0 then
               1
             else
               x * pow x (n - 1)
           in
           pow (succ (succ 0)) (Stdlib.List.length finT) )
      in
      let s = loop_terminates fuel q q t0 finQ finT in
      let (Coq_existT (x, p)) = s in
      let p0, _ = p in
      let p1, f = p0 in
      let c, _ = p1 in
      Coq_existT (x, (((c, __), f), __))

    (** val lstar_opt :
      int -> coq_HypothesisDFA -> (__, __ T.DFA.t) sigT option **)

    let rec lstar_opt fuel h =
      (fun fO fS n ->
        if n = 0 then
          fO ()
        else
          fS (n - 1) )
        (fun _ -> None)
        (fun n ->
          let o = T.equiv_query (make_dfa h) in
          match o with
          | Some s ->
              let s0 = find_separable h s in
              let (Coq_existT (x, s1)) = s0 in
              let (Coq_existT (x0, p)) = s1 in
              let _, p0 = p in
              let p1, f = p0 in
              let _, f0 = p1 in
              let q' = str_upd h.coq_Q x true in
              let t' = str_upd h.coq_T x0 true in
              let s2 = union_closed q' t' f0 f in
              let (Coq_existT (x1, p2)) = s2 in
              let p3, _ = p2 in
              let p4, f1 = p3 in
              let c, _ = p4 in
              lstar_opt n {coq_Q= x1; coq_T= t'; clos= c; fin_Q= f1; fin_T= f}
          | None ->
              Some (Coq_existT (__, Obj.magic make_dfa h)) )
        fuel
  end
