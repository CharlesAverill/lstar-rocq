type 'a coq_sig = 'a
(* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT = Coq_existT of 'a * 'p

type sumbool = Coq_left | Coq_right

type 'a sumor = Coq_inleft of 'a | Coq_inright
