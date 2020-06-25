(*this is the example for the difference between SME-NI and SIR-NNI*)

Require Export refine.
Require Export parser.

(** Fig.4 (b)(e) *)

Definition expr1b:IA := parse
"IA [s0,s1,s2] (s0) [h] [a,b] [] [s0->(h)s1, s1->(a)s2, s0->(b)s2]".

Definition expr1b_hid: IA :=
  (IAutomaton.hiding expr1b (ASet.GenActs [&"h"]) ).

Definition expr1b_res: IA :=
  IAutomaton.restriction expr1b (ASet.GenActs [&"h"]).

Eval compute in (RNNI_refinement expr1b_res expr1b_hid). (*false*)

