(*this is the example for the difference between SME-NI and SIR-NNI*)

Require Export refine.
Require Export parser.

(** Fig.4(a)(d) *)

Definition expr1a:IA := parse
"IA [s0,s1,s2] (s0) [h] [a] [] [s0->(h)s1, s1->(a)s2, s0->(a)s2]".


Definition expr1a_hid: IA :=
  (IAutomaton.hiding expr1a (ASet.GenActs [&"h"]) ).

Definition expr1a_res := 
  IAutomaton.restriction expr1a (ASet.GenActs [&"h"]).

Eval compute in (RNNI_refinement expr1a_res expr1a_hid). (*true*)


