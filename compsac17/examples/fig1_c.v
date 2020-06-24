(* Fig.1 (c) of COMPSAC'17 paper *)

Require Import refine.
Require Import parser.

Definition binS2: IA := parse
"IA [s1,s2,s3,s4] (s1) [h] [a,b,c] [] 
[s1->(h)s2, s1->(a)s3, s1->(b)s4, s2->(c)s4]".

Definition binS2_hid_l: IA :=
  IAutomaton.hiding binS2 (ASet.GenActs [&"h"]).

Definition binS2_res_l: IA :=
  IAutomaton.restriction binS2 (ASet.GenActs [&"h"]).

Definition binS2_rep_l: IA :=
  IAutomaton.replacement binS2 (&"tau") (ASet.GenActs [&"h"]).

Eval compute in :> binS2_hid_l.
Eval compute in :> binS2_res_l.
Eval compute in :> binS2_rep_l.

(* SIR-GNNI: false *)
Eval compute in (SIRGNNI_refinement binS2_res_l binS2_hid_l).

(* SME-NI: false *)
Eval compute in (SMENI_refinement binS2_rep_l binS2_hid_l).