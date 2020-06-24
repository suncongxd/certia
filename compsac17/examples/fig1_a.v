(* Fig.1(a) of COMPSAC'17 paper *)

Require Import refine.
Require Import parser.

Definition binS1: IA := parse 
"IA [s1,s2,s3,s4] (s1) [h] [a,b] [] 
[s1->(h)s2, s2->(b)s4, s1->(b)s4, s1->(a)s3]".

Definition binS1_rep_l: IA := 
  IAutomaton.replacement binS1 (&"tau") (ASet.GenActs [&"h"]).

Definition binS1_hid_l: IA :=
  IAutomaton.hiding binS1 (ASet.GenActs [&"h"]).

Definition binS1_res_l: IA :=
  IAutomaton.restriction binS1 (ASet.GenActs [&"h"]).

Eval compute in :> binS1_rep_l.
Eval compute in :> binS1_hid_l.
Eval compute in :> binS1_res_l.

(* SIR-GNNI: true *)
Eval compute in (SIRGNNI_refinement binS1_res_l binS1_hid_l).

(* SME-NI: true *)
Eval compute in (SMENI_refinement binS1_rep_l binS1_hid_l).

