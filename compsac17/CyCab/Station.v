Require Import refine.
Require Import parser.

(** The CyCab example *)

(********* the security of component Station ************)

Definition Station: IA := parse
"IA [s1,s2] (s1) [pos] [far, halt] []
[s1->(pos)s2, s2->(far)s1, s2->(halt)s1]".

(* SIR-GNNI at l: false *)
Definition Station_hid_l: IA :=
 IAutomaton.hiding Station (ASet.GenActs [&"pos"]).

Definition Station_res_l: IA :=
 IAutomaton.restriction Station (ASet.GenActs [&"pos"]).

Eval compute in :> Station_hid_l.
Eval compute in :> Station_res_l.
Eval compute in SIRGNNI_refinement Station_res_l Station_hid_l.

(* SME-NI at l: false *)
Definition Station_rep_l: IA :=
 IAutomaton.replacement Station (&"tau") (ASet.GenActs [&"pos"]).

Eval compute in :> Station_rep_l.
Eval compute in SMENI_refinement Station_rep_l Station_hid_l.