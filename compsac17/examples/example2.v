(* Example 2 of COMPSAC'17 paper,
also see Fig.4 of Matias Lee's SCCC'10 paper  *)

Require Import parser.
Require Import refine.

Definition binS3: IA := parse
"IA [s1,s2,s3,s4,s5,s6] (s1) [h2] [h1,a] [e]
[s1->(h2)s2, s2->(e)s4, s4->(a)s6, s1->(h1)s3, s3->(a)s5]".

Definition binS3_hid_l: IA :=
  IAutomaton.hiding binS3 (ASet.GenActs [&"h1",&"h2"]).

Definition binS3_res_l: IA :=
  IAutomaton.hiding
  (IAutomaton.restriction binS3 (ASet.GenActs [&"h2"]))
  (ASet.GenActs [&"h1"]).

Definition binS3_rep_l: IA :=
  IAutomaton.hiding
  (IAutomaton.replacement binS3 (&"tau") (ASet.GenActs [&"h2"]))
  (ASet.GenActs [&"h1"]).

Eval compute in :> binS3_hid_l.
Eval compute in :> binS3_res_l.
Eval compute in :> binS3_rep_l.

(* SIR-GNNI: true *)
Eval compute in SIRGNNI_refinement binS3_res_l binS3_hid_l.

(* SME-NI: true *)
Eval compute in SMENI_refinement binS3_rep_l binS3_hid_l.