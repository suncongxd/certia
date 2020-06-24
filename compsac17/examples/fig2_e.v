(* Fig.2(e) of COMPSAC'17 paper *)

Require Export refine.
Require Export parser.
Require Export subsetconst.

Definition multS2: IA := parse
"IA [s1,s2,s3,s4,s5] (s1) [h1,h2] [m1,m2] []
[s1->(h1)s2, s1->(h2)s3, s2->(m1)s4, s3->(m2)s5]".

(******************** SIR-GNNI ****************)
(* SIR-GNNI at m1: false *)
Definition multS2_hid_m1: IA :=
  IAutomaton.hiding multS2 (ASet.GenActs [&"h1",&"h2",&"m2"]).

Definition multS2_res_m1: IA :=
  IAutomaton.hiding
  ( IAutomaton.restriction multS2 (ASet.GenActs [&"h1",&"h2"]) )
  (ASet.GenActs [&"m2"]).

Eval compute in :> multS2_hid_m1.
Eval compute in :> multS2_res_m1.
Eval compute in SIRGNNI_refinement multS2_res_m1 multS2_hid_m1.

(* SIR-GNNI at m2: false *)
Definition multS2_hid_m2: IA :=
  IAutomaton.hiding multS2 (ASet.GenActs [&"h1",&"h2",&"m1"]).

Definition multS2_res_m2: IA :=
  IAutomaton.hiding
  (IAutomaton.restriction multS2 (ASet.GenActs [&"h1",&"h2"]) )
  (ASet.GenActs [&"m1"]).

Eval compute in :> multS2_hid_m2.
Eval compute in :> multS2_res_m2.
Eval compute in SIRGNNI_refinement multS2_res_m2 multS2_hid_m2.

(* SIR-GNNI at l: true *)
Definition multS2_hid_l: IA :=
  IAutomaton.hiding multS2 (ASet.GenActs [&"h1",&"h2",&"m1",&"m2"]).

Definition multS2_res_l: IA :=
  IAutomaton.hiding
  (IAutomaton.restriction multS2 (ASet.GenActs [&"h1",&"h2"]) )
  (ASet.GenActs [&"m1",&"m2"]).

Eval compute in :> multS2_hid_l.
Eval compute in :> multS2_res_l.
Eval compute in SIRGNNI_refinement multS2_res_l multS2_hid_l.

(******************** SME-NI *******************************)

(*SME-NI at m1: false*)
Definition multS2_rep_m1: IA :=
 subset_construction
 (IAutomaton.hiding
  ( IAutomaton.replacement multS2 (&"tau") (ASet.GenActs [&"h1",&"h2"]) )
  (ASet.GenActs [&"m2"]) ).

Eval compute in :> multS2_rep_m1.
Eval compute in SMENI_refinement multS2_rep_m1 multS2_hid_m1.

(*SME-NI at m2: false*)
Definition multS2_rep_m2: IA :=
 subset_construction
 (IAutomaton.hiding
  ( IAutomaton.replacement multS2 (&"tau") (ASet.GenActs [&"h1",&"h2"]) )
  (ASet.GenActs [&"m1"]) ).

Eval compute in :> multS2_rep_m2.
Eval compute in SMENI_refinement multS2_rep_m2 multS2_hid_m2.

(*SME-NI at l: true*)
Definition multS2_rep_l: IA :=
 subset_construction
 (IAutomaton.hiding
  ( IAutomaton.replacement multS2 (&"tau") (ASet.GenActs [&"h1",&"h2"]) )
  (ASet.GenActs [&"m1",&"m2"]) ).

Eval compute in :> multS2_rep_l.
Eval compute in SMENI_refinement multS2_rep_l multS2_hid_l.
