(* Fig.2(a) of COMPSAC'17 paper *)

Require Export refine.
Require Export parser.
Require Export subsetconst.

Definition multS1: IA := parse
"IA [s1,s2,s3,s4,s5] (s1) [m1,m2] [a,m1_] []
[s1->(m1)s2, s2->(a)s4, s1->(m2)s3, s3->(m1_)s5]".

(** ************** SIR-GNNI ************************)

(* SIR-GNNI at m1: false *)
Definition multS1_hid_m1: IA :=
 IAutomaton.hiding multS1 (ASet.GenActs [&"m2"]).

Definition multS1_res_m1: IA :=
 IAutomaton.restriction multS1 (ASet.GenActs [&"m2"]).

Eval compute in :> multS1_hid_m1.
Eval compute in :> multS1_res_m1.
Eval compute in SIRGNNI_refinement multS1_res_m1 multS1_hid_m1.

(* SIR-GNNI at m2: false *)
Definition multS1_hid_m2: IA :=
 IAutomaton.hiding multS1 (ASet.GenActs [&"m1",&"m1_"]).

Definition multS1_res_m2: IA :=
 IAutomaton.hiding
 (IAutomaton.restriction multS1 (ASet.GenActs [&"m1"]) )
 (ASet.GenActs [&"m1_"]).

Eval compute in :> multS1_hid_m2.
Eval compute in :> multS1_res_m2.
Eval compute in SIRGNNI_refinement multS1_res_m2 multS1_hid_m2.

(* SIR-GNNI at l: false *)
Definition multS1_hid_l: IA :=
 IAutomaton.hiding multS1 (ASet.GenActs [&"m1",&"m1_",&"m2"]).

Definition multS1_res_l: IA :=
 IAutomaton.hiding
 (IAutomaton.restriction multS1 (ASet.GenActs [&"m1",&"m2"]) )
 (ASet.GenActs [&"m1_"]).

Eval compute in :> multS1_hid_l.
Eval compute in :> multS1_res_l.
Eval compute in SIRGNNI_refinement multS1_res_l multS1_hid_l.

(****************** SME-NI ****************************)
(* SME-NI at m1: false *)
Definition multS1_hid_m1_: IA :=
 IAutomaton.hiding multS1 (ASet.GenActs [&"m2",&"a"]).

Definition multS1_rep_m1: IA :=
 IAutomaton.hiding
 (IAutomaton.replacement multS1 (&"tau") (ASet.GenActs [&"m2"]) )
 (ASet.GenActs [&"a"]).

Eval compute in :> multS1_hid_m1_.
Eval compute in :> multS1_rep_m1.
Eval compute in SMENI_refinement multS1_rep_m1 multS1_hid_m1_.

(* SME-NI at m2: true *)
Definition multS1_hid_m2_: IA :=
 IAutomaton.hiding multS1 (ASet.GenActs [&"m1",&"m1_",&"a"]).

Definition multS1_rep_m2: IA :=
 IAutomaton.hiding
 (IAutomaton.replacement multS1 (&"tau") (ASet.GenActs [&"m1"]) )
 (ASet.GenActs [&"a",&"m1_"]).

Eval compute in :> multS1_hid_m2_.
Eval compute in :> multS1_rep_m2.
Eval compute in SMENI_refinement multS1_rep_m2 multS1_hid_m2_.

(* SME-NI at l: false *)
Definition multS1_rep_l: IA :=
 subset_construction
 (IAutomaton.hiding
 (IAutomaton.replacement multS1 (&"tau") (ASet.GenActs [&"m1",&"m2"]) )
 (ASet.GenActs [&"m1_"]) ).

Eval compute in :> multS1_rep_l.
Eval compute in SMENI_refinement multS1_rep_l multS1_hid_l.

 






