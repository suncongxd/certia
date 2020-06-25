(*interface (h) to show the difference 
between SME-NI and the extended SIR-NNI*)

Require Export refine.
Require Export parser.
Require Import subsetconst.

Definition expr2h: IA := parse
"IA [s1,s2,s3,s4,s5] (s1) [m2_,m1_] [m1,m2] []
 [s1->(m2_)s2, s1->(m1_)s3, s2->(m1)s4, s3->(m2)s5]".

(*at m1: false*)
Definition expr2h_m1_rep: IA := 
 IAutomaton.hiding 
 ( IAutomaton.replacement expr2h (&"tau") (ASet.GenActs [&"m2_"]) )
 (ASet.GenActs [&"m2"]).

Definition expr2h_m1_hid: IA :=
IAutomaton.hiding expr2h (ASet.GenActs [&"m2_",&"m2"]).

Eval compute in SMENI_refinement expr2h_m1_rep expr2h_m1_hid.


(*at m2: false*)
Definition expr2h_m2_rep: IA :=
 IAutomaton.hiding 
 ( IAutomaton.replacement expr2h (&"tau") (ASet.GenActs [&"m1_"]) )
 (ASet.GenActs [&"m1"]).

Definition expr2h_m2_hid: IA :=
IAutomaton.hiding expr2h (ASet.GenActs [&"m1_",&"m1"]).

Eval compute in SMENI_refinement expr2h_m2_rep expr2h_m2_hid.


(*at l: true *)
Definition expr2h_l_rep: IA :=
 subset_construction
 ( IAutomaton.hiding
 ( IAutomaton.replacement expr2h (&"tau") (ASet.GenActs [&"m2_",&"m1_"]) )
 (ASet.GenActs [&"m1",&"m2"]) ).
(*Eval compute in IAutomaton.display expr2h_l_rep.*)

Definition expr2h_l_hid: IA :=
 IAutomaton.hiding expr2h (ASet.GenActs [&"m2_",&"m1_",&"m1",&"m2"]).

Eval compute in SMENI_refinement expr2h_l_rep expr2h_l_hid.

