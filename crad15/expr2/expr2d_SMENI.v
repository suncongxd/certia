(*interface (d) to show the difference 
between SME-NI and the extended SIR-NNI*)

Require Export refine.
Require Export parser.
Require Import subsetconst.

Definition expr2d: IA := parse
"IA [s1,s2,s3,s4] (s1) [m1,m2] [m2_,m1_] [] [s1->(m1)s2, s1->(m2)s3, s2->(m2_)s4, s3->(m1_)s4]".

(*at m1: false*)
Definition expr2d_m1_rep: IA :=
 IAutomaton.hiding
  ( IAutomaton.replacement expr2d (&"tau") (ASet.GenActs [&"m2"]) )
  (ASet.GenActs [&"m2_"]).

Definition expr2d_m1_hid: IA :=
  IAutomaton.hiding expr2d (ASet.GenActs [&"m2",&"m2_"]).

Eval compute in SMENI_refinement expr2d_m1_rep expr2d_m1_hid.

(*at m2: false*)
Definition expr2d_m2_rep: IA :=
  IAutomaton.hiding
  ( IAutomaton.replacement expr2d (&"tau") (ASet.GenActs [&"m1"]) )
  (ASet.GenActs [&"m1_"]).

Definition expr2d_m2_hid: IA :=
  IAutomaton.hiding expr2d (ASet.GenActs [&"m1",&"m1_"]).

Eval compute in SMENI_refinement expr2d_m2_rep expr2d_m2_hid.


(*at l: true*)
Definition expr2d_l_rep: IA :=
 subset_construction
 ( IAutomaton.hiding
 ( IAutomaton.replacement expr2d (&"tau") (ASet.GenActs [&"m1",&"m2"]) )
 (ASet.GenActs [&"m1_",&"m2_"]) ).
(*Eval compute in IAutomaton.display expr2d_l_rep.*)

Definition expr2d_l_hid: IA :=
  IAutomaton.hiding expr2d (ASet.GenActs [&"m1",&"m2",&"m1_",&"m2_"]).

Eval compute in SMENI_refinement expr2d_l_rep expr2d_l_hid.

