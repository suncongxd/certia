(*interface (c) to show the difference 
between SME-NI and the extended SIR-NNI*)

Require Export refine.
Require Export parser.
Require Import subsetconst.

Definition expr2c: IA := parse
"IA [s1,s2,s3,s4] (s1) [m1,m2] [a,m1_] [] [s1->(m1)s2, s1->(m2)s3, s2->(a)s4, s3->(m1_)s4]".

(*at m1: false*)
Definition expr2c_m1_rep: IA :=
 IAutomaton.hiding
  ( IAutomaton.replacement expr2c (&"tau") (ASet.GenActs [&"m2"]) )
  (ASet.GenActs [&"a"]).

Definition expr2c_m1_hid: IA :=
  IAutomaton.hiding expr2c (ASet.GenActs [&"m2",&"a"]).

Eval compute in SMENI_refinement expr2c_m1_rep expr2c_m1_hid.


(*at m2: true*)
Definition expr2c_m2_rep: IA :=
  IAutomaton.hiding
  ( IAutomaton.replacement expr2c (&"tau") (ASet.GenActs [&"m1"]) )
  (ASet.GenActs [&"a",&"m1_"]).

Definition expr2c_m2_hid: IA :=
  IAutomaton.hiding expr2c (ASet.GenActs [&"m1",&"a",&"m1_"]).

Eval compute in SMENI_refinement expr2c_m2_rep expr2c_m2_hid.


(*at l: false*)
Definition expr2c_l_rep: IA :=
 subset_construction
 ( IAutomaton.hiding
 ( IAutomaton.replacement expr2c (&"tau") (ASet.GenActs [&"m1",&"m2"]) )
 (ASet.GenActs [&"m1_"]) ).
(*Eval compute in IAutomaton.display expr2c_l_rep.*)

Definition expr2c_l_hid: IA :=
  IAutomaton.hiding expr2c (ASet.GenActs [&"m1",&"m2",&"m1_"]).

Eval compute in SMENI_refinement expr2c_l_rep expr2c_l_hid.

