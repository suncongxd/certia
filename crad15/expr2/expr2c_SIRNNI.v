(*interface (c) to show the difference 
between SME-NI and the extended SIR-NNI*)

Require Export refine.
Require Export parser.

Definition expr2c: IA := parse
"IA [s1,s2,s3,s4] (s1) [m1,m2] [a,m1_] [] [s1->(m1)s2, s1->(m2)s3, s2->(a)s4, s3->(m1_)s4]".

(*at m1: false*)
Definition expr2c_m1_res: IA :=
  IAutomaton.restriction expr2c (ASet.GenActs [&"m2"]).

Definition expr2c_m1_hid: IA :=
  IAutomaton.hiding expr2c (ASet.GenActs [&"m2"]).

Eval compute in RNNI_refinement expr2c_m1_res expr2c_m1_hid.


(*at m2: false*)
Definition expr2c_m2_res: IA :=
  IAutomaton.hiding
  ( IAutomaton.restriction expr2c (ASet.GenActs [&"m1"]) )
  (ASet.GenActs [&"m1_"]).

Definition expr2c_m2_hid: IA :=
  IAutomaton.hiding expr2c (ASet.GenActs [&"m1",&"m1_"]).

Eval compute in RNNI_refinement expr2c_m2_res expr2c_m2_hid.


(*at l: false*)
Definition expr2c_l_res: IA :=
  IAutomaton.hiding
  ( IAutomaton.restriction expr2c (ASet.GenActs [&"m1",&"m2"]) )
  (ASet.GenActs [&"m1_"]).

Definition expr2c_l_hid: IA :=
  IAutomaton.hiding expr2c (ASet.GenActs [&"m1",&"m2",&"m1_"]).

Eval compute in RNNI_refinement expr2c_l_res expr2c_l_hid.
