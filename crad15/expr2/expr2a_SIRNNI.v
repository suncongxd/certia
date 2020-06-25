(*interface (a) to show the difference 
between SME-NI and the extended SIR-NNI*)

Require Export refine.
Require Export parser.

Definition expr2a: IA := parse
"IA [s1,s2,s3,s4] (s1) [m1,m2] [a,b] [] [s1->(m1)s2, s1->(m2)s3, s2->(a)s4, s3->(b)s4]".

(*at m1: false*)
Definition expr2a_m1_res: IA :=
  IAutomaton.restriction expr2a (ASet.GenActs [&"m2"]).

Definition expr2a_m1_hid: IA :=
  IAutomaton.hiding expr2a (ASet.GenActs [&"m2"]).

Eval compute in RNNI_refinement expr2a_m1_res expr2a_m1_hid.


(*at m2: false*)
Definition expr2a_m2_res: IA :=
  IAutomaton.restriction expr2a (ASet.GenActs [&"m1"]).

Definition expr2a_m2_hid: IA :=
  IAutomaton.hiding expr2a (ASet.GenActs [&"m1"]).

Eval compute in RNNI_refinement expr2a_m2_res expr2a_m2_hid.


(*at l: false*)
Definition expr2a_l_res: IA :=
  IAutomaton.restriction expr2a (ASet.GenActs [&"m1",&"m2"]).

Definition expr2a_l_hid: IA :=
  IAutomaton.hiding expr2a (ASet.GenActs [&"m1",&"m2"]).

Eval compute in RNNI_refinement expr2a_l_res expr2a_l_hid.
