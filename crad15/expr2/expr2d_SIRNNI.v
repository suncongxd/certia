(*interface (d) to show the difference 
between SME-NI and the extended SIR-NNI*)

Require Export refine.
Require Export parser.

Definition expr2d: IA := parse
"IA [s1,s2,s3,s4] (s1) [m1,m2] [m2_,m1_] [] [s1->(m1)s2, s1->(m2)s3, s2->(m2_)s4, s3->(m1_)s4]".

(*at m1: false*)
Definition expr2d_m1_res: IA :=
 IAutomaton.hiding
  ( IAutomaton.restriction expr2d (ASet.GenActs [&"m2"]) )
  (ASet.GenActs [&"m2_"]).

Definition expr2d_m1_hid: IA :=
  IAutomaton.hiding expr2d (ASet.GenActs [&"m2",&"m2_"]).

Eval compute in RNNI_refinement expr2d_m1_res expr2d_m1_hid.

(*at m2: false*)
Definition expr2d_m2_res: IA :=
  IAutomaton.hiding
  ( IAutomaton.restriction expr2d (ASet.GenActs [&"m1"]) )
  (ASet.GenActs [&"m1_"]).

Definition expr2d_m2_hid: IA :=
  IAutomaton.hiding expr2d (ASet.GenActs [&"m1",&"m1_"]).

Eval compute in RNNI_refinement expr2d_m2_res expr2d_m2_hid.


(*at l: true*)
Definition expr2d_l_res: IA :=
 IAutomaton.hiding
 ( IAutomaton.restriction expr2d (ASet.GenActs [&"m1",&"m2"]) )
 (ASet.GenActs [&"m1_",&"m2_"]).

Definition expr2d_l_hid: IA :=
  IAutomaton.hiding expr2d (ASet.GenActs [&"m1",&"m2",&"m1_",&"m2_"]).

Eval compute in RNNI_refinement expr2d_l_res expr2d_l_hid.

