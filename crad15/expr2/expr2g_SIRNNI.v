(*interface (g) to show the difference 
between SME-NI and the extended SIR-NNI*)

Require Export refine.
Require Export parser.

Definition expr2g: IA := parse
"IA [s1,s2,s3,s4,s5] (s1) [h1,m1_] [m1,m2] []
 [s1->(h1)s2, s1->(m1_)s3, s2->(m1)s4, s3->(m2)s5]".

(*at m1: false*)
Definition expr2g_m1_res: IA := 
 IAutomaton.hiding 
 ( IAutomaton.restriction expr2g (ASet.GenActs [&"h1"]) )
 (ASet.GenActs [&"m2"]).

Definition expr2g_m1_hid: IA :=
IAutomaton.hiding expr2g (ASet.GenActs [&"h1",&"m2"]).

Eval compute in RNNI_refinement expr2g_m1_res expr2g_m1_hid.


(*at m2: false*)
Definition expr2g_m2_res: IA :=
 IAutomaton.hiding 
 ( IAutomaton.restriction expr2g (ASet.GenActs [&"h1",&"m1_"]) )
 (ASet.GenActs [&"m1"]).

Definition expr2g_m2_hid: IA :=
IAutomaton.hiding expr2g (ASet.GenActs [&"h1",&"m1_",&"m1"]).

Eval compute in RNNI_refinement expr2g_m2_res expr2g_m2_hid.


(*at l: true *)
Definition expr2g_l_res: IA :=
 IAutomaton.hiding
 ( IAutomaton.restriction expr2g (ASet.GenActs [&"h1",&"m1_"]) )
 (ASet.GenActs [&"m1",&"m2"]).

Definition expr2g_l_hid: IA :=
 IAutomaton.hiding expr2g (ASet.GenActs [&"h1",&"m1_",&"m1",&"m2"]).

Eval compute in RNNI_refinement expr2g_l_res expr2g_l_hid.

