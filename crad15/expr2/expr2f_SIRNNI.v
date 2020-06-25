(*interface (f) to show the difference 
between SME-NI and the extended SIR-NNI*)

Require Export refine.
Require Export parser.

Definition expr2f: IA := parse
"IA [s1,s2,s3,s4,s5] (s1) [h1,h2] [m1,a] []
 [s1->(h1)s2, s1->(h2)s3, s2->(m1)s4, s3->(a)s5]".

(*at m1: false*)
Definition expr2f_m1_res: IA := 
 IAutomaton.restriction expr2f (ASet.GenActs [&"h1",&"h2"]).

Definition expr2f_m1_hid: IA :=
IAutomaton.hiding expr2f (ASet.GenActs [&"h1",&"h2"]).

Eval compute in RNNI_refinement expr2f_m1_res expr2f_m1_hid.


(*at m2: false*)
Definition expr2f_m2_res: IA :=
 IAutomaton.hiding 
 ( IAutomaton.restriction expr2f (ASet.GenActs [&"h1",&"h2"]) )
 (ASet.GenActs [&"m1"]).

Definition expr2f_m2_hid: IA :=
IAutomaton.hiding expr2f (ASet.GenActs [&"h1",&"h2",&"m1"]).

Eval compute in RNNI_refinement expr2f_m2_res expr2f_m2_hid.


(*at l: false*)
Definition expr2f_l_res: IA :=
 IAutomaton.hiding
 ( IAutomaton.restriction expr2f (ASet.GenActs [&"h1",&"h2"]) )
 (ASet.GenActs [&"m1"]).

Definition expr2f_l_hid: IA :=
 IAutomaton.hiding expr2f (ASet.GenActs [&"h1",&"h2",&"m1"]).

Eval compute in RNNI_refinement expr2f_l_res expr2f_l_hid.

