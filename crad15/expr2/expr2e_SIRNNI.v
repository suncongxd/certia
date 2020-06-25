(*interface (e) to show the difference 
between SME-NI and the extended SIR-NNI*)

Require Export refine.
Require Export parser.

Definition expr2e: IA := parse
"IA [s1,s2,s3,s4,s5] (s1) [h1,h2] [m1,m2] []
 [s1->(h1)s2, s1->(h2)s3, s2->(m1)s4, s3->(m2)s5]".

(*at m1: false*)
Definition expr2e_m1_res: IA := 
 IAutomaton.hiding 
 ( IAutomaton.restriction expr2e (ASet.GenActs [&"h1",&"h2"]) )
 (ASet.GenActs [&"m2"]).

Definition expr2e_m1_hid: IA :=
IAutomaton.hiding expr2e (ASet.GenActs [&"h1",&"h2",&"m2"]).

Eval compute in RNNI_refinement expr2e_m1_res expr2e_m1_hid.


(*at m2: false*)
Definition expr2e_m2_res: IA :=
 IAutomaton.hiding 
 ( IAutomaton.restriction expr2e (ASet.GenActs [&"h1",&"h2"]) )
 (ASet.GenActs [&"m1"]).

Definition expr2e_m2_hid: IA :=
IAutomaton.hiding expr2e (ASet.GenActs [&"h1",&"h2",&"m1"]).

Eval compute in RNNI_refinement expr2e_m2_res expr2e_m2_hid.


(*at l: true*)
Definition expr2e_l_res: IA :=
 IAutomaton.hiding 
 ( IAutomaton.restriction expr2e (ASet.GenActs [&"h1",&"h2"]) )
 (ASet.GenActs [&"m1",&"m2"]).
(*Eval compute in IAutomaton.display expr2e_l_res.*)

Definition expr2e_l_hid: IA :=
IAutomaton.hiding expr2e (ASet.GenActs [&"h1",&"h2",&"m1",&"m2"]).

Eval compute in RNNI_refinement expr2e_l_res expr2e_l_hid.