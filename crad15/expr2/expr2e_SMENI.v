(*interface (e) to show the difference 
between SME-NI and the extended SIR-NNI*)

Require Export refine.
Require Export parser.
Require Import subsetconst.

Definition expr2e: IA := parse
"IA [s1,s2,s3,s4,s5] (s1) [h1,h2] [m1,m2] []
 [s1->(h1)s2, s1->(h2)s3, s2->(m1)s4, s3->(m2)s5]".

(*at m1: false*)
Definition expr2e_m1_rep: IA := 
 subset_construction
 ( IAutomaton.hiding 
 ( IAutomaton.replacement expr2e (&"tau") (ASet.GenActs [&"h1",&"h2"]) )
 (ASet.GenActs [&"m2"]) ).
(*Eval compute in IAutomaton.display expr2e_m1_rep.*)

Definition expr2e_m1_hid: IA :=
IAutomaton.hiding expr2e (ASet.GenActs [&"h1",&"h2",&"m2"]).

(*Eval compute in IAutomaton.display expr2e_m1_rep.
Eval compute in IAutomaton.display expr2e_m1_hid.*)
Eval compute in SMENI_refinement expr2e_m1_rep expr2e_m1_hid.


(*at m2: false*)
Definition expr2e_m2_rep: IA :=
 subset_construction
 ( IAutomaton.hiding 
 ( IAutomaton.replacement expr2e (&"tau") (ASet.GenActs [&"h1",&"h2"]) )
 (ASet.GenActs [&"m1"]) ).
(*Eval compute in IAutomaton.display expr2e_m2_rep.*)

Definition expr2e_m2_hid: IA :=
IAutomaton.hiding expr2e (ASet.GenActs [&"h1",&"h2",&"m1"]).

Eval compute in SMENI_refinement expr2e_m2_rep expr2e_m2_hid.


(*at l: true *)
Definition expr2e_l_rep: IA :=
 subset_construction
 ( IAutomaton.hiding
 ( IAutomaton.replacement expr2e (&"tau") (ASet.GenActs [&"h1",&"h2"]) )
 (ASet.GenActs [&"m1",&"m2"]) ).

Definition expr2e_l_hid: IA :=
 IAutomaton.hiding expr2e (ASet.GenActs [&"h1",&"h2",&"m1",&"m2"]).

Eval compute in SMENI_refinement expr2e_l_rep expr2e_l_hid.

