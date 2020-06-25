(*interface (f) to show the difference 
between SME-NI and the extended SIR-NNI*)

Require Export refine.
Require Export parser.
Require Import subsetconst.

Definition expr2f: IA := parse
"IA [s1,s2,s3,s4,s5] (s1) [h1,h2] [m1,a] []
 [s1->(h1)s2, s1->(h2)s3, s2->(m1)s4, s3->(a)s5]".

(*at m1: false*)
Definition expr2f_m1_rep: IA := 
 subset_construction
 ( IAutomaton.hiding 
 ( IAutomaton.replacement expr2f (&"tau") (ASet.GenActs [&"h1",&"h2"]) )
 (ASet.GenActs [&"a"]) ).
(*Eval compute in IAutomaton.display expr2f_m1_rep.*)

Definition expr2f_m1_hid: IA :=
IAutomaton.hiding expr2f (ASet.GenActs [&"h1",&"h2",&"a"]).

Eval compute in SMENI_refinement expr2f_m1_rep expr2f_m1_hid.


(*at m2: true*)
Definition expr2f_m2_rep: IA :=
 subset_construction
 ( IAutomaton.hiding 
 ( IAutomaton.replacement expr2f (&"tau") (ASet.GenActs [&"h1",&"h2"]) )
 (ASet.GenActs [&"m1",&"a"]) ).
(*Eval compute in IAutomaton.display expr2f_m2_rep.*)

Definition expr2f_m2_hid: IA :=
IAutomaton.hiding expr2f (ASet.GenActs [&"h1",&"h2",&"m1",&"a"]).
(*Eval compute in IAutomaton.display expr2f_m2_hid.*)

Eval compute in SMENI_refinement expr2f_m2_rep expr2f_m2_hid.


(*at l: false*)
Definition expr2f_l_rep: IA :=
 subset_construction
 ( IAutomaton.hiding
 ( IAutomaton.replacement expr2f (&"tau") (ASet.GenActs [&"h1",&"h2"]) )
 (ASet.GenActs [&"m1"]) ).

Definition expr2f_l_hid: IA :=
 IAutomaton.hiding expr2f (ASet.GenActs [&"h1",&"h2",&"m1"]).

Eval compute in SMENI_refinement expr2f_l_rep expr2f_l_hid.

