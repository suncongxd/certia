(*this is the example for the difference between SME-NI and SIR-NNI*)

Require Export refine.
Require Export parser.

Definition expr1c: IA := parse
"IA [s1,s2,s3,s4,s5,s6] (s1) [h2] [h1,a] [e] 
[s1->(h2)s2, s1->(h1)s3, s3->(a)s5, s2->(e)s4, s4->(a)s6]".

Definition expr1c_hid: IA :=
 IAutomaton.hiding expr1c (ASet.GenActs [&"h1",&"h2"]).

Definition expr1c_res: IA :=
 IAutomaton.hiding
 ( IAutomaton.restriction expr1c (ASet.GenActs [&"h2"]) )
 (ASet.GenActs [&"h1"]).

Eval compute in RNNI_refinement expr1c_res expr1c_hid. (*true*)
