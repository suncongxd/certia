(*this is the example for the difference between SME-NI and SIR-NNI*)

Require Export refine.
Require Export parser.


Definition expr1c: IA := parse
"IA [s1,s2,s3,s4,s5,s6] (s1) [h2] [h1,a] [e] 
[s1->(h2)s2, s1->(h1)s3, s3->(a)s5, s2->(e)s4, s4->(a)s6]".

(*SME-NI: true*)
Definition expr1c_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement expr1c (&"tau") (ASet.GenActs [&"h2"]) )
 (ASet.GenActs [&"h1"]).

Definition expr1c_hid: IA :=
 IAutomaton.hiding expr1c (ASet.GenActs [&"h1",&"h2"]).

Eval compute in SMENI_refinement expr1c_rep expr1c_hid.
