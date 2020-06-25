(*interface (a) to show the difference 
between SME-NI and the extended SIR-NNI*)

Require Export refine.
Require Export parser.
Require Import subsetconst.

Definition expr2a: IA := parse
"IA [s1,s2,s3,s4] (s1) [m1,m2] [a,b] [] [s1->(m1)s2, s1->(m2)s3, s2->(a)s4, s3->(b)s4]".

(*at m1: true*)
Definition expr2a_m1_rep: IA :=
 IAutomaton.hiding
  ( IAutomaton.replacement expr2a (&"tau") (ASet.GenActs [&"m2"]) )
  (ASet.GenActs [&"a",&"b"]).

Definition expr2a_m1_hid: IA :=
  IAutomaton.hiding expr2a (ASet.GenActs [&"m2",&"a",&"b"]).

(*Eval compute in IAutomaton.display expr2a_m1_rep.
Eval compute in IAutomaton.display expr2a_m1_hid.*)
Eval compute in SMENI_refinement expr2a_m1_rep expr2a_m1_hid.


(*at m2: true*)
Definition expr2a_m2_rep: IA :=
  IAutomaton.hiding
  ( IAutomaton.replacement expr2a (&"tau") (ASet.GenActs [&"m1"]) )
  (ASet.GenActs [&"a",&"b"]).

Definition expr2a_m2_hid: IA :=
  IAutomaton.hiding expr2a (ASet.GenActs [&"m1",&"a",&"b"]).

Eval compute in SMENI_refinement expr2a_m2_rep expr2a_m2_hid.


(*at l: false*)
Definition expr2a_l_rep: IA :=
  subset_construction ( IAutomaton.replacement expr2a (&"tau") (ASet.GenActs [&"m1",&"m2"]) ).
(*Eval compute in IAutomaton.display expr2a_l_rep.*)

Definition expr2a_l_hid: IA :=
  IAutomaton.hiding expr2a (ASet.GenActs [&"m1",&"m2"]).

Eval compute in SMENI_refinement expr2a_l_rep expr2a_l_hid.

