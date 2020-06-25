
Require Export parser.
Require Export refine.

(** the security of single component Transaction Service *)
Definition TS: IA := parse
"IA [s1,s2,s3,s4,s5,s6,s7] (s1) [acceptT, endT, newT, startM, endM] [startT, logM] []
[s1->(acceptT)s1, s1->(newT)s2, s2->(startT)s3, s3->(endT)s1, s1->(startM)s4,
s4->(endM)s1, s4->(newT)s5, s5->(startT)s6, s6->(endT)s7, s7->(logM)s4]".

(*SME-NI: true*)
Definition TS_hid: IA :=
 IAutomaton.hiding TS (ASet.GenActs [&"startM",&"endM",&"logM"]).

Definition TS_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement TS (&"tau") (ASet.GenActs [&"startM",&"endM"]) )
 (ASet.GenActs [&"logM"]).

Eval compute in SMENI_refinement TS_rep TS_hid.

