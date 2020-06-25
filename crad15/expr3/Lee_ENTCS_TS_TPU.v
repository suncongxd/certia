
Require Export parser.
Require Export refine.

Definition TS: IA := parse
"IA [s1,s2,s3,s4,s5,s6,s7] (s1) [acceptT, endT, newT, startM, endM] [startT, logM] []
[s1->(acceptT)s1, s1->(newT)s2, s2->(startT)s3, s3->(endT)s1, s1->(startM)s4,
s4->(endM)s1, s4->(newT)s5, s5->(startT)s6, s6->(endT)s7, s7->(logM)s4]".

Definition TPU: IA := parse
"IA [t1,t2,t3,t4] (t1) [startT] [nOk,ok,logF,endT] []
[t1->(startT)t2, t2->(nOk)t4, t4->(logF)t3, t2->(ok)t3,t3->(endT)t1]".

Eval compute in IAutomaton.b_compatible TS TPU. (*true*)

Definition TS_TPU: IA := IAutomaton.composition TS TPU.
(*Eval compute in :> TS_TPU.*)
(*"IA [s7_t1, s6_t4, s6_t3, s6_t2, s3_t4, s3_t3, s3_t2, s5_t1, s2_t1, s1_t1, s4_t1] 
(s1_t1) [endM, startM, newT, acceptT] [logF, ok, nOk, logM] [startT, endT] 
[s1_t1->(startM)s4_t1, s1_t1->(newT)s2_t1, s1_t1->(acceptT)s1_t1, s4_t1->(newT)s5_t1, 
s4_t1->(endM)s1_t1, s2_t1->(startT)s3_t2, s3_t2->(ok)s3_t3, s3_t2->(nOk)s3_t4, 
s5_t1->(startT)s6_t2, s6_t2->(ok)s6_t3, s3_t4->(logF)s3_t3, s6_t2->(nOk)s6_t4, 
s3_t3->(endT)s1_t1, s6_t4->(logF)s6_t3, s6_t3->(endT)s7_t1, s7_t1->(logM)s4_t1]"*)

(*SME-NI: true *)
Definition TS_TPU_hid: IA :=
 IAutomaton.hiding TS_TPU (ASet.GenActs [&"startM",&"endM",&"logM"]).

Definition TS_TPU_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement TS_TPU (&"tau") (ASet.GenActs [&"startM",&"endM"]) )
 (ASet.GenActs [&"logM"]).

Eval compute in SMENI_refinement TS_TPU_rep TS_TPU_hid. (*true*)
