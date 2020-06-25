
Require Export parser.
Require Export refine.

Definition TS: IA := parse
"IA [s1,s2,s3,s4,s5,s6,s7] (s1) [acceptT, endT, newT, startM, endM] [startT, logM] []
[s1->(acceptT)s1, s1->(newT)s2, s2->(startT)s3, s3->(endT)s1, s1->(startM)s4,
s4->(endM)s1, s4->(newT)s5, s5->(startT)s6, s6->(endT)s7, s7->(logM)s4]".

Definition SV: IA := parse
"IA [u1,u2,u3,u4,u5] (u1) [mOn, logM, logF] [startM, endM] []
 [u1->(mOn)u2, u1->(logF)u1, u2->(startM)u3, u3->(logM)u3, u3->(logF)u4,
 u4->(logM)u5, u5->(endM)u1]".

Eval compute in IAutomaton.b_compatible TS SV. (*true*)

Definition TS_SV: IA := IAutomaton.composition TS SV.
(*Eval compute in :> TS_SV.*)
(*"IA [s4_u5, s7_u4, s6_u4, s7_u3, s5_u4, s6_u3, s4_u4, s5_u3, s4_u3, 
s3_u1, s1_u2, s1_u1, s2_u1] (s1_u1) [logF, mOn, newT, endT, acceptT] [startT] 
[logM, endM, startM] [s1_u1->(newT)s2_u1, s1_u1->(acceptT)s1_u1, 
s1_u1->(logF)s1_u1, s1_u1->(mOn)s1_u2, s2_u1->(startT)s3_u1, 
s1_u2->(acceptT)s1_u2, s2_u1->(logF)s2_u1, s1_u2->(startM)s4_u3, 
s4_u3->(newT)s5_u3, s3_u1->(endT)s1_u1, s4_u3->(logF)s4_u4, 
s3_u1->(logF)s3_u1, s5_u3->(startT)s6_u3, s4_u4->(newT)s5_u4, 
s5_u3->(logF)s5_u4, s6_u3->(endT)s7_u3, s5_u4->(startT)s6_u4, 
s6_u3->(logF)s6_u4, s6_u4->(endT)s7_u4, s7_u3->(logF)s7_u4, 
s7_u3->(logM)s4_u3, s7_u4->(logM)s4_u5, s4_u5->(endM)s1_u1]"*)

(*SME-NI: true *)
Definition TS_SV_hid: IA :=
 IAutomaton.hiding TS_SV (ASet.GenActs [&"mOn"]).

Definition TS_SV_rep: IA :=
 IAutomaton.replacement TS_SV (&"tau") (ASet.GenActs [&"mOn"]).

Eval compute in SMENI_refinement TS_SV_rep TS_SV_hid. (*false*)
