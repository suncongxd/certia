
Require Export parser.
Require Export refine.


Definition SV: IA := parse
"IA [u1,u2,u3,u4,u5] (u1) [mOn, logM, logF] [startM, endM] []
 [u1->(mOn)u2, u1->(logF)u1, u2->(startM)u3, u3->(logM)u3, u3->(logF)u4,
 u4->(logM)u5, u5->(endM)u1]".

Definition TPU: IA := parse
"IA [t1,t2,t3,t4] (t1) [startT] [nOk,ok,logF,endT] []
[t1->(startT)t2, t2->(nOk)t4, t4->(logF)t3, t2->(ok)t3,t3->(endT)t1]".

Eval compute in IAutomaton.b_compatible SV TPU. (*true*)

Definition SV_TPU: IA := IAutomaton.composition SV TPU.
(*Eval compute in :> SV_TPU.*)
(*"IA [u5_t1, u4_t1, u5_t3, u4_t3, u3_t3, u3_t4, u2_t3, u3_t2, u1_t4, u1_t3, 
u3_t1, u1_t2, u1_t1, u2_t1] (u1_t1) [startT, logM, mOn] 
[endT, ok, nOk, endM, startM] [logF] 
[u1_t1->(mOn)u2_t1, u1_t1->(startT)u1_t2, u2_t1->(startM)u3_t1, 
u1_t2->(ok)u1_t3, u1_t2->(nOk)u1_t4, u3_t1->(logM)u3_t1, 
u1_t3->(mOn)u2_t3, u1_t3->(endT)u1_t1, u3_t1->(startT)u3_t2, 
u1_t4->(logF)u1_t3, u3_t2->(logM)u3_t2, u2_t3->(startM)u3_t3, 
u2_t3->(endT)u2_t1, u3_t2->(ok)u3_t3, u3_t2->(nOk)u3_t4, 
u3_t4->(logM)u3_t4, u3_t3->(logM)u3_t3, u3_t3->(endT)u3_t1, 
u3_t4->(logF)u4_t3, u4_t3->(logM)u5_t3, u4_t3->(endT)u4_t1, 
u5_t3->(endM)u1_t3, u4_t1->(logM)u5_t1, u5_t3->(endT)u5_t1, 
u5_t1->(endM)u1_t1]"*)

(*SME-NI: *)
Definition SV_TPU_hid: IA :=
 IAutomaton.hiding SV_TPU (ASet.GenActs [&"mOn",&"logM",&"startM",&"endM"]).

Definition SV_TPU_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement SV_TPU (&"tau") (ASet.GenActs [&"mOn",&"logM"]) )
 (ASet.GenActs [&"startM",&"endM"]).

Eval compute in SMENI_refinement SV_TPU_rep SV_TPU_hid. (*true*)
