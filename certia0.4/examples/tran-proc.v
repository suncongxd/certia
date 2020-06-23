(*the following is the example of Lee's ENTCS 264(2010)*)

Require Import IA.
Require Import parser.

Definition TS:IA := parse
"IA [s1,s2,s3,s4,s5,s6,s7] (s1) [acceptT,endT,newT,endM,startM] [startT,logM] []
[s1->(acceptT)s1, s1->(newT)s2, s1->(startM)s4, s2->(startT)s3, s3->(endT)s1,
s4->(endM)s1, s4->(newT)s5, s5->(startT)s6, s6->(endT)s7, s7->(logM)s4]".

Definition TPU:IA :=parse
"IA [t1,t2,t3,t4] (t1) [startT] [nOk,ok,logF,endT] []
[t1->(startT)t2, t2->(ok)t3, t2->(nOk)t4, t4->(logF)t3, t3->(endT)t1]".

Eval compute in :> (IAutomaton.IAProd TS TPU).
Eval compute in IAutomaton.b_compatible TS TPU.
Definition tmpIA: IA := IAutomaton.composition TS TPU.
Eval compute in :> tmpIA.

Definition Sup:IA := parse
"IA [u1,u2,u3,u4,u5] (u1) [logF,mOn,logM] [startM,endM] []
[u1->(logF)u1, u1->(mOn)u2, u2->(startM)u3, u3->(logM)u3, 
u3->(logF)u4, u4->(logM)u5, u5->(endM)u1]".

Eval compute in (IAutomaton.b_compatible tmpIA Sup).
Eval compute in :> (IAutomaton.composition tmpIA Sup).

