
Require Export parser.
Require Export refine.

(** the security of TPU *)
Definition TPU: IA := parse
"IA [t1,t2,t3,t4] (t1) [startT] [nOk,ok,logF,endT] []
[t1->(startT)t2, t2->(nOk)t4, t4->(logF)t3, t2->(ok)t3,t3->(endT)t1]".

Eval compute in SMENI_refinement TPU TPU. (*true*)
