(* [10],Fig.1 for Performance Evaluation of COMPSAC'17 paper*)

Require Export parser.
Require Export refine.

(** the security of single component Transaction Service *)
Definition TS: IA := parse
"IA [s1,s2,s3,s4,s5,s6,s7] (s1) [acceptT, endT, newT, startM, endM] [startT, logM] []
[s1->(acceptT)s1, s1->(newT)s2, s2->(startT)s3, s3->(endT)s1, s1->(startM)s4,
s4->(endM)s1, s4->(newT)s5, s5->(startT)s6, s6->(endT)s7, s7->(logM)s4]".

(*SIR-GNNI: true*)
Definition TS_hid: IA :=
 IAutomaton.hiding TS (ASet.GenActs [&"startM",&"endM",&"logM"]).

Definition TS_res: IA :=
 IAutomaton.hiding
 ( IAutomaton.restriction TS (ASet.GenActs [&"startM",&"endM"]) )
 (ASet.GenActs [&"logM"]).

Eval compute in :> TS_hid.
Eval compute in :> TS_res.
Eval compute in SIRGNNI_refinement TS_res TS_hid.

(*SME-NI: true *)
Definition TS_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement TS (&"tau") (ASet.GenActs [&"startM",&"endM"]) )
 (ASet.GenActs [&"logM"]).

Eval compute in :> TS_rep.
Eval compute in SMENI_refinement TS_rep TS_hid.

(** the security of Supervisor *)
Definition SV: IA := parse
"IA [u1,u2,u3,u4,u5] (u1) [mOn, logM, logF] [startM, endM] []
 [u1->(mOn)u2, u1->(logF)u1, u2->(startM)u3, u3->(logM)u3, u3->(logF)u4,
 u4->(logM)u5, u5->(endM)u1]".

(*SIR-GNNI: true *)
Definition SV_hid: IA :=
 IAutomaton.hiding SV (ASet.GenActs [&"mOn",&"logM",&"startM",&"endM"]).

Definition SV_res: IA :=
 IAutomaton.hiding
 ( IAutomaton.restriction SV (ASet.GenActs [&"mOn",&"logM"]) )
 (ASet.GenActs [&"endM",&"startM"]).

Eval compute in :> SV_hid.
Eval compute in :> SV_res.
Eval compute in SIRGNNI_refinement SV_res SV_hid.

(*SME-NI: true *)
Definition SV_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement SV (&"tau") (ASet.GenActs [&"mOn", &"logM"]) )
 (ASet.GenActs [&"startM",&"endM"]).

Eval compute in :> SV_rep.
Eval compute in SMENI_refinement SV_rep SV_hid.

(** the security of the result of composition *)
Definition TPU: IA := parse
"IA [t1,t2,t3,t4] (t1) [startT] [nOk,ok,logF,endT] []
[t1->(startT)t2, t2->(nOk)t4, t4->(logF)t3, t2->(ok)t3,t3->(endT)t1]".

Definition compIA: IA := IAutomaton.composition TS (IAutomaton.composition TPU SV).
Eval compute in :> compIA.

(*SIR-GNNI: true *)
Definition compIA_hid: IA :=
 IAutomaton.hiding compIA (ASet.GenActs [&"mOn"]).

Definition compIA_res: IA :=
 IAutomaton.restriction compIA (ASet.GenActs [&"mOn"]).

Eval compute in SIRGNNI_refinement compIA_res compIA_hid.
