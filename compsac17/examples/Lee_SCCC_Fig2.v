(* [11],Fig.2 for Performance Evaluation of COMPSAC'17 paper *)

Require Export parser.
Require Export refine.

Definition ECP: IA := parse
"IA [t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15] (t1)
[reject_all,ext_ctrl,accept,decline,review] [done,ext_no,ext_yes] [allow,process]
[t1->(ext_ctrl)t2, t2->(ext_no)t3, t2->(ext_yes)t4, t3->(accept)t7,
 t3->(review)t6, t4->(accept)t7, t4->(decline)t7, t6->(process)t5,
 t5->(done)t1, t7->(process)t8, t8->(done)t1, t1->(reject_all)t9,
 t9->(ext_ctrl)t10, t10->(ext_no)t11, t11->(allow)t13, t11->(accept)t12,
 t13->(accept)t12, t12->(process)t15, t13->(review)t14, t14->(process)t15, t15->(done)t9]".

(* SIR-GNNI: true*)
Definition ECP_hid: IA :=
 IAutomaton.hiding ECP (ASet.GenActs [&"reject_all"]).

Definition ECP_res: IA :=
 IAutomaton.restriction ECP (ASet.GenActs [&"reject_all"]).

Eval compute in :> ECP_hid.
Eval compute in :> ECP_res.
Eval compute in SIRGNNI_refinement ECP_res ECP_hid.

(* SME-NI: true*)
Definition ECP_rep: IA :=
 IAutomaton.replacement ECP (&"tau") (ASet.GenActs [&"reject_all"]).

Eval compute in :> ECP_rep.
Eval compute in SMENI_refinement ECP_rep ECP_hid.