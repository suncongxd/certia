(* [11],Fig.1 for Performance Evaluation of COMPSAC'17 paper *)

Require Export parser.
Require Export refine.

Definition CAP: IA := parse
"IA [s1,s2,s3,s4,s5,s6,s7] (s1) 
[only_loc_off,only_loc,cred_req,done] [yes,no,loc_ctrl,ext_ctrl] []
[s1->(cred_req)s2, s2->(loc_ctrl)s3, s2->(ext_ctrl)s4, s3->(yes)s1, s3->(no)s1,
 s4->(done)s1, s1->(only_loc)s5, s5->(only_loc_off)s1, s5->(cred_req)s6,
 s6->(loc_ctrl)s7, s7->(yes)s5, s7->(no)s5]".

(* SIR-GNNI: true *)
Definition CAP_hid: IA :=
 IAutomaton.hiding CAP
 (ASet.GenActs [&"only_loc_off",&"only_loc"]).

Definition CAP_res: IA :=
 IAutomaton.restriction CAP
 (ASet.GenActs [&"only_loc_off",&"only_loc"]).

Eval compute in :> CAP_hid.
Eval compute in :> CAP_res.
Eval compute in SIRGNNI_refinement CAP_res CAP_hid.

(* SME-NI: true *)
Definition CAP_rep: IA :=
 IAutomaton.replacement CAP (&"tau")
 (ASet.GenActs [&"only_loc_off",&"only_loc"]).

Eval compute in :> CAP_rep.
Eval compute in SMENI_refinement CAP_rep CAP_hid.