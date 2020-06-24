Require Export parser.
Require Export refine.

Definition P4: IA := parse
"IA [IDLE_F, DISC_1_F, DISC_2_F, CONIND_F, WFAU3_F, DISC_3_F, SA_HP_F,
 DATA_F, T_HP_F, SA_DA_F, T_DA_F, RAU3_F, WFRESP_F, SNDAR_F] 
 (IDLE_F)
 [T_CONN_ind_F, Sa_DISC_req_F, T_DISC_ind_F, Sa_DATA_req_F, T_DATA_ind_F, Sa_CONN_resp_F, Sa_HPDATA_req_F, T_HPDATA_ind_F] 
 [Sa_CONN_ind_F, T_DISC_req_F, Sa_DISC_ind_F, T_DATA_req_F, Sa_DATA_ind_F, T_CONN_resp_F, T_HPDATA_req_F, Sa_HPDATA_ind_F] [e]
 [DISC_1_F->(T_DISC_req_F)IDLE_F, DISC_2_F->(Sa_DISC_ind_F)IDLE_F,
 IDLE_F->(T_CONN_ind_F)CONIND_F, CONIND_F->(e)DISC_1_F,
 CONIND_F->(T_CONN_resp_F)WFAU3_F, WFAU3_F->(T_DATA_ind_F)RAU3_F,
 RAU3_F->(e)DISC_1_F, RAU3_F->(Sa_CONN_ind_F)WFRESP_F,
 WFRESP_F->(Sa_DISC_req_F)DISC_1_F, WFRESP_F->(T_DISC_ind_F)DISC_2_F,
 WFRESP_F->(Sa_CONN_resp_F)SNDAR_F, SNDAR_F->(T_DATA_req_F)DATA_F,
 DATA_F->(Sa_HPDATA_req_F)SA_HP_F, SA_HP_F->(T_HPDATA_req_F)DATA_F,
 DATA_F->(T_HPDATA_ind_F)T_HP_F, T_HP_F->(Sa_HPDATA_ind_F)DATA_F,
 DATA_F->(Sa_DATA_req_F)SA_DA_F, SA_DA_F->(T_DATA_req_F)DATA_F,
 DATA_F->(T_DATA_ind_F)T_DA_F, T_DA_F->(Sa_DATA_ind_F)DATA_F,
 WFAU3_F->(T_DISC_ind_F)IDLE_F, DATA_F->(T_DISC_ind_F)DISC_2_F,
 T_DA_F->(Sa_DISC_ind_F)DISC_3_F, DISC_3_F->(T_DISC_req_F)IDLE_F, 
 DATA_F->(Sa_DISC_req_F)DISC_3_F]".

Eval compute in :> P4.

(* SME-NI: true *)
Definition P4_hid: IA :=
 IAutomaton.hiding P4 
  (ASet.GenActs [&"T_HPDATA_req_F",&"Sa_HPDATA_req_F",&"T_HPDATA_ind_F",&"Sa_HPDATA_ind_F"]).

Definition P4_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement P4 (&"tau") (ASet.GenActs [&"T_HPDATA_ind_F", &"Sa_HPDATA_req_F"]) )
 (ASet.GenActs [&"T_HPDATA_req_F", &"Sa_HPDATA_ind_F"]).

Eval compute in :> P4_hid.
Eval compute in :> P4_rep.
Eval compute in SMENI_refinement P4_rep P4_hid.