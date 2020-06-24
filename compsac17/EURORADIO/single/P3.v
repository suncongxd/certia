Require Export parser.
Require Export refine.

Definition P3: IA := parse
"IA [IDLE_T, HP_F_T, CONR_S_T, DA_S_T, DISC_S_T, HP_S_T, DISC_F_T, DA_F_T, CONRS_F_T] (IDLE_T)
 [T_HPDATA_req_F, T_CONN_resp_F, T_DATA_req_F, T_DISC_req_F, T_HPDATA_req_S, 
  T_DISC_req_S, T_DATA_req_S, T_CONN_req_S]
 [T_HPDATA_ind_S, T_CONN_conf_S, T_DATA_ind_S, T_DISC_ind_S, T_HPDATA_ind_F, 
  T_DISC_ind_F, T_DATA_ind_F, T_CONN_ind_F] [e]
 [ IDLE_T->(T_HPDATA_req_F)HP_F_T, HP_F_T->(T_HPDATA_ind_S)IDLE_T,
   IDLE_T->(T_CONN_resp_F)CONRS_F_T, CONRS_F_T->(T_CONN_conf_S)IDLE_T,
   IDLE_T->(T_DATA_req_F)DA_F_T, DA_F_T->(T_DATA_ind_S)IDLE_T,
   IDLE_T->(T_DISC_req_F)DISC_F_T, DISC_F_T->(T_DISC_ind_S)IDLE_T,
   IDLE_T->(T_HPDATA_req_S)HP_S_T, HP_S_T->(T_HPDATA_ind_F)IDLE_T,
   IDLE_T->(T_DISC_req_S)DISC_S_T, DISC_S_T->(T_DISC_ind_F)IDLE_T, DISC_S_T->(e)IDLE_T,
   IDLE_T->(T_DATA_req_S)DA_S_T, DA_S_T->(T_DATA_ind_F)IDLE_T,
   IDLE_T->(T_CONN_req_S)CONR_S_T, CONR_S_T->(T_CONN_ind_F)IDLE_T
 ]".

(* SME-NI: true *)

Definition P3_hid: IA :=
 IAutomaton.hiding P3 
   (ASet.GenActs [&"T_HPDATA_req_F", &"T_HPDATA_req_S", &"T_HPDATA_ind_S", &"T_HPDATA_ind_F"]).

Definition P3_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement P3 (&"tau") (ASet.GenActs [&"T_HPDATA_req_F", &"T_HPDATA_req_S"]) )
 (ASet.GenActs [&"T_HPDATA_ind_S", &"T_HPDATA_ind_F"]).

Eval compute in :> P3_hid.
Eval compute in :> P3_rep.
Eval compute in SMENI_refinement P3_rep P3_hid.
