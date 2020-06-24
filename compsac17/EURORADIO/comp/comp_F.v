(* SME-NI of P3||(P4||P5): true *)

Require Export refine.
Require Export parser.

Definition P3: IA := parse
"IA [IDLE_T, HP_F_T, CONR_S_T, DA_S_T, DISC_S_T, HP_S_T, DISC_F_T, DA_F_T, CONRS_F_T] 
 (IDLE_T)
 [T_HPDATA_req_F, T_CONN_resp_F, T_DATA_req_F, T_DISC_req_F, T_HPDATA_req_S, T_DISC_req_S, T_DATA_req_S, T_CONN_req_S]
 [T_HPDATA_ind_S, T_CONN_conf_S, T_DATA_ind_S, T_DISC_ind_S, T_HPDATA_ind_F, T_DISC_ind_F, T_DATA_ind_F, T_CONN_ind_F]
 [e]
 [ IDLE_T->(T_HPDATA_req_F)HP_F_T, HP_F_T->(T_HPDATA_ind_S)IDLE_T,
   IDLE_T->(T_CONN_resp_F)CONRS_F_T, CONRS_F_T->(T_CONN_conf_S)IDLE_T,
   IDLE_T->(T_DATA_req_F)DA_F_T, DA_F_T->(T_DATA_ind_S)IDLE_T,
   IDLE_T->(T_DISC_req_F)DISC_F_T, DISC_F_T->(T_DISC_ind_S)IDLE_T,
   IDLE_T->(T_HPDATA_req_S)HP_S_T, HP_S_T->(T_HPDATA_ind_F)IDLE_T,
   IDLE_T->(T_DISC_req_S)DISC_S_T, DISC_S_T->(T_DISC_ind_F)IDLE_T, DISC_S_T->(e)IDLE_T,
   IDLE_T->(T_DATA_req_S)DA_S_T, DA_S_T->(T_DATA_ind_F)IDLE_T,
   IDLE_T->(T_CONN_req_S)CONR_S_T, CONR_S_T->(T_CONN_ind_F)IDLE_T
 ]".

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

Definition P5: IA := parse
"IA [IDLE_SF, WAIT_SF, DATA_SF] (IDLE_SF)
 [Sa_CONN_ind_F, Sa_DISC_ind_F, Sa_HPDATA_ind_F, Sa_DATA_ind_F] 
 [Sa_CONN_resp_F, Sa_DISC_req_F, Sa_HPDATA_req_F, Sa_DATA_req_F] []
 [IDLE_SF->(Sa_CONN_ind_F)WAIT_SF, WAIT_SF->(Sa_CONN_resp_F)DATA_SF, 
  WAIT_SF->(Sa_DISC_ind_F)IDLE_SF, WAIT_SF->(Sa_DISC_req_F)IDLE_SF, 
  DATA_SF->(Sa_DISC_ind_F)IDLE_SF, DATA_SF->(Sa_DISC_req_F)IDLE_SF,
  DATA_SF->(Sa_DATA_ind_F)DATA_SF, DATA_SF->(Sa_HPDATA_ind_F)DATA_SF,
  DATA_SF->(Sa_DATA_req_F)DATA_SF, DATA_SF->(Sa_HPDATA_req_F)DATA_SF]".

Definition P345: IA :=
 IAutomaton.composition P3 (IAutomaton.composition P4 P5).
(*Eval compute in :> P345.*)
(* P345:
IA 
[DISC_F_T_IDLE_F_IDLE_SF, DISC_S_T_WFAU3_F_IDLE_SF, IDLE_T_DISC_1_F_IDLE_SF, 
IDLE_T_WFAU3_F_IDLE_SF, CONRS_F_T_WFAU3_F_IDLE_SF, IDLE_T_CONIND_F_IDLE_SF, 
IDLE_T_IDLE_F_IDLE_SF, CONR_S_T_IDLE_F_IDLE_SF] 
(IDLE_T_IDLE_F_IDLE_SF) 
[T_CONN_req_S, T_DATA_req_S, T_DISC_req_S, T_HPDATA_req_S] 
[T_DISC_ind_S, T_DATA_ind_S, T_CONN_conf_S, T_HPDATA_ind_S] 
[e, T_CONN_ind_F, T_DATA_ind_F, T_DISC_ind_F, T_HPDATA_ind_F, T_DISC_req_F, 
T_DATA_req_F, T_CONN_resp_F, T_HPDATA_req_F, Sa_HPDATA_ind_F, Sa_DATA_ind_F, 
Sa_DISC_ind_F, Sa_CONN_ind_F, Sa_HPDATA_req_F, Sa_CONN_resp_F, Sa_DATA_req_F, Sa_DISC_req_F] 
[IDLE_T_IDLE_F_IDLE_SF->(T_CONN_req_S)CONR_S_T_IDLE_F_IDLE_SF, 
CONR_S_T_IDLE_F_IDLE_SF->(T_CONN_ind_F)IDLE_T_CONIND_F_IDLE_SF, 
IDLE_T_CONIND_F_IDLE_SF->(T_CONN_resp_F)CONRS_F_T_WFAU3_F_IDLE_SF, 
CONRS_F_T_WFAU3_F_IDLE_SF->(T_CONN_conf_S)IDLE_T_WFAU3_F_IDLE_SF, 
IDLE_T_WFAU3_F_IDLE_SF->(T_DISC_req_S)DISC_S_T_WFAU3_F_IDLE_SF, 
IDLE_T_DISC_1_F_IDLE_SF->(T_DISC_req_F)DISC_F_T_IDLE_F_IDLE_SF, 
DISC_F_T_IDLE_F_IDLE_SF->(T_DISC_ind_S)IDLE_T_IDLE_F_IDLE_SF, 
DISC_S_T_WFAU3_F_IDLE_SF->(T_DISC_ind_F)IDLE_T_IDLE_F_IDLE_SF]
*)

Definition P345_hid: IA :=
 IAutomaton.hiding P345
  (ASet.GenActs [&"T_HPDATA_req_S", &"T_HPDATA_ind_S"]).

Definition P345_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement P345 (&"tau") (ASet.GenActs [&"T_HPDATA_req_S"]) )
 (ASet.GenActs [&"T_HPDATA_ind_S"]).

Eval compute in :> P345_hid.
Eval compute in :> P345_rep.
Eval compute in SMENI_refinement P345_rep P345_hid.
