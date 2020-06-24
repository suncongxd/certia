Require Export parser.
Require Export refine.

Definition P2_synthesis: IA := parse
"IA 
 [DISC_1_S, IDLE_S, DISC_2_S, CONN_S, WFDIS_S, DISC_3_S, SA_HP_S, DISC_4_S,
  WFTC_S, T_DA_S, DATA_S, SA_DA_S, T_HP_S, CONF_S, WFAR_S, AR_S] 
 (IDLE_S)
 [Sa_CONN_req_S, Sa_DISC_req_S, T_DISC_ind_S, Sa_HPDATA_req_S, T_DATA_ind_S, T_CONN_conf_S, Sa_DATA_req_S, T_HPDATA_ind_S] 
 [T_CONN_req_S, T_DISC_req_S, Sa_DISC_ind_S, T_HPDATA_req_S, Sa_DATA_ind_S, Sa_CONN_conf_S, T_DATA_req_S, Sa_HPDATA_ind_S]
 [e]
 [IDLE_S->(Sa_CONN_req_S)CONN_S,
  CONN_S->(T_CONN_req_S)WFTC_S, CONN_S->(e)DISC_1_S,
  DISC_1_S->(Sa_DISC_ind_S)IDLE_S, 
  WFTC_S->(Sa_DISC_req_S)WFDIS_S, WFTC_S->(T_DISC_ind_S)DISC_1_S,
  WFDIS_S->(T_DISC_req_S)IDLE_S,
  WFTC_S->(T_CONN_conf_S)CONF_S, 
  CONF_S->(T_DISC_req_S)DISC_1_S, CONF_S->(T_DATA_req_S)WFAR_S,
  WFAR_S->(T_DISC_ind_S)DISC_1_S, WFAR_S->(Sa_DISC_req_S)DISC_2_S, 
  WFAR_S->(T_DATA_ind_S)AR_S, 
  AR_S->(Sa_DISC_ind_S)DISC_2_S, AR_S->(Sa_CONN_conf_S)DATA_S, 
  DATA_S->(Sa_DISC_req_S)DISC_2_S, DISC_2_S->(T_DISC_req_S)IDLE_S,
  DATA_S->(T_DISC_ind_S)DISC_4_S, DISC_4_S->(Sa_DISC_ind_S)IDLE_S,
  DATA_S->(Sa_HPDATA_req_S)SA_HP_S, SA_HP_S->(T_HPDATA_req_S)DATA_S, 
  DATA_S->(T_DATA_ind_S)T_DA_S, T_DA_S->(Sa_DATA_ind_S)DATA_S, 
  DATA_S->(Sa_DATA_req_S)SA_DA_S, SA_DA_S->(T_DATA_req_S)DATA_S,
  DATA_S->(T_HPDATA_ind_S)T_HP_S, T_HP_S->(Sa_HPDATA_ind_S)DATA_S,
  T_DA_S->(Sa_DISC_ind_S)DISC_3_S, DISC_3_S->(T_DISC_req_S)IDLE_S]".

Definition P2_synthesis_hid: IA :=
 IAutomaton.hiding P2_synthesis 
  (ASet.GenActs [&"Sa_HPDATA_req_S",&"T_HPDATA_req_S",&"Sa_HPDATA_ind_S",&"T_HPDATA_ind_S"]).

Definition P2_synthesis_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement P2_synthesis (&"tau") 
   (ASet.GenActs [&"Sa_HPDATA_req_S",&"T_HPDATA_ind_S"]) )
 (ASet.GenActs [&"T_HPDATA_req_S", &"Sa_HPDATA_ind_S"]).

Eval compute in :> P2_synthesis_hid.
Eval compute in :> P2_synthesis_rep.
Eval compute in SMENI_refinement P2_synthesis_rep P2_synthesis_hid.