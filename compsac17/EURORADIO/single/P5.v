Require Export parser.
Require Export refine.

Definition P5: IA := parse
"IA [IDLE_SF, WAIT_SF, DATA_SF] (IDLE_SF)
 [Sa_CONN_ind_F, Sa_DISC_ind_F, Sa_HPDATA_ind_F, Sa_DATA_ind_F] 
 [Sa_CONN_resp_F, Sa_DISC_req_F, Sa_HPDATA_req_F, Sa_DATA_req_F] []
 [IDLE_SF->(Sa_CONN_ind_F)WAIT_SF, WAIT_SF->(Sa_CONN_resp_F)DATA_SF, 
  WAIT_SF->(Sa_DISC_ind_F)IDLE_SF, WAIT_SF->(Sa_DISC_req_F)IDLE_SF, 
  DATA_SF->(Sa_DISC_ind_F)IDLE_SF, DATA_SF->(Sa_DISC_req_F)IDLE_SF,
  DATA_SF->(Sa_DATA_ind_F)DATA_SF, DATA_SF->(Sa_HPDATA_ind_F)DATA_SF,
  DATA_SF->(Sa_DATA_req_F)DATA_SF, DATA_SF->(Sa_HPDATA_req_F)DATA_SF]".

(* SME-NI: true *)
Definition P5_hid: IA :=
 IAutomaton.hiding P5 (ASet.GenActs [&"Sa_HPDATA_req_F",&"Sa_HPDATA_ind_F"]).

Definition P5_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement P5 (&"tau") (ASet.GenActs [&"Sa_HPDATA_ind_F"]) )
 (ASet.GenActs [&"Sa_HPDATA_req_F"]).

Eval compute in :> P5_hid.
Eval compute in :> P5_rep.
Eval compute in SMENI_refinement P5_rep P5_hid.
