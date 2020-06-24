Require Export parser.
Require Export refine.

Definition P1: IA := parse
"IA [IDLE_SS, WAIT_SS, DATA_SS] (IDLE_SS)
[Sa_CONN_conf_S, Sa_DISC_ind_S, Sa_HPDATA_ind_S, Sa_DATA_ind_S] 
[Sa_CONN_req_S, Sa_DISC_req_S, Sa_HPDATA_req_S, Sa_DATA_req_S] []
[IDLE_SS->(Sa_CONN_req_S)WAIT_SS, WAIT_SS->(Sa_DISC_ind_S)IDLE_SS,
 WAIT_SS->(Sa_CONN_conf_S)DATA_SS, DATA_SS->(Sa_DATA_ind_S)DATA_SS,
 DATA_SS->(Sa_HPDATA_ind_S)DATA_SS, DATA_SS->(Sa_DATA_req_S)DATA_SS, 
 DATA_SS->(Sa_HPDATA_req_S)DATA_SS, DATA_SS->(Sa_DISC_ind_S)IDLE_SS,
 DATA_SS->(Sa_DISC_req_S)IDLE_SS]".

(* SME-NI: true *)
Definition P1_hid: IA :=
 IAutomaton.hiding P1 (ASet.GenActs [&"Sa_HPDATA_req_S", &"Sa_HPDATA_ind_S"]).

Definition P1_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement P1 (&"tau") (ASet.GenActs [&"Sa_HPDATA_req_S"]) )
 (ASet.GenActs [&"Sa_HPDATA_ind_S"]).

Eval compute in :> P1_hid.
Eval compute in :> P1_rep.
Eval compute in SMENI_refinement P1_rep P1_hid.