Require Export parser.

Definition P1: IA := parse
"IA [IDLE_SS, WAIT_SS, DATA_SS] (IDLE_SS)
[Sa_CONN_conf_S, Sa_DISC_ind_S, Sa_HPDATA_ind_S, Sa_DATA_ind_S] 
[Sa_CONN_req_S, Sa_DISC_req_S, Sa_HPDATA_req_S, Sa_DATA_req_S] []
[IDLE_SS->(Sa_CONN_req_S)WAIT_SS, 
 WAIT_SS->(Sa_DISC_ind_S)IDLE_SS,
 WAIT_SS->(Sa_CONN_conf_S)DATA_SS, 
 DATA_SS->(Sa_DATA_ind_S)DATA_SS, DATA_SS->(Sa_HPDATA_ind_S)DATA_SS, 
 DATA_SS->(Sa_DATA_req_S)DATA_SS, DATA_SS->(Sa_HPDATA_req_S)DATA_SS, 
 DATA_SS->(Sa_DISC_ind_S)IDLE_SS, DATA_SS->(Sa_DISC_req_S)IDLE_SS]".

Definition P2: IA := parse
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
  WFTC_S->(Sa_DISC_ind_S)WFDIS_S, WFTC_S->(T_DISC_ind_S)DISC_1_S,
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

(*this is an alternative P2 that considers
  the maximum connection establishment delay timer T_{estab} thus
  the dash arcs in Fig5.(a) of Zhang Yan's SciChinaE *)
Definition P2': IA := parse
"IA [DISC_1_S, IDLE_S, DISC_2_S, CONN_S, WFDIS_S, DISC_3_S, SA_HP_S, DISC_4_S,
    WFTC_S, T_DA_S, DATA_S, SA_DA_S, T_HP_S, CONF_S, WFAR_S, AR_S] (IDLE_S)
 [Sa_CONN_req_S, Sa_DISC_req_S, T_DISC_ind_S, Sa_HPDATA_req_S, T_DATA_ind_S,
  T_CONN_conf_S, Sa_DATA_req_S, T_HPDATA_ind_S] 
 [T_CONN_req_S, T_DISC_req_S, Sa_DISC_ind_S, T_HPDATA_req_S, Sa_DATA_ind_S,
  Sa_CONN_conf_S, T_DATA_req_S, Sa_HPDATA_ind_S] [e]
 [DISC_1_S->(Sa_DISC_ind_S)IDLE_S, DISC_2_S->(T_DISC_req_S)IDLE_S,
 IDLE_S->(Sa_CONN_req_S)CONN_S, CONN_S->(e)DISC_1_S,
 WFDIS_S->(T_DISC_req_S)IDLE_S,
 DISC_3_S->(T_DISC_req_S)IDLE_S, DISC_4_S->(Sa_DISC_ind_S)IDLE_S,
 CONN_S->(T_CONN_req_S)WFTC_S, WFTC_S->(Sa_DISC_ind_S)WFDIS_S,
 WFTC_S->(T_DISC_ind_S)DISC_1_S,
 WFTC_S->(T_CONN_conf_S)CONF_S, CONF_S->(T_DISC_req_S)DISC_1_S,
 CONF_S->(T_DATA_req_S)WFAR_S, WFAR_S->(T_DISC_ind_S)DISC_1_S,
 WFAR_S->(Sa_DISC_req_S)DISC_2_S, 
 WFAR_S->(T_DATA_ind_S)AR_S, AR_S->(Sa_DISC_ind_S)DISC_2_S,
 AR_S->(Sa_CONN_conf_S)DATA_S, 
 DATA_S->(T_DISC_ind_S)DISC_4_S, DATA_S->(Sa_DISC_req_S)DISC_2_S, 
 DATA_S->(Sa_HPDATA_req_S)SA_HP_S, SA_HP_S->(T_HPDATA_req_S)DATA_S, 
 DATA_S->(T_DATA_ind_S)T_DA_S, T_DA_S->(Sa_DATA_ind_S)DATA_S, 
 DATA_S->(Sa_DATA_req_S)SA_DA_S, SA_DA_S->(T_DATA_req_S)DATA_S,
 DATA_S->(T_HPDATA_ind_S)T_HP_S, T_HP_S->(Sa_HPDATA_ind_S)DATA_S, 
 T_DA_S->(Sa_DISC_ind_S)DISC_3_S,
 WFAR_S->(Sa_DISC_ind_S)DISC_2_S, WFTC_S->(T_DISC_req_S)DISC_1_S]".

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

(* the S-side synthesis on P2 and P2' *)
Eval compute in IAutomaton.b_compatible P1 P2. (*false*)
Eval compute in IAutomaton.b_compatible P2 P3. (*true*)

Definition P23: IA := IAutomaton.composition P2 P3.

Eval compute in IAutomaton.b_compatible P1 P23. (*true*)

Eval compute in IAutomaton.b_compatible P1 P2'. (*false*)
Eval compute in IAutomaton.b_compatible P2' P3. (*true*)

Definition P23': IA := IAutomaton.composition P2' P3.

Eval compute in IAutomaton.b_compatible P1 P23'. (*true*)

(* according to the synthesis, we get the correct P2 as P2_synthesis *)
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

Eval compute in IAutomaton.b_compatible P1 P2_synthesis. (* true *)
Eval compute in IAutomaton.b_compatible P2_synthesis P3. (* true *)

(* the S-side composition *)
Definition P23'': IA := IAutomaton.composition P2_synthesis P3.

Eval compute in IAutomaton.b_compatible P1 P23''. (* true *)

Definition P123: IA := IAutomaton.composition P1 P23''.
Eval compute in :> P123.

(* the F-side composition *)
Eval compute in IAutomaton.b_compatible P3 P4. (*true*)
Eval compute in IAutomaton.b_compatible P4 P5. (*true*)

Definition P45: IA := IAutomaton.composition P4 P5.

Eval compute in IAutomaton.b_compatible P3 P45. (*true*)

Definition P345: IA := IAutomaton.composition P3 P45.

Eval compute in :> P345.




