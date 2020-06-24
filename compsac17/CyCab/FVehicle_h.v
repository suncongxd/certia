Require Export refine.
Require Export parser.

Definition FVehicle: IA := parse
 "IA [s1,s2,s3,s4,s5,s6] (s1) [fstart,start,emrg,far,halt] [pos,reset] [move,stop]
  [s1->(start)s2, s2->(move)s3, s2->(emrg)s5, s3->(pos)s4, s3->(emrg)s5, s4->(far)s2,
  s4->(halt)s1, s4->(emrg)s5, s5->(reset)s1, s1->(fstart)s6, s6->(move)s6, s6->(emrg)s5,
  s6->(stop)s1]".

(*************************** \Gamma(fstart)=h ****************************)
(* SIR-GNNI at m: false *)
Definition FVehicle_hid_m: IA :=
 IAutomaton.hiding FVehicle (ASet.GenActs [&"emrg",&"reset",&"fstart"]).

Definition FVehicle_res_m: IA := 
 IAutomaton.hiding 
   (IAutomaton.restriction FVehicle (ASet.GenActs [&"emrg",&"fstart"]) )
   (ASet.GenActs [&"reset"]).

Eval compute in :> FVehicle_hid_m.
Eval compute in :> FVehicle_res_m.
Eval compute in SIRGNNI_refinement FVehicle_res_m FVehicle_hid_m.

(* SIR-GNNI at l: false *)
Definition FVehicle_hid_l: IA :=
 IAutomaton.hiding FVehicle (ASet.GenActs [&"start",&"pos",&"emrg",&"fstart",&"reset"]).

Definition FVehicle_res_l: IA :=
 IAutomaton.hiding
 ( IAutomaton.restriction FVehicle (ASet.GenActs [&"start",&"emrg",&"fstart"]) )
 (ASet.GenActs [&"pos",&"reset"]).

Eval compute in :> FVehicle_hid_l.
Eval compute in :> FVehicle_res_l.
Eval compute in SIRGNNI_refinement FVehicle_res_l FVehicle_hid_l.

(* SME-NI at m: false *)
Definition FVehicle_rep_m: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement FVehicle (&"tau") (ASet.GenActs [&"emrg",&"fstart"]) )
 (ASet.GenActs [&"reset"]).

Eval compute in :> FVehicle_rep_m.
Eval compute in SMENI_refinement FVehicle_rep_m FVehicle_hid_m.

(* SME-NI at l: false*)
Definition FVehicle_rep_l: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement FVehicle (&"tau") (ASet.GenActs [&"start",&"emrg",&"fstart"]) )
 (ASet.GenActs [&"reset",&"pos"]).

Eval compute in :> FVehicle_rep_l.
Eval compute in SMENI_refinement FVehicle_rep_l FVehicle_hid_l.








