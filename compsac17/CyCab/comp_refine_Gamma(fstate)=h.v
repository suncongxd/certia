Require Export refine.
Require Export parser.

Require Export Station.
Require Export Vehicle.
Require Export comp.

(** The CyCab example *)

Definition FVehicle: IA := parse
 "IA [s1,s2,s3,s4,s5,s6] (s1) [fstart,start,emrg,far,halt] [pos,reset] [move,stop]
  [s1->(start)s2, s2->(move)s3, s2->(emrg)s5, s3->(pos)s4, s3->(emrg)s5, s4->(far)s2,
  s4->(halt)s1, s4->(emrg)s5, s5->(reset)s1, s1->(fstart)s6, s6->(move)s6, s6->(emrg)s5,
  s6->(stop)s1]".

(* FVehicle is a refinement of Vehicle *)
Eval compute in IAutomaton.bRefine Vehicle FVehicle.

Eval compute in IAutomaton.b_compatible FVehicle Station.

(*Definition FVehicle_Station_prod: IA := IAutomaton.IAProd FVehicle Station.
Eval compute in :> FVehicle_Station_prod.*)

Definition FVehicle_Station: IA :=IAutomaton.composition FVehicle Station.
Eval compute in :> FVehicle_Station.

(* the composition results comply with the refinement relation *)
Eval compute in IAutomaton.bRefine Vehicle_Station FVehicle_Station.

(*********** security of FVehicle*Station ******************************************)

(*************************** \Gamma(fstart)=h ****************************)
(* SIR-GNNI at m: true *)
Definition FVehicle_Station_hid_m: IA :=
 IAutomaton.hiding FVehicle_Station (ASet.GenActs [&"emrg",&"reset",&"fstart"]).

Definition FVehicle_Station_res_m: IA :=
 IAutomaton.hiding
 ( IAutomaton.restriction FVehicle_Station (ASet.GenActs [&"emrg",&"fstart"]) )
 (ASet.GenActs [&"reset"]).

Eval compute in :> FVehicle_Station_hid_m.
Eval compute in :> FVehicle_Station_res_m.
Eval compute in SIRGNNI_refinement FVehicle_Station_res_m FVehicle_Station_hid_m.

(* SME-NI at m: true *)
Definition FVehicle_Station_rep_m: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement FVehicle_Station (&"tau") (ASet.GenActs [&"emrg",&"fstart"]) )
 (ASet.GenActs [&"reset"]).

Eval compute in :> FVehicle_Station_rep_m.
Eval compute in SMENI_refinement FVehicle_Station_rep_m FVehicle_Station_hid_m.

(* SIR-GNNI at l: true *)
Definition FVehicle_Station_hid_l: IA :=
  IAutomaton.hiding FVehicle_Station
  (ASet.GenActs [&"emrg",&"start",&"fstart",&"reset"]).

Definition FVehicle_Station_res_l: IA :=
  IAutomaton.hiding
  ( IAutomaton.restriction FVehicle_Station (ASet.GenActs [&"emrg",&"start",&"fstart"]) )
  (ASet.GenActs [&"reset"]).

Eval compute in :>FVehicle_Station_hid_l.
Eval compute in :>FVehicle_Station_res_l.
Eval compute in SIRGNNI_refinement FVehicle_Station_res_l FVehicle_Station_hid_l.

(* SME-NI at l: true *)
Definition FVehicle_Station_rep_l: IA :=
  IAutomaton.hiding
  ( IAutomaton.replacement FVehicle_Station (&"tau") (ASet.GenActs [&"emrg",&"start",&"fstart"]) )
  (ASet.GenActs [&"reset"]).

Eval compute in :>FVehicle_Station_rep_l.
Eval compute in SMENI_refinement FVehicle_Station_rep_l FVehicle_Station_hid_l.
