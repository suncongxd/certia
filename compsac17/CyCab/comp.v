Require Import refine.
Require Import parser.

Require Export Vehicle.
Require Export Station.

(** The CyCab example *)

(** The security of the composition of Vehicle and Station.
    This case shows the composition of Vehicle and Station is secure *)

Eval compute in IAutomaton.b_compatible Vehicle Station.

Definition Vehicle_Station: IA :=
 IAutomaton.composition Vehicle Station.
Eval compute in :> Vehicle_Station.

(* SIR-GNNI at m: true *)
Definition Vehicle_Station_hid_m: IA :=
 IAutomaton.hiding Vehicle_Station (ASet.GenActs [&"emrg",&"reset"]).

Definition Vehicle_Station_res_m: IA :=
 IAutomaton.hiding
 ( IAutomaton.restriction Vehicle_Station (ASet.GenActs [&"emrg"]) )
 (ASet.GenActs [&"reset"]).

Eval compute in :> Vehicle_Station_hid_m.
Eval compute in :> Vehicle_Station_res_m.
Eval compute in SIRGNNI_refinement Vehicle_Station_res_m Vehicle_Station_hid_m.

(* SME-NI at m: true *)
Definition Vehicle_Station_rep_m: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement Vehicle_Station (&"tau") (ASet.GenActs [&"emrg"]) )
 (ASet.GenActs [&"reset"]).

Eval compute in :> Vehicle_Station_rep_m.
Eval compute in SMENI_refinement Vehicle_Station_rep_m Vehicle_Station_hid_m.

(* SIR-GNNI at l: true *)
Definition Vehicle_Station_hid_l: IA :=
 IAutomaton.hiding Vehicle_Station (ASet.GenActs [&"emrg",&"reset",&"start"]).

Definition Vehicle_Station_res_l: IA :=
 IAutomaton.hiding
 ( IAutomaton.restriction Vehicle_Station (ASet.GenActs [&"emrg",&"start"]) )
 (ASet.GenActs [&"reset"]).

Eval compute in :> Vehicle_Station_hid_l.
Eval compute in :> Vehicle_Station_res_l.
Eval compute in SIRGNNI_refinement Vehicle_Station_res_l Vehicle_Station_hid_l.

(* SME-NI at l: true *)

Definition Vehicle_Station_rep_l: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement Vehicle_Station (&"tau") (ASet.GenActs [&"emrg",&"start"]) )
 (ASet.GenActs [&"reset"]).

Eval compute in :> Vehicle_Station_rep_l.
Eval compute in SMENI_refinement Vehicle_Station_rep_l Vehicle_Station_hid_l.


(* The security of vehicle*station*starter *)
Definition Starter: IA := parse
 "IA [s0,s1] (s0) [] [start] [] [s0->(start)s1]".

Eval compute in IAutomaton.b_compatible Vehicle_Station Starter.

Definition Vehicle_Station_Starter: IA := IAutomaton.composition Vehicle_Station Starter.
Eval compute in :> Vehicle_Station_Starter.

(* SIR-GNNI and SME-NI at m/l: *)
Definition Vehicle_Station_Starter_hid: IA :=
 IAutomaton.hiding Vehicle_Station_Starter (ASet.GenActs [&"emrg",&"reset"]).

Definition Vehicle_Station_Starter_res: IA :=
IAutomaton.hiding
 ( IAutomaton.restriction Vehicle_Station_Starter (ASet.GenActs [&"emrg"]) )
 (ASet.GenActs [&"reset"]).

Definition Vehicle_Station_Starter_rep: IA :=
IAutomaton.hiding
 ( IAutomaton.replacement Vehicle_Station_Starter (&"tau") (ASet.GenActs [&"emrg"]) )
 (ASet.GenActs [&"reset"]).

Eval compute in :> Vehicle_Station_Starter_hid.
Eval compute in :> Vehicle_Station_Starter_res.
Eval compute in :> Vehicle_Station_Starter_rep.
Eval compute in SIRGNNI_refinement Vehicle_Station_Starter_res Vehicle_Station_Starter_hid.
Eval compute in SMENI_refinement Vehicle_Station_Starter_rep Vehicle_Station_Starter_hid.

Definition Emergency_halt: IA := parse
 "IA [s0,s1] (s0) [reset] [emrg] [] [s0->(emrg)s1, s1->(reset)s0]".

Eval compute in IAutomaton.b_compatible Vehicle_Station_Starter Emergency_halt.
Definition Sys: IA := IAutomaton.composition Vehicle_Station_Starter Emergency_halt.
Eval compute in :> Sys.





