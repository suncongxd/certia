Require Import refine.
Require Import parser.

(** The CyCab example *)

(********* the security of component Vehicle ************)

Definition Vehicle: IA := parse
"IA [s1,s2,s3,s4] (s1) [start, emrg, far, halt] [pos, reset] []
[s3->(halt)s1, s1->(start)s2, s2->(pos)s3, s3->(far)s2, 
s2->(emrg)s4, s3->(emrg)s4, s4->(reset)s1]".

(* SIR-GNNI at m: false *)
Definition Vehicle_hid_m: IA :=
 IAutomaton.hiding Vehicle (ASet.GenActs [&"emrg",&"reset"]).

Definition Vehicle_res_m: IA := 
 IAutomaton.hiding 
   (IAutomaton.restriction Vehicle (ASet.GenActs [&"emrg"]) )
   (ASet.GenActs [&"reset"]).

Eval compute in :> Vehicle_hid_m.
Eval compute in :> Vehicle_res_m.
Eval compute in SIRGNNI_refinement Vehicle_res_m Vehicle_hid_m.

(* SIR-GNNI at l: false *)
Definition Vehicle_hid_l: IA :=
 IAutomaton.hiding Vehicle (ASet.GenActs [&"start",&"pos",&"emrg",&"reset"]).

Definition Vehicle_res_l: IA :=
 IAutomaton.hiding
 ( IAutomaton.restriction Vehicle (ASet.GenActs [&"start",&"emrg"]) )
 (ASet.GenActs [&"pos",&"reset"]).

Eval compute in :> Vehicle_hid_l.
Eval compute in :> Vehicle_res_l.
Eval compute in SIRGNNI_refinement Vehicle_res_l Vehicle_hid_l.

(* SME-NI at m: false *)
Definition Vehicle_rep_m: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement Vehicle (&"tau") (ASet.GenActs [&"emrg"]) )
 (ASet.GenActs [&"reset"]).

Eval compute in :> Vehicle_rep_m.
Eval compute in SMENI_refinement Vehicle_rep_m Vehicle_hid_m.

(* SME-NI at l: false*)
Definition Vehicle_rep_l: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement Vehicle (&"tau") (ASet.GenActs [&"start",&"emrg"]) )
 (ASet.GenActs [&"reset",&"pos"]).

Eval compute in :> Vehicle_rep_l.
Eval compute in SMENI_refinement Vehicle_rep_l Vehicle_hid_l.