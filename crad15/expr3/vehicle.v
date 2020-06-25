
Require Export parser.
Require Export refine.

Definition vehicle: IA := parse
"IA [s1,s2,s3,s4] (s1) [start, emrg, far, halt] [pos, reset] []
[s3->(halt)s1, s1->(start)s2, s2->(pos)s3, s3->(far)s2, 
s2->(emrg)s4, s3->(emrg)s4, s4->(reset)s1]".

(*at m: false*)
Definition vehicle_m_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement vehicle (&"tau") (ASet.GenActs [&"emrg"]) )
 (ASet.GenActs [&"reset",&"pos"]).

Definition vehicle_m_hid: IA :=
 IAutomaton.hiding vehicle (ASet.GenActs [&"emrg",&"reset",&"pos"]).

Eval compute in SMENI_refinement vehicle_m_rep vehicle_m_hid.


(*at l: false*)
Definition vehicle_l_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement vehicle (&"tau") (ASet.GenActs [&"emrg",&"start"]) )
 (ASet.GenActs [&"reset"]).

Definition vehicle_l_hid: IA :=
 IAutomaton.hiding vehicle (ASet.GenActs [&"emrg",&"start",&"reset"]).

Eval compute in SMENI_refinement vehicle_l_rep vehicle_l_hid.