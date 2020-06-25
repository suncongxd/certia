

Require Export parser.
Require Export refine.

Definition vehicle: IA := parse
"IA [s1,s2,s3,s4] (s1) [start, emrg, far, halt] [pos, reset] []
[s3->(halt)s1, s1->(start)s2, s2->(pos)s3, s3->(far)s2, 
s2->(emrg)s4, s3->(emrg)s4, s4->(reset)s1]".

Definition station: IA := parse
"IA [s1,s2] (s1) [pos] [far, halt] []
[s1->(pos)s2, s2->(far)s1, s2->(halt)s1]".

Eval compute in IAutomaton.b_compatible vehicle station.

Definition vs: IA := IAutomaton.composition vehicle station.
(*Eval compute in IAutomaton.display vs.
"IA [s3_s2, s4_s1, s1_s1, s2_s1] (s1_s1) 
[emrg, start] [reset] [pos, halt, far] 
[s1_s1->(start)s2_s1, s2_s1->(emrg)s4_s1, s2_s1->(pos)s3_s2, 
s4_s1->(reset)s1_s1, s3_s2->(far)s2_s1, s3_s2->(halt)s1_s1]"*)

(*at m: true *)
Definition vs_m_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement vs (&"tau") (ASet.GenActs [&"emrg"]) )
 (ASet.GenActs [&"reset"]).

Definition vs_m_hid: IA :=
 IAutomaton.hiding vs (ASet.GenActs [&"emrg",&"reset"]).

Eval compute in SMENI_refinement vs_m_rep vs_m_hid.


(*at l: true*)
Definition vs_l_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement vs (&"tau") (ASet.GenActs [&"emrg",&"start"]) )
 (ASet.GenActs [&"reset"]).

Definition vs_l_hid: IA :=
 IAutomaton.hiding vs (ASet.GenActs [&"emrg",&"start",&"reset"]).

Eval compute in SMENI_refinement vs_l_rep vs_l_hid.
