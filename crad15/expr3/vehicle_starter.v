
Require Export parser.
Require Export refine.

Definition vehicle: IA := parse
"IA [s1,s2,s3,s4] (s1) [start, emrg, far, halt] [pos, reset] []
[s3->(halt)s1, s1->(start)s2, s2->(pos)s3, s3->(far)s2, 
s2->(emrg)s4, s3->(emrg)s4, s4->(reset)s1]".

Definition starter: IA := parse
"IA [t1,t2] (t1) [] [start] [] [t1->(start)t2]".

Eval compute in IAutomaton.b_compatible vehicle starter.

Definition vst: IA := IAutomaton.composition vehicle starter.
(*Eval compute in IAutomaton.display vst.
"IA [s1_t2, s3_t2, s4_t2, s1_t1, s2_t2] (s1_t1) 
[halt, far, emrg] [reset, pos] [start] 
[s1_t1->(start)s2_t2, s2_t2->(emrg)s4_t2, s2_t2->(pos)s3_t2, 
s4_t2->(reset)s1_t2, s3_t2->(emrg)s4_t2, s3_t2->(far)s2_t2, 
s3_t2->(halt)s1_t2]"*)

(*at m: true*)
Definition vst_m_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement vst (&"tau") (ASet.GenActs [&"emrg"]) )
 (ASet.GenActs [&"reset",&"pos"]).

Definition vst_m_hid: IA :=
 IAutomaton.hiding vst (ASet.GenActs [&"emrg",&"reset",&"pos"]).

Eval compute in SMENI_refinement vst_m_rep vst_m_hid.


(*at l: true*)
Definition vst_l_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement vst (&"tau") (ASet.GenActs [&"emrg"]) )
 (ASet.GenActs [&"reset"]).

Definition vst_l_hid: IA :=
 IAutomaton.hiding vst (ASet.GenActs [&"emrg",&"reset"]).

Eval compute in SMENI_refinement vst_l_rep vst_l_hid.
