Require Export parser.
Require Export refine.

Definition vehicle: IA := parse
"IA [s1,s2,s3,s4] (s1) [start, emrg, far, halt] [pos, reset] []
[s3->(halt)s1, s1->(start)s2, s2->(pos)s3, s3->(far)s2, 
s2->(emrg)s4, s3->(emrg)s4, s4->(reset)s1]".

Definition starter: IA := parse
"IA [t1,t2] (t1) [] [start] [] [t1->(start)t2]".

Definition vst: IA := IAutomaton.composition vehicle starter.

Definition emrghalt: IA := parse
"IA [e1,e2] (e1) [reset] [emrg] []
[e1->(emrg)e2, e2->(reset)e1]". 
(*emrghalt cannot be composed with vehicle directly*)

Eval compute in IAutomaton.b_compatible vst emrghalt. (*true*)

Definition vste: IA := IAutomaton.composition vst emrghalt.
(*Eval compute in IAutomaton.display vste.
"IA [s1_t2_e1, s4_t2_e2, s3_t2_e1, s1_t1_e1, s2_t2_e1] (s1_t1_e1) 
[halt, far] [pos] [reset, emrg, start] 
[s1_t1_e1->(start)s2_t2_e1, s2_t2_e1->(pos)s3_t2_e1, 
s2_t2_e1->(emrg)s4_t2_e2, s3_t2_e1->(far)s2_t2_e1, 
s3_t2_e1->(halt)s1_t2_e1, s4_t2_e2->(reset)s1_t2_e1, 
s3_t2_e1->(emrg)s4_t2_e2]"*)

(*at m: true*)
Definition vste_m_rep: IA :=
 IAutomaton.hiding vste (ASet.GenActs [&"pos"]).

Definition vste_m_hid: IA :=
 IAutomaton.hiding vste (ASet.GenActs [&"pos"]).

Eval compute in SMENI_refinement vste_m_rep vste_m_hid.

(*at l: true*)
Definition vste_l_rep: IA := vste.

Definition vste_l_hid: IA := vste.

Eval compute in SMENI_refinement vste_l_rep vste_l_hid.
 