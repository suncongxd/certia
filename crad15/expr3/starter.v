
Require Export parser.
Require Export refine.

Definition starter: IA := parse
"IA [t1,t2] (t1) [] [start] [] [t1->(start)t2]".

(*at m: true*)
Definition starter_m_rep: IA := starter.

Definition starter_m_hid: IA := starter.

Eval compute in SMENI_refinement starter_m_rep starter_m_hid.

(*at l: true*)
Definition starter_l_rep: IA :=
 IAutomaton.hiding starter (ASet.GenActs [&"start"]).

Definition starter_l_hid: IA :=
 IAutomaton.hiding starter (ASet.GenActs [&"start"]).

Eval compute in SMENI_refinement starter_l_rep starter_l_hid.