
Require Export parser.
Require Export refine.

Definition emrghalt: IA := parse
"IA [e1,e2] (e1) [reset] [emrg] []
[e1->(emrg)e2, e2->(reset)e1]".

(*at m: true*)

Definition emrghalt_m_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement emrghalt (&"tau") (ASet.GenActs [&"reset"]) )
 (ASet.GenActs [&"emrg"]).

Definition emrghalt_m_hid: IA :=
 IAutomaton.hiding emrghalt (ASet.GenActs [&"reset",&"emrg"]).

Eval compute in SMENI_refinement emrghalt_m_rep emrghalt_m_hid.


(*at l: true*)

Definition emrghalt_l_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement emrghalt (&"tau") (ASet.GenActs [&"reset"]) )
 (ASet.GenActs [&"emrg"]).

Definition emrghalt_l_hid: IA :=
 IAutomaton.hiding emrghalt (ASet.GenActs [&"reset",&"emrg"]).

Eval compute in SMENI_refinement emrghalt_l_rep emrghalt_l_hid.