

Require Export parser.
Require Export refine.

Definition station: IA := parse
"IA [s1,s2] (s1) [pos] [far, halt] []
[s1->(pos)s2, s2->(far)s1, s2->(halt)s1]".

(*at m: true*)
Definition station_m_rep: IA :=
 IAutomaton.hiding station (ASet.GenActs [&"far",&"halt"]).

Definition station_m_hid: IA :=
 IAutomaton.hiding station (ASet.GenActs [&"far",&"halt"]).

Eval compute in SMENI_refinement station_m_rep station_m_hid.


(*at l: true*)
Definition station_l_rep: IA := station.

Definition station_l_hid: IA := station.

Eval compute in SMENI_refinement station_l_rep station_l_hid.