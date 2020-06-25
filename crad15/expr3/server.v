
Require Export parser.
Require Export refine.

Definition server: IA := parse
"IA [s1,s2,s3,s4,s5,s6,s7,s8] (s1)
[admin_md,usr,pass,value,query] [connected,error,service] []
[s1->(usr)s2, s2->(pass)s3, s3->(connected)s4, s4->(value)s5,
s5->(query)s6, s6->(service)s1, s1->(admin_md)s7,
s7->(usr)s8, s8->(error)s1]".


Definition server_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement server (&"tau") (ASet.GenActs [&"query",&"value"]) )
 (ASet.GenActs [&"service"]).

Definition server_hid: IA :=
 IAutomaton.hiding server (ASet.GenActs [&"query",&"value",&"service"]).

Eval compute in SMENI_refinement server_rep server_hid. (*false*)