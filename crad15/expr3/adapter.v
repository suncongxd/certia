

Require Export parser.
Require Export refine.

Definition adapter: IA := parse
"IA [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11] (s1)
[login,req,connected,arg,service] 
[usr,pass,ok,ack,value,query] []
[s1->(login)s2, s2->(usr)s3, s3->(pass)s4,
s4->(connected)s5, s5->(ok)s6, s6->(req)s7,
s7->(arg)s8, s8->(value)s9, s9->(query)s10,
s10->(service)s11, s11->(ack)s1]".

Definition adapter_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement adapter (&"tau") (ASet.GenActs [&"req",&"arg",&"service"]) )
 (ASet.GenActs [&"value",&"query",&"ack"]).

Definition adapter_hid: IA :=
 IAutomaton.hiding adapter (ASet.GenActs [&"req",&"arg",&"service",&"value",&"query",&"ack"]).

Eval compute in SMENI_refinement adapter_rep adapter_hid. (*false*)