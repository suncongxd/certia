Require Export parser.
Require Export refine.

Definition client: IA := parse
"IA [c1,c2,c3,c4,c5] (c1)
[ok,ack,error] [login,req,arg] []
[c1->(login)c2, c2->(error)c1, c2->(ok)c3,
c3->(req)c4, c4->(arg)c5, c5->(ack)c1]".

Definition adapter: IA := parse
"IA [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11] (s1)
[login,req,connected,arg,service] 
[usr,pass,ok,ack,value,query] []
[s1->(login)s2, s2->(usr)s3, s3->(pass)s4,
s4->(connected)s5, s5->(ok)s6, s6->(req)s7,
s7->(arg)s8, s8->(value)s9, s9->(query)s10,
s10->(service)s11, s11->(ack)s1]".

Eval compute in IAutomaton.b_compatible client adapter. (*true*)

Definition client_adapter: IA := IAutomaton.composition client adapter.
(*Eval compute in IAutomaton.display client_adapter.
"IA [c5_s11, c5_s10, c5_s9, c5_s8, c4_s7, c3_s6, c2_s5, c2_s4, c2_s3, c1_s1, c2_s2]
 (c1_s1) [service, connected, error] [query, value, pass, usr] 
[arg, req, login, ack, ok] 
[c1_s1->(login)c2_s2, c2_s2->(usr)c2_s3, c2_s3->(pass)c2_s4, 
c2_s4->(connected)c2_s5, c2_s5->(ok)c3_s6, c3_s6->(req)c4_s7, 
c4_s7->(arg)c5_s8, c5_s8->(value)c5_s9, c5_s9->(query)c5_s10, 
c5_s10->(service)c5_s11, c5_s11->(ack)c1_s1]"*)

Definition client_adapter_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement client_adapter (&"tau") (ASet.GenActs [&"service"]) )
 (ASet.GenActs [&"query",&"value"]).

Definition client_adapter_hid: IA :=
 IAutomaton.hiding client_adapter (ASet.GenActs [&"service",&"query",&"value"]).

Eval compute in SMENI_refinement client_adapter_rep client_adapter_hid. (*false*)