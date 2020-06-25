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

Definition server: IA := parse
"IA [s1,s2,s3,s4,s5,s6,s7,s8] (s1)
[admin_md,usr,pass,value,query] [connected,error,service] []
[s1->(usr)s2, s2->(pass)s3, s3->(connected)s4, s4->(value)s5,
s5->(query)s6, s6->(service)s1, s1->(admin_md)s7,
s7->(usr)s8, s8->(error)s1]".

Eval compute in IAutomaton.b_compatible adapter server. (*true*)

Definition adapter_server: IA := IAutomaton.composition adapter server.
(*Eval compute in IAutomaton.display adapter_server.
"IA [s11_s7, s11_s1, s10_s6, s9_s5, s8_s4, s7_s4, s6_s4, s5_s4, s4_s3, 
s3_s2, s1_s7, s1_s1, s2_s1] (s1_s1) 
[admin_md, arg, req, login] [error, ack, ok] 
[query, value, pass, usr, service, connected] 
[s1_s1->(login)s2_s1, s1_s1->(admin_md)s1_s7, s2_s1->(usr)s3_s2, 
s3_s2->(pass)s4_s3, s4_s3->(connected)s5_s4, s5_s4->(ok)s6_s4, 
s6_s4->(req)s7_s4, s7_s4->(arg)s8_s4, s8_s4->(value)s9_s5, 
s9_s5->(query)s10_s6, s10_s6->(service)s11_s1, s11_s1->(ack)s1_s1, 
s11_s1->(admin_md)s11_s7, s11_s7->(ack)s1_s7]"*)

Definition adapter_server_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement adapter_server (&"tau") (ASet.GenActs [&"arg",&"req"]) )
 (ASet.GenActs [&"ack"]).

Definition adapter_server_hid: IA :=
 IAutomaton.hiding adapter_server (ASet.GenActs [&"arg",&"req",&"ack"]).

Eval compute in SMENI_refinement adapter_server_rep adapter_server_hid. (*false*)