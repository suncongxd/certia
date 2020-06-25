

Require Export parser.
Require Export refine.

Definition client: IA := parse
"IA [c1,c2,c3,c4,c5] (c1)
[ok,ack,error] [login,req,arg] []
[c1->(login)c2, c2->(error)c1, c2->(ok)c3,
c3->(req)c4, c4->(arg)c5, c5->(ack)c1]".

Definition client_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement client (&"tau") (ASet.GenActs [&"ack"]) )
 (ASet.GenActs [&"arg",&"req"]).

Definition client_hid: IA :=
 IAutomaton.hiding client (ASet.GenActs [&"ack",&"arg",&"req"]).

Eval compute in SMENI_refinement client_rep client_hid. (*false*)