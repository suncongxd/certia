(* this example is from 
Larsen K., et al. Modal I/O Automata for Interface and Product Line Theories.*)

Require Import IA.
Require Import parser.

Definition Datalink: IA := parse
"IA [14,15,16,17,18,19,20,21,22] (14)
[send,ack,nack,up,down] [ok,fail,trnsmt,linkStatus,log] []
[14->(send)15, 15->(trnsmt)16, 16->(nack)17, 16->(ack)19, 17->(trnsmt)18,
18->(nack)17, 18->(ack)19, 19->(ok)14, 17->(linkStatus)20, 20->(up)17,
20->(down)21, 21->(log)22, 22->(fail)14]".

Definition Client: IA := parse
"IA [2,3] (2) [ok,fail] [send] [] [2->(send)3, 3->(ok)2]".

Eval compute in :> (IAutomaton.IAProd Datalink Client).
Eval compute in IAutomaton.b_compatible Datalink Client.
Eval compute in :> (IAutomaton.composition Datalink Client).