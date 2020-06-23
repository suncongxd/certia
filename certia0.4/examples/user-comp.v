(* the original example in de Alfaro 2001*)

Require Import IA.
Require Import parser.

Definition User:IA := parse
"IA [s0, s1] (s0) [fail, ok] [msg] [] [s0->(msg)s1, s1->(ok)s0]".

Eval compute in :> User.

Definition Comp:IA := parse 
"IA [s0,s1,s2,s3,s4,s5,s6] (s0) [msg,ack,nack] [fail,ok,send] [] 
[s0->(msg)s1, s1->(send)s2, s2->(nack)s3, s3->(send)s4, s4->(ack)s5,
s2->(ack)s5, s5->(ok)s0, s4->(nack)s6, s6->(fail)s0]".

Eval compute in :> (IAutomaton.IAProd User Comp).
Eval compute in IAutomaton.b_compatible User Comp.
Definition user_comp: IA := IAutomaton.composition User Comp.
Eval compute in :> user_comp.

Definition Channel:IA := parse
"IA [s0,s1,s2,s3] (s0) [send] [ack,nack,gettoken,puttoken] []
[s0->(send)s1, s1->(gettoken)s2, s2->(ack)s3, s3->(puttoken)s0]".

Eval compute in IAutomaton.b_compatible user_comp Channel.
Eval compute in :> (IAutomaton.composition user_comp Channel).


(* Example 2: the example in Fig.3 of de Alfaro 2005*)

Definition TryTwice:IA := parse
"IA [s0,s1,s2,s3,s4,s5,s6] (s0) [send,nack,ack] [trnsmt,ok,fail] []
[s0->(send)s1, s1->(trnsmt)s2, s2->(nack)s3, s3->(trnsmt)s4,
s4->(ack)s5, s2->(ack)s5, s5->(ok)s0, s4->(nack)s6, s6->(fail)s0]".

Definition Client:IA := parse
"IA [s0,s1] (s0) [ok,fail] [send] [] [s0->(send)s1, s1->(ok)s0]".

Eval compute in :> (IAutomaton.IAProd TryTwice Client).
Eval compute in (IAutomaton.b_compatible TryTwice Client).
Eval compute in :> (IAutomaton.composition TryTwice Client).






