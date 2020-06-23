Require Export IA.
Require Export parser.

Definition TryTwice: IA := parse
  "IA [s0,s1,s2,s3,s4,s5,s6,err,err0] (s0) [send,ack,nack] [ok,fail,trnsmt] []
  [s0->(send)s1, s1->(trnsmt)s2, s2->(ack)s5, s2->(nack)s3, s3->(trnsmt)s4, 
  s4->(ack)s5, s4->(nack)s6, s5->(ok)s0, s6->(fail)s0 ]".

Definition OnceOrTwice: IA := parse
  "IA [s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,err,err0] (s0) [once,send,nack,ack] 
  [ok,fail,trnsmt] []
  [s0->(send)s1, s0->(once)s7, s1->(trnsmt)s2, s2->(ack)s5, s2->(nack)s3, 
  s3->(trnsmt)s4, s4->(nack)s6, s4->(ack)s5, s5->(ok)s0, s6->(fail)s0, s0->(once)s7,
  s7->(trnsmt)s8, s8->(ack)s9, s8->(nack)s10, s9->(ok)s0, s10->(fail)s0]".

Eval compute in (IAutomaton.b_compatible TryTwice OnceOrTwice).
Eval compute in (IAutomaton.bRefine TryTwice OnceOrTwice).

Definition IllOnceOrTwice: IA := parse
  "IA [s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,err,err0] (s0) [once,send,nack,ack] 
  [ok,fail,trnsmt] []
  [s0->(send)s1, s0->(once)s7, s1->(trnsmt)s2,
  s3->(trnsmt)s4, s4->(nack)s6, s4->(ack)s5, s5->(ok)s0, s6->(fail)s0, s0->(once)s7,
  s7->(trnsmt)s8, s8->(ack)s9, s8->(nack)s10, s9->(ok)s0, s10->(fail)s0]".

Eval compute in (IAutomaton.bRefine TryTwice IllOnceOrTwice).










