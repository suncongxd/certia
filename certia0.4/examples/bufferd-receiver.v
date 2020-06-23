(** In de Alfaro, L. and M. Stoelinga (2004). 
"Interfaces: A Game-Theoretic Framework for 
Reasoning About Component-Based Systems." 
Electronic Notes in Theoretical Computer Science 97: 3-23.*)

Require Export IA.
Require Export parser.

Definition Buffer:IA := parse
"IA [b0,b1,b2] (b0) [snd] [rec] [] 
[b0->(snd)b1, b1->(snd)b2, b2->(rec)b1, b1->(rec)b0]".

Definition Receiver:IA := parse
"IA [r0,r1] (r0) [rec] [proc] []
[r0->(rec)r1, r1->(proc)r0]".

Eval compute in :> (IAutomaton.IAProd Buffer Receiver).
Eval compute in IAutomaton.b_compatible Buffer Receiver.
Eval compute in :> (IAutomaton.composition Buffer Receiver).