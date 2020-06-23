Require Import IA.
Require Import parser.

(*ticc: fire-detector.si*)
Definition CtrlU:IA := parse
"IA [s0,s1,s2] (s0) [fire] [FD] [] [s0->(fire)s1, s1->(FD)s2]".

Definition FireD1:IA := parse
"IA [s0,s1,s2] (s0) [smoke1,fire] [fire] [] 
[s0->(smoke1)s1, s1->(fire)s2, s0->(fire)s0, s1->(fire)s1, s2->(fire)s2]".

Eval compute in :> IAutomaton.IAProd CtrlU FireD1.
Eval compute in IAutomaton.b_compatible CtrlU FireD1.

Definition FireD2:IA :=parse
"IA [s0,s1,s2] (s0) [smoke2,fire] [fire] [] 
[s0->(smoke2)s1, s1->(fire)s2, s0->(fire)s0, s1->(fire)s1, s2->(fire)s2]".

Eval compute in :> IAutomaton.IAProd FireD1 FireD2.
Eval compute in IAutomaton.b_compatible FireD1 FireD2.
Eval compute in :> IAutomaton.composition FireD1 FireD2.

Definition c1:IA := IAutomaton.composition FireD1 FireD2.

Eval compute in IAutomaton.b_compatible CtrlU c1.
Eval compute in :> IAutomaton.composition CtrlU c1.

