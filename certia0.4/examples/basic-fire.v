Require Import IA.
Require Import parser.

(*case 1:basic_fire.si*)
Definition CtrlU:IA := parse
"IA [s0,s1,s2] (s0) [fire] [FD] [] [s0->(fire)s1, s1->(FD)s2]".

Definition FireD1:IA := parse
"IA [s0,s1,s2] (s0) [smoke1] [fire] [] [s0->(smoke1)s1, s1->(fire)s2]".

Definition FireD2:IA :=parse
"IA [s0,s1,s2] (s0) [smoke2] [fire] [] [s0->(smoke2)s1, s1->(fire)s2]".

Eval compute in IAutomaton.b_compatible FireD1 CtrlU.
Eval compute in :> IAutomaton.IAProd FireD1 CtrlU.
Eval compute in :> IAutomaton.composition FireD1 CtrlU.

Eval compute in :> IAutomaton.IAProd (IAutomaton.IAProd FireD1 CtrlU) FireD2.

Definition c: IA := IAutomaton.composition CtrlU FireD1.

Eval compute in IAutomaton.b_compatible c FireD2.
Eval compute in :> IAutomaton.composition c FireD2.
