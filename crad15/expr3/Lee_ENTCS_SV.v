
Require Export parser.
Require Export refine.

(** the security of Supervisor *)
Definition SV: IA := parse
"IA [u1,u2,u3,u4,u5] (u1) [mOn, logM, logF] [startM, endM] []
 [u1->(mOn)u2, u1->(logF)u1, u2->(startM)u3, u3->(logM)u3, u3->(logF)u4,
 u4->(logM)u5, u5->(endM)u1]".

(*SME-NI: true *)
Definition SV_hid: IA :=
 IAutomaton.hiding SV (ASet.GenActs [&"mOn",&"logM",&"startM",&"endM"]).

Definition SV_rep: IA :=
 IAutomaton.hiding
 ( IAutomaton.replacement SV (&"tau") (ASet.GenActs [&"mOn", &"logM"]) )
 (ASet.GenActs [&"startM",&"endM"]).

Eval compute in SMENI_refinement SV_rep SV_hid.


