(* [11],Fig.5 for Performance Evaluation of COMPSAC'17 paper *)

Require Import refine.
Require Import parser.

Definition S: IA := parse 
"IA [s0,s1,s2,s3,s4,s5,s6,s7,s8] (s0) [a,H2,H1] [b] [e] 
[s0->(a)s1, s1->(b)s2, s2->(e)s3, s3->(H2)s4, s0->(H1)s5, s5->(a)s6,
s6->(b)s7, s7->(H2)s8]".

Definition T: IA := parse
"IA [t0,t1,t2] (t0) [b] [H2] []
[t0->(b)t1, t1->(H2)t2]".

Eval compute in :> (IAutomaton.IAProd S T).
Eval compute in (IAutomaton.b_compatible S T).

Definition S_T:IA := IAutomaton.composition S T.
Eval compute in :> (IAutomaton.composition S T).

(* judge both S and T are noninterferent *)
Definition S_res: IA :=
IAutomaton.restriction S (ASet.GenActs [&"H1",&"H2"]).

Definition S_hid: IA :=
IAutomaton.hiding S (ASet.GenActs [&"H1",&"H2"]).

Eval compute in :> S_res.
Eval compute in :> S_hid.

Eval compute in (SIRGNNI_refinement S_res S_hid).

Definition T_res:IA :=
IAutomaton.restriction T (ASet.GenActs [&"H2"]).

Definition T_hid:IA :=
IAutomaton.hiding T (ASet.GenActs [&"H2"]).

Eval compute in :> T_res.
Eval compute in :> T_hid.

Eval compute in (SIRGNNI_refinement T_res T_hid).

(* judge the composition of S and T is insecure *)
(* S_T := "IA [s4_t2, s8_t2, s7_t1, s3_t1, s6_t0, s5_t0, s0_t0] (s0_t0) 
[H1, a] [] [b, H2, e] 
[s0_t0->(H1)s5_t0, s5_t0->(a)s6_t0, s6_t0->(b)s7_t1, 
s7_t1->(H2)s8_t2, s3_t1->(H2)s4_t2]"*)

Definition S_T_res:IA :=
IAutomaton.restriction S_T (ASet.GenActs [&"H1"]).

Definition S_T_hid:IA :=
IAutomaton.hiding S_T (ASet.GenActs [&"H1"]).

Eval compute in :> S_T_res.
Eval compute in :> S_T_hid.

Eval compute in (SIRGNNI_refinement S_T_res S_T_hid).
