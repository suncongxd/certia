(* IA.v

   Copyright (C) 2017, Cong Sun

   This code is a part of CertIA.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
*)

Require Import String.
Require Export state.
Require Export action.
Require Export transition.
Require Export srelation.

(** The inductive type of interface automaton *)
Inductive IA: Type :=
 | constr_ia: SSet.t -> St 
     -> ASet.t -> ASet.t -> ASet.t -> TSet.t -> IA.

(** The module definition of interface automaton *)
Module IAutomaton.

Definition t:Type :=IA.

Definition t_states :=SSet.t.
Definition t_st := State.t.
Definition t_actions := ASet.t.
Definition t_trans :=TSet.t.

(** the getters of interface automaton *)
Definition get_trans (ia:t): t_trans :=
  match ia with constr_ia _ _ _ _ _ tset => tset end.

Definition get_states (ia:t): t_states :=
  match ia with constr_ia sset _ _ _ _ _ => sset end.

Definition get_AI (ia:t): t_actions :=
  match ia with constr_ia _ _ AI _ _ _ => AI end.

Definition get_AO (ia:t): t_actions :=
  match ia with constr_ia _ _ _ AO _ _ => AO end.

Definition get_AH (ia:t): t_actions :=
  match ia with constr_ia _ _ _ _ AH _ => AH end.

Definition get_init (ia:t): t_st :=
  match ia with constr_ia _ init _ _ _ _ => init end.

Definition get_actions (ia:t) : t_actions :=
  match ia with constr_ia _ _ AI AO AH _ => 
    (ASet.union (ASet.union AI AO) AH) end.

Lemma union_actions_eq: forall ia:t,  (get_actions ia) =
  (ASet.union (ASet.union (get_AI ia) (get_AO ia)) (get_AH ia)).
Proof.
intros. induction ia.
unfold get_actions. unfold get_AI. unfold get_AO. unfold get_AH. reflexivity.
Qed.

(** Definition 5, restriction, hiding, replacement of IA *)

Definition restriction (ia:t) (X:t_actions) :t :=
 constr_ia (get_states ia) (get_init ia) 
    (ASet.diff (get_AI ia) X)
    (ASet.diff (get_AO ia) X)
    (get_AH ia) (TSet.diff_by_acts (get_trans ia) X).

Definition hiding (ia:t) (X:t_actions) :t :=
 constr_ia (get_states ia) (get_init ia)
   (ASet.diff (get_AI ia) X)
   (ASet.diff (get_AO ia) X)
   (ASet.union (get_AH ia) X)
   (get_trans ia).

Definition replacement (ia:t) (a:Act) (X:t_actions): t :=
 constr_ia (get_states ia) (get_init ia)
   (ASet.replace_actions (get_AI ia) X a)
   (ASet.replace_actions (get_AO ia) X a)
   (get_AH ia)
   (TSet.replace_trans (get_trans ia) X a).

(** Several basic properties *)
Definition input_deterministic (ia:t): Prop :=
 forall (q q' q'':t_st) (a:Action.t), TSet.In (trans q a q') (get_trans ia) ->
   TSet.In (trans q a q'') (get_trans ia) -> q'=q''.

(** judge the validation of interface automaton, 
input deterministic and the action sets are pairwise disjoint *)
Definition valid_IA (ia:t): Prop :=
  (ASet.Equal (ASet.inter (get_AI ia) (get_AO ia)) ASet.empty) 
  /\ (ASet.Equal (ASet.inter (get_AI ia) (get_AH ia)) ASet.empty) 
  /\ (ASet.Equal (ASet.inter (get_AO ia) (get_AH ia)) ASet.empty)
  /\ (input_deterministic ia).

(** action enabled, action disabled *)
Definition action_enabled (ia:t) (q:t_st): Prop :=
  match SSet.elements (TSet.get_next (get_trans ia) q) with
   | nil => False
   | cons _ _ => True
  end.

Definition action_disabled (ia:t) (q:St): Prop := ~(action_enabled ia q).

(** judge whether ia is closed, i.e., A^I=A^O=empty *)
Definition closed_IA (ia:t) : Prop :=
  ASet.Empty (get_AI ia) /\ ASet.Empty (get_AO ia).

(** COMPATIBILITY AND COMPOSITION *)
Definition composable (ia ia':t) :Prop :=
  (ASet.Equal (ASet.inter (get_AH ia) (get_actions ia')) ASet.empty) /\
  (ASet.Equal (ASet.inter (get_actions ia) (get_AH ia')) ASet.empty) /\
  (ASet.Equal (ASet.inter (get_AI ia) (get_AI ia')) ASet.empty) /\
  (ASet.Equal (ASet.inter (get_AO ia) (get_AO ia')) ASet.empty).

Definition shared (ia ia':t) : t_actions :=
  ASet.inter (get_actions ia) (get_actions ia').

Lemma shared_composable_eq:
  forall ia ia':t, valid_IA ia -> valid_IA ia' ->composable ia ia' -> 
   (ASet.Equal (shared ia ia') 
     (ASet.union (ASet.inter (get_AI ia) (get_AO ia')) (ASet.inter (get_AO ia) (get_AI ia')))).
Proof.
unfold composable, valid_IA, shared, get_actions.
induction ia,ia'; simpl.
intros. 
destruct H as [H2 [H3 [H4 H5]]]. 
destruct H0 as [H6 [H7 [H8 H9]]].
destruct H1 as [H10 [H11 [H12 H13]]].
unfold ASet.Equal.
apply ASet.inter_a_union_empty in H10; destruct H10.
apply ASet.inter_union_a_empty in H11; destruct H11.
apply ASet.inter_a_union_empty in H; destruct H.
apply ASet.inter_union_a_empty in H1; destruct H1.
induction a; simpl; split; intros.
 apply ASet.inter_spec in H15; destruct H15.
  apply ASet.union_spec in H15; apply ASet.union_spec in H16; destruct H15; destruct H16.
  apply ASet.union_spec in H15; apply ASet.union_spec in H16; destruct H15; destruct H16;
  apply ASet.union_spec.
    apply (ASet.inter_empty_inv t1 t6 (act t10)) in H12. inversion H12. auto. auto.
    left. apply ASet.inter_spec; split; auto.
    right. apply ASet.inter_spec; split; auto.
    apply (ASet.inter_empty_inv t2 t7 (act t10)) in H13. inversion H13. auto. auto.
  apply ASet.union_spec in H15; destruct H15.
    apply (ASet.inter_empty_inv t1 t8 (act t10)) in H1. inversion H1. auto. auto.
    apply (ASet.inter_empty_inv t2 t8 (act t10)) in H14. inversion H14. auto. auto.
  apply ASet.union_spec in H16; destruct H16.
    apply (ASet.inter_empty_inv t3 t6 (act t10)) in H. inversion H. auto. auto.
    apply (ASet.inter_empty_inv t3 t7 (act t10)) in H11. inversion H11. auto. auto.
    apply (ASet.inter_empty_inv t3 t8 (act t10)) in H0. inversion H0. auto. auto.
  apply ASet.inter_spec; split.
  apply ASet.union_spec in H15; destruct H15.
  apply ASet.inter_spec in H15; destruct H15.
  apply ASet.union_spec. left. apply ASet.union_spec. left; auto.
  apply ASet.inter_spec in H15; destruct H15.
  apply ASet.union_spec. left. apply ASet.union_spec. right; auto.
  apply ASet.union_spec in H15; destruct H15. apply ASet.inter_spec in H15; destruct H15.
  apply ASet.union_spec. left. apply ASet.union_spec. right; auto.
  apply ASet.inter_spec in H15; destruct H15.
  apply ASet.union_spec. left. apply ASet.union_spec. left; auto.
Qed.

(** definition of the product of interface automata *)
Definition IAProd (ia ia':t) :t :=
 let share := shared ia ia' in 
 match ia, ia' with
  | constr_ia QS qS AI_S AO_S AH_S tranS, constr_ia QT qT AI_T AO_T AH_T tranT =>
    let trans_S_T:= TSet.union 
     (TSet.union 
       (TSet.transSetProd_r 
         (TSet.elements tranS) (ASet.diff (get_actions ia) (get_actions ia')) (QT))
       (TSet.transSetProd_l 
         (TSet.elements tranT) (ASet.diff (get_actions ia') (get_actions ia)) (QS)) )
     (TSet.transSetProd_m 
         (TSet.elements tranS) (TSet.elements tranT) share) in
    let reachable_trans_S_T := TSet.reachable_trans (List.length (TSet.elements trans_S_T))
              (SSet.add (State.prod qS qT) SSet.empty) trans_S_T TSet.empty in
  constr_ia 
   (TSet.getStatesByTrans reachable_trans_S_T) 
   (State.prod qS qT) 
   (ASet.diff (ASet.union AI_S AI_T) share)
   (ASet.diff (ASet.union AO_S AO_T) share)
   (ASet.union (ASet.union AH_S AH_T) share) 
   (reachable_trans_S_T)
  end.
(*old: cost more memory resources
Definition IAProd (ia ia':t) :t :=
 let share := shared ia ia' in 
 match ia, ia' with
  | constr_ia QS qS AI_S AO_S AH_S tranS, constr_ia QT qT AI_T AO_T AH_T tranT =>
    let trans_S_T:= TSet.union 
     (TSet.union 
       (TSet.transSetProd_r 
         (TSet.elements tranS) (ASet.diff (get_actions ia) (get_actions ia')) (QT))
       (TSet.transSetProd_l 
         (TSet.elements tranT) (ASet.diff (get_actions ia') (get_actions ia)) (QS)) )
     (TSet.transSetProd_m 
         (TSet.elements tranS) (TSet.elements tranT) share) in
  constr_ia 
   (TSet.reachable_state (TSet.cardinal trans_S_T) 
                                  (SSet.add (State.prod qS qT) SSet.empty) trans_S_T) 
   (State.prod qS qT) 
   (ASet.diff (ASet.union AI_S AI_T) share)
   (ASet.diff (ASet.union AO_S AO_T) share)
   (ASet.union (ASet.union AH_S AH_T) share) 
   (TSet.reachable_trans (List.length (TSet.elements trans_S_T))
              (SSet.add (State.prod qS qT) SSet.empty) trans_S_T TSet.empty)
  end.
*)
(* remove the unreachable states from SSet.prod QS QT. This helps the getErrorStates *)

(** ********************* Illegal(P,Q)*********************** *)
(** used in getErrorStates, judge whether s is an error state *)
Fixpoint judgeErrorState_aux (shared: list Act) (acts1 acts2 acts3 acts4:t_actions) {struct shared}: bool :=
  match shared with
  | nil => false
  | cons a shared' =>
    if orb (ASet.mem a (ASet.diff acts1 acts2))
           (ASet.mem a (ASet.diff acts3 acts4)) then true
    else judgeErrorState_aux shared' acts1 acts2 acts3 acts4
  end.
(*old:
Fixpoint judgeErrorState_aux (shared: list Act) (acts1 acts2 acts3 acts4:t_actions) {struct shared}: bool :=
  match shared with
  | nil => false
  | cons a shared' =>
    if orb (andb (ASet.mem a acts1) (negb (ASet.mem a acts2)))
           (andb (ASet.mem a acts3) (negb (ASet.mem a acts4))) then true
    else judgeErrorState_aux shared' acts1 acts2 acts3 acts4
  end.*)
Fixpoint judgeErrorState (s: t_st) (AI_P AI_Q AO_P AO_Q:t_actions) 
                         (trsP trsQ: t_trans): bool:=
 match s with
 | st (lbl _) => false (*could not happen in our application*)
 | st (cpl p e) =>
   let shared := ASet.union (ASet.inter AO_P AI_Q) (ASet.inter AO_Q AI_P) in
   let acts1 := TSet.next_acts_in_acts (TSet.elements trsP) (st (lbl p)) AO_P in
   let acts2 := TSet.next_acts_in_acts (TSet.elements trsQ) (st e) AI_Q in
   let acts3 := TSet.next_acts_in_acts (TSet.elements trsQ) (st e) AO_Q in
   let acts4 := TSet.next_acts_in_acts (TSet.elements trsP) (st (lbl p)) AI_P in
     judgeErrorState_aux (ASet.elements shared) acts1 acts2 acts3 acts4
 end.

(** generate the set of illegal states from the transition set of product *)
Fixpoint getErrorStates (ss: list St) (AI_P AI_Q AO_P AO_Q: t_actions)
                        (trsP trsQ: t_trans): t_states :=
 match ss with
 | nil => SSet.empty
 | cons s sts' =>
   if judgeErrorState s AI_P AI_Q AO_P AO_Q trsP trsQ then
     SSet.add s (getErrorStates sts' AI_P AI_Q AO_P AO_Q trsP trsQ)
   else (getErrorStates sts' AI_P AI_Q AO_P AO_Q trsP trsQ)
 end.

Definition Illegal (P Q:t): t_states :=
 getErrorStates (SSet.elements (get_states (IAProd P Q)))
                (get_AI P) (get_AI Q) (get_AO P) (get_AO Q) 
                (get_trans P) (get_trans Q).

(** *********************************************** *)

(** environment of IA *)
Definition Env (R E:t) : Prop :=
(composable R E) /\ (ASet.Equal (get_AI E) (get_AO R)) /\ (SSet.Empty (Illegal R E)).

(** ******************** COMPATIBLE(P,Q) ******************* *)
(** compatibility of IAs, we implements Def.14 of deAlfaro'05. 
The older form (Def.8 of deAlfaro'01) is hard to implement. *)

Definition compatible (ia ia':t): Prop :=
  let product := IAProd ia ia' in
  let all_trans := get_trans product in
  let trs := TSet.getTransByActions (TSet.elements all_trans) (ASet.union (get_AO product) (get_AH product)) in
  let err_states := (Illegal ia ia') in
  ~ TSet.targets_reachable (TSet.cardinal all_trans) 
                                  err_states (SSet.add (get_init product) SSet.empty) trs.

Definition b_compatible (ia ia':t): bool :=
  let product := IAProd ia ia' in
  let all_trans := get_trans product in
  let trs := TSet.getTransByActions (TSet.elements all_trans) (ASet.union (get_AO product) (get_AH product)) in
  let err_states := (Illegal ia ia') in
  negb (TSet.b_targets_reachable (TSet.cardinal all_trans) 
                                  err_states (SSet.add (get_init product) SSet.empty) trs).

Theorem sym_compatible: forall (P Q:t), compatible P Q -> compatible Q P.
Proof.
induction P,Q; simpl; intros.
unfold compatible in *|-*. unfold TSet.targets_reachable in *|-*.
intro H'; apply H.
Admitted.

(** COMPOSITION of COMPATIBLE IAs.
the set of transitions should been trimed according Def.15 of de Alfaro'2005*)

(** derive all the compatible states of product *)
Definition compatible_states_of_product (ia ia':t): t_states :=
  let product := IAProd ia ia' in
  let all_trans := get_trans product in
  let all_states := get_states product in
  let trs := TSet.getTransByActions (TSet.elements all_trans) (ASet.union (get_AO product) (get_AH product)) in
  let err_states := (Illegal ia ia') in
    TSet.getUnreachableSources (SSet.elements (SSet.diff all_states err_states)) err_states trs.

Definition composition (ia ia':t): t :=
  let product := IAProd ia ia' in
  let all_trans := get_trans product in
  let states := compatible_states_of_product ia ia' in
   (constr_ia states (get_init product) (get_AI product) (get_AO product) (get_AH product)
    (TSet.getCloseTrans states (TSet.elements all_trans))).
(*Definition composition (ia ia':t): t :=
  let product := IAProd ia ia' in
  let all_trans := get_trans product in
  let states := compatible_states_of_product ia ia' in
   (constr_ia states (get_init product) (get_AI product) (get_AO product) (get_AH product)
    (TSet.trimBoundaryTrans states (get_AI product) (TSet.elements all_trans))).
*)

(** *************** REFINEMENT ************ *)
(** to implement: alter_sim v u ::= forall a:Act, In a (union (ObsAI v P) (ObsAO u Q)) ->
  forall u':State, In u' (ExtDest Q u a) ->
  exists v':State, In v' (ExtDest P v a) /\
    SRelCons (srel v u) (alter_sim (srel v' u') P Q). **)

Definition ExtDest (v:St) (a:Act) (ia:t) : t_states :=
  let hidden_acts := get_AH ia in
  let trs := get_trans ia in
  let u_set := TSet.epsilon_closure v hidden_acts trs in
    TSet.ExtDest_aux (TSet.elements trs) a u_set.

Fixpoint alter_sim (v u:St) (P Q:t) (n:nat) : SRelSet.t :=
match n with
| O => SRelSet.empty
| S p =>
 let actsP := TSet.obsAI v (get_AH P) (get_AI P) (get_trans P) in
 let actsP_o := TSet.obsAO v (get_AH P) (get_AO P) (get_trans P) in
 let actsQ := TSet.obsAO u (get_AH Q) (get_AO Q) (get_trans Q) in
 let actsQ_i := TSet.obsAI u (get_AH Q) (get_AI Q) (get_trans Q) in
 if negb (andb (ASet.subset actsP actsQ_i) (ASet.subset actsQ actsP_o)) then
  SRelSet.add (srel (st (lbl "err")) (st (lbl "err0"))) SRelSet.empty
 else
  let acts := ASet.union actsP actsQ in
  match (ASet.elements acts) with
  | nil => SRelSet.empty
  | cons a acts' =>
    let destQ:= ExtDest u a Q in
    let destP:= ExtDest v a P in
    match (SSet.elements destQ) with
    | nil => SRelSet.empty
    | cons u' destQ' =>
      (fix f3 (u0:St) (dest_p:list St) (P Q:t) {struct dest_p}: SRelSet.t :=
        match dest_p with
        | nil => SRelSet.add (srel (st (lbl "err")) (st (lbl "err0"))) SRelSet.empty
        | cons v' dest_p' =>
          let tmpSRelSet:=(alter_sim v' u' P Q p) in
          if negb (SRelSet.mem (srel (st (lbl "err")) (st (lbl "err0"))) tmpSRelSet) then
            SRelSet.add (srel v u) tmpSRelSet
          else f3 u0 dest_p' P Q
        end
      ) u' (SSet.elements destP) P Q
    end
  end
end.

Definition Refine (P Q:t): Prop :=
  (ASet.Subset (get_AI P) (get_AI Q))/\
  (ASet.Subset (get_AO Q) (get_AO P))/\
  ~( SRelSet.In (srel (st (lbl "err")) (st (lbl "err0"))) 
     (alter_sim (get_init P) (get_init Q) P Q (TSet.cardinal (get_trans Q))) ).

Definition bRefine (P Q:t): bool :=
  andb (andb (ASet.subset (get_AI P) (get_AI Q)) (ASet.subset (get_AO Q) (get_AO P)))
  (
  negb (SRelSet.mem (srel (st (lbl "err")) (st (lbl "err0"))) 
     (alter_sim (get_init P) (get_init Q) P Q (TSet.cardinal (get_trans Q))) )
  ).

(** auxiliary function for debugging *)
Definition display (ia:t): string :=
 String.append "IA [" (
  String.append (SSet.display (SSet.elements (get_states ia))) (
   String.append "] (" (
    String.append (match (get_init ia) with (st e) => Element.display e end) (
     String.append ") [" (
      String.append (ASet.display (ASet.elements (get_AI ia))) (
       String.append "] [" (
        String.append (ASet.display (ASet.elements (get_AO ia))) (
         String.append "] [" (
          String.append (ASet.display (ASet.elements (get_AH ia))) (
           String.append "] [" (
            String.append (TSet.display (TSet.elements (get_trans ia))) "]"
 ))))))))))).

End IAutomaton.

Notation ":> ia" := (IAutomaton.display ia) (at level 20).
