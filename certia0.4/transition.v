(* transition.v

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

Require Export action.
Require Export state.
Require Import MSets.
Require Import String.

Inductive Trans :Type :=
 | trans: St -> Act -> St -> Trans.

Notation " p '->{' t '}' q" := (trans (st (lbl (p))) (act (lbl (t))) (st (lbl (q)))) 
     (at level 41).

Inductive eq_Trans: Trans->Trans->Prop :=
  | trs_ident : forall t:Trans, eq_Trans t t
  | trs_pair: forall (s s' s1 s1':St) (a a':Act),
     (eq_St s s') -> (eq_Act a a') -> (eq_St s1 s1') -> 
     (eq_Trans (trans s a s1) (trans s' a' s1')).

Definition eq_Trans_dec: forall t t':Trans, {eq_Trans t t'}+{~ eq_Trans t t'}.
induction t,t'; simpl.
assert ({eq_St s s1}+{~ eq_St s s1}). apply eq_St_dec.
assert ({eq_Act a a0}+{~ eq_Act a a0}). apply eq_Act_dec.
assert ({eq_St s0 s2}+{~ eq_St s0 s2}). apply eq_St_dec.
destruct H; destruct H0; destruct H1.
 left. apply trs_pair; auto.
 right. intro H. apply n. inversion H.
   induction s2;simpl;apply eq_Elt_refl. apply H8.
 right. intro H; apply n. inversion H.
   induction a0; simpl; apply eq_Elt_refl. apply H7.
 right. intro H; apply n0. inversion H.
   induction s2; simpl; apply eq_Elt_refl. apply H8.
 right. intro H; apply n; inversion H.
   induction s1; simpl; apply eq_Elt_refl. apply H4.
 right. intro H; apply n; inversion H.
   induction s1; simpl; apply eq_Elt_refl. apply H4.
 right. intro H; apply n; inversion H.
   induction s1; simpl; apply eq_Elt_refl. apply H4.
 right. intro H; apply n; inversion H.
   induction s1; simpl; apply eq_Elt_refl. apply H4.
Defined.

Definition beq_Trans (t t':Trans): bool :=
  match t,t' with
  | (trans s a s1),(trans s' a' s1') =>
    andb (andb (beq_St s s') (beq_Act a a')) (beq_St s1 s1')
  end.

Definition eq_Trans_sym: forall x y : Trans, eq_Trans x y -> eq_Trans y x.
induction x,y; simpl; intros.
apply trs_pair; inversion H.
 induction s1; simpl. apply eq_Elt_refl.
 induction s1,s; simpl. inversion H4; subst.
   apply eq_Elt_refl. apply eq_cpl. 
   destruct H9; split. auto. apply eq_Elt_sym. apply H1.
 induction a0; simpl. apply eq_Elt_refl.
 induction a,a0; simpl. inversion H7; subst.
   apply eq_Elt_refl. apply eq_cpl.
   destruct H9; split. auto. apply eq_Elt_sym. apply H1.
 induction s2; simpl. apply eq_Elt_refl.
 induction s2,s0; simpl. inversion H8; subst.
   apply eq_Elt_refl. apply eq_cpl.
   destruct H9; split. auto. apply eq_Elt_sym. apply H1.
Defined.

Definition eq_Trans_trans: 
  forall x y z : Trans, eq_Trans x y -> eq_Trans y z -> eq_Trans x z.
induction x,y,z; simpl. intros.
inversion H; inversion H0; subst; auto.
apply trs_pair.
 induction s,s1,s3; simpl in *|-*.
  eapply element.eq_Elt_trans. apply H5. apply H14.
 induction a,a0,a1; simpl in *|-*.
  eapply element.eq_Elt_trans. apply H8. apply H17.
 induction s0,s2,s4; simpl in *|-*.
  eapply element.eq_Elt_trans. apply H9. apply H18.
Defined.

Module Transition <: DecidableType.

Definition t:=Trans.

Definition eq: t->t->Prop := eq_Trans.

Instance eq_equiv: Equivalence eq.
split.
 unfold Reflexive. apply trs_ident.
 unfold Symmetric. apply eq_Trans_sym.
 unfold Transitive. apply eq_Trans_trans.
Defined.

Definition eq_dec := eq_Trans_dec.

Definition beq: t->t->bool := beq_Trans.

(* for debugging*)
Definition display (tr:t): string :=
  match tr with
  | trans (st e1) (act e2) (st e3) =>
    String.append (Element.display e1) (
    String.append "->(" (
    String.append (Element.display e2) (
    String.append ")" (Element.display e3)
    )))
  end.
End Transition.


Module TSet <: WSets.
Include MSetWeakList.Make Transition.

Definition t_states := SSet.t.
(*Definition t_st := State.t.*)
Definition t_actions := ASet.t.

(** find the states directed by trans from q*)
Fixpoint get_next_aux (trs:list elt) (q:St) :  t_states :=
  match trs with
  | nil => SSet.empty
  | (cons (trans q' _ q'') trs') => 
     if State.beq q q' then SSet.add q'' (get_next_aux trs' q)
     else get_next_aux trs' q
  end.
Definition get_next (trs:t) (q:St) : t_states :=
  get_next_aux (elements trs) q.

(** find the actions of transitions directed by trans from q, and in a set A,
used to derive A^I(q), A^H(q), and A^O(q) *)
Fixpoint actions_enabled_aux (trs:list elt) (q:St) (A:t_actions): t_actions :=
  match trs with
  | nil => ASet.empty
  | (cons (trans q' a _) trs') =>
    if andb (State.beq q q') (ASet.mem a A) then ASet.add a (actions_enabled_aux trs' q A)
    else (actions_enabled_aux trs' q A)
  end.
Definition actions_enabled (trs:t) (q:St) (A:t_actions): t_actions :=
  actions_enabled_aux (elements trs) q A.

(** for the restriction, hiding, replacement of IA *)
Definition diff_by_acts_aux (X:t_actions) (e: elt): bool :=
  match e with (trans _ a _) => negb (ASet.mem a X) end.
Definition diff_by_acts (B:t) (X:t_actions): t :=
 filter (diff_by_acts_aux X) B.

(** for the replacement, restriction and hiding of actions *)
Fixpoint replace_trans_aux (trs:list elt) (X:t_actions) (act:Act) : t :=
 match trs with
 | nil => empty
 | cons tr trtl =>
    match tr with trans s a s' =>
     if (ASet.mem a X) then add (trans s act s') (replace_trans_aux trtl X act)
     else add tr (replace_trans_aux trtl X act)
   end
 end.
Definition replace_trans (trs: t) (X:t_actions) (act:Act) :t :=
  replace_trans_aux (elements trs) X act.

(** this section is used to generate the set of transitions, T_{P\otimes Q} *)
(** the auxiliary functions for T_{P\otimes Q} *)
Fixpoint transPairing_r_states (tr:elt) (states: list St) : t :=
  match states with
  | nil => empty
  | cons sa states' => 
    match tr with trans s a s' => 
      add (trans (State.prod s sa) a (State.prod s' sa)) (transPairing_r_states tr states')
    end
  end.

Fixpoint transPairing_l_states (tr:elt) (states: list St) : t :=
  match states with
  | nil => empty
  | cons sa states' => 
    match tr with trans s a s' => 
      add (trans (State.prod sa s) a (State.prod sa s')) (transPairing_l_states tr states')
    end
  end.

Fixpoint transEltSetProd (tr:elt) (trs':list elt): t :=
  match trs' with
  | nil => empty
  | cons (trans p b p') tl => 
     match tr with (trans s a s') =>
       if Action.beq a b then
         add (trans (State.prod s p) a (State.prod s' p')) (transEltSetProd tr tl)
       else (transEltSetProd tr tl)
     end
  end.

(** generate the first subset of T_{P\otimes Q} *)
Fixpoint transSetProd_r (trs: list elt) (neg_shared: t_actions) (states: t_states): t :=
 match trs with
 | nil => empty
 | cons (trans s a s') trs' =>
   if (ASet.mem a neg_shared) then
     union (transPairing_r_states (trans s a s') (SSet.elements states)) 
           (transSetProd_r trs' neg_shared states)
   else (transSetProd_r trs' neg_shared states)
 end.

(** generate the second subset of T_{P\otimes Q} *)
Fixpoint transSetProd_l (trs: list elt) (neg_shared: t_actions) (states: t_states): t :=
 match trs with
 | nil => empty
 | cons (trans s a s') trs' =>
   if (ASet.mem a neg_shared) then 
     union (transPairing_l_states (trans s a s') (SSet.elements states))
           (transSetProd_l trs' neg_shared states)
   else transSetProd_l trs' neg_shared states
 end.

(** generate the third subset of T_{P\otimes Q} *)
Fixpoint transSetProd_m (trs trs':list elt) (shared: t_actions): t :=
  match trs, trs' with
  | nil, _ => empty
  | _, nil => empty
  | cons (trans s a s') trs1, _ =>
    if (ASet.mem a shared) then 
      union (transEltSetProd (trans s a s') trs') (transSetProd_m trs1 trs' shared)
    else (transSetProd_m trs1 trs' shared)
  end.
(** ******************************************* *)

(** functions for removing unreachable states of an interface automaton *)
Fixpoint nextStates (vis:t_states) (trs:list elt) : t_states :=
 match trs with
  | nil => SSet.empty
  | cons (trans s _ s') trs' => 
    if SSet.mem s vis then SSet.add s' (nextStates vis trs')
    else nextStates vis trs'
  end.

Definition nextTrans_aux (vis:t_states) (t:elt): bool :=
 match t with
 | trans s _ _ => if SSet.mem s vis then true else false
 end.
Definition nextTrans (vis:t_states) (trs:t):t :=
 filter (nextTrans_aux vis) trs.

(** A BFS to collect all the states reachable from the initial vis of states *)
Fixpoint reachable_state (n:nat) (vis:t_states) (trs:t): t_states :=
 match n with
 | O => vis (*should be avoid by setting the initial n with the number of transitions*)
 | S p =>
   let tmpSts := nextStates vis (elements trs) in
   let tmpTrs := nextTrans vis trs in
     if is_empty tmpTrs then vis
     else reachable_state p (SSet.union tmpSts vis) (diff trs tmpTrs)
 end.

(** A BFS to collect all the transitions reachable from the initial vis of states,
the initial vis_trs should be set as the transitions already contained by the initial v *)
Fixpoint reachable_trans (n:nat) (vis:t_states) (trs: t) (vis_trs:t) : t :=
 match n with
 | O => vis_trs
 | S p =>
   let tmpSts := nextStates vis (elements trs) in
   let tmpTrs := nextTrans vis trs in
     if is_empty tmpTrs then vis_trs
     else reachable_trans p (SSet.union tmpSts vis) (diff trs tmpTrs) (union vis_trs tmpTrs)
 end.

(** derive the set of actions used in identifying the error state of IA production *)
Fixpoint next_acts_in_acts (trs:list elt) (q:State.t) (acts:t_actions): t_actions:=
  match trs with
  | nil => ASet.empty
  | cons (trans s a s') trs' =>
    if andb (State.beq q s) (ASet.mem a acts) then
       ASet.add a (next_acts_in_acts trs' q acts)
    else next_acts_in_acts trs' q acts
  end.

(** find the transitions in trs driven by the actions of acts *)
Fixpoint getTransByActions (trs:list elt) (acts:t_actions): t :=
  match trs with
  | nil => empty
  | cons (trans q a q') trs' =>
    if ASet.mem a acts then
      add (trans q a q') (getTransByActions trs' acts)
    else getTransByActions trs' acts
  end.

(** find whether target is reachable from the set of states vis *)
Definition target_reachable (n:nat) (target:State.t) (vis:t_states) (trs:t): bool :=
  SSet.mem target (reachable_state n vis trs).

(** find whether there is a state in targets reachable from vis *)
Definition targets_reachable (n:nat) (targets:t_states) (vis:t_states) (trs:t): Prop :=
  ~(SSet.Empty (SSet.inter (reachable_state n vis trs) targets)).

Definition b_targets_reachable (n:nat) (targets:t_states) (vis:t_states) (trs:t): bool :=
  negb (SSet.is_empty (SSet.inter (reachable_state n vis trs) targets)).

(** pick the states in srcs which cannot reach the targets by trs *)
Fixpoint getUnreachableSources (srcs:list St) (targets:t_states) (trs:t): t_states :=
match srcs with
| nil => SSet.empty
| cons s src' =>
  let b := (SSet.is_empty ( SSet.inter 
           (reachable_state (cardinal trs) (SSet.add s (SSet.empty)) trs) targets)) in
  if b then SSet.add s (getUnreachableSources src' targets trs)
  else getUnreachableSources src' targets trs
end.

(** trim the transitions cause incompatibility, used in the composition of IAs,
 used in Def.15 of de Alfaro'05, but in this version of certia, this definition
 is not used & we use Def.10 of de Alfaro'01 as the definition of composition.*)
Fixpoint trimBoundaryTrans (srcs:t_states) (acts:t_actions) (trs:list elt):t :=
  match trs with
  | nil => empty
  | cons (trans q a q') trs' =>
    if andb (andb (SSet.mem q srcs) (ASet.mem a acts))
            (negb (SSet.mem q' srcs)) then
       trimBoundaryTrans srcs acts trs'
    else add (trans q a q') (trimBoundaryTrans srcs acts trs')
  end.

(** get the transitions whose both ends are in the states *)
Fixpoint getCloseTrans (sts: t_states) (trs:list elt): t :=
  match trs with
  | nil => empty
  | cons (trans s a s') trs' =>
    if andb (SSet.mem s sts) (SSet.mem s' sts) then
      add (trans s a s') (getCloseTrans sts trs')
    else (getCloseTrans sts trs')
  end.

(** *********** auxiliary definitions for refinement ************ *)
Definition epsilon_closure (q:St) (hidden_acts:t_actions) (trs:t): t_states :=
  let hidden_trans := getTransByActions (elements trs) (hidden_acts) in
  reachable_state (cardinal hidden_trans) (SSet.add q SSet.empty) hidden_trans.

(** for each state in epsilon_closure(s), i.e. u, 
find the outsourcing input/output actions from u.
Note that the obsAO(s) find all the outputs from ANY u in epsilon_closure(s), 
while obsAI(s) find the inputs from ALL u in epsilon_closure(s) *)

Fixpoint obsAO_aux (sts: list St) (trs:t) (out_acts: t_actions): t_actions :=
  match sts with
  | nil => ASet.empty
  | cons s sts' =>
    ASet.union (actions_enabled trs s out_acts) (obsAO_aux sts' trs out_acts)
  end.
Definition obsAO (q:St) (hidden_acts out_acts:t_actions) (trs:t) : t_actions :=
  let eps_states := epsilon_closure q hidden_acts trs in
    obsAO_aux (SSet.elements eps_states) trs out_acts.

(* the definition given by de Alfaro, used by alter_sim *)
Fixpoint obsAI_aux (sts: list St) (trs:t) (in_acts: t_actions): t_actions :=
  match sts with
  | nil => in_acts
  | cons s sts' =>
    ASet.inter (actions_enabled trs s in_acts) (obsAI_aux sts' trs in_acts)
  end.
Definition obsAI (q:St) (hidden_acts in_acts:t_actions) (trs:t): t_actions :=
  let eps_states := epsilon_closure q hidden_acts trs in
    obsAI_aux (SSet.elements eps_states) trs in_acts.

(* this definition on obsAI is used by the refinement for SIR-GNNI and SME-NI *)
Fixpoint obsAI_aux2 (sts: list St) (trs:t) (in_acts: t_actions): t_actions :=
  match sts with
  | nil => ASet.empty
  | cons s sts' =>
    ASet.union (actions_enabled trs s in_acts) (obsAI_aux2 sts' trs in_acts)
  end.
Definition obsAI2 (q:St) (hidden_acts in_acts:t_actions) (trs:t): t_actions :=
  let eps_states := epsilon_closure q hidden_acts trs in
    obsAI_aux2 (SSet.elements eps_states) trs in_acts.

Fixpoint ExtDest_aux (trs:list elt) (act:Act) (u_set:t_states): t_states :=
  match trs with
  | nil => SSet.empty
  | cons (trans u b u') trs' =>
    if andb (SSet.mem u u_set) (Action.beq b act) then
      SSet.add u' (ExtDest_aux trs' act u_set)
    else ExtDest_aux trs' act u_set
  end.  

(*Fixpoint post (q:St) (act:Act) (trs:list elt): t_states :=
  match trs with
  | nil => SSet.empty
  | cons (trans p a p') trs' =>
    if andb (State.beq p q) (Action.beq a act) then 
      SSet.add p' (post q act trs')
    else post q act trs'
  end.*)

Fixpoint getStatesByTrans_aux (trs:list elt): SSet.t :=
  match trs with
  | nil => SSet.empty
  | cons (trans q _ q') trs' =>
     SSet.add q (SSet.add q' (getStatesByTrans_aux trs'))
  end.
Definition getStatesByTrans (trs: t): SSet.t :=
  getStatesByTrans_aux (elements trs).

(** auxiliary functions for debugging*)
Fixpoint GenTrs (trs: list elt): t :=
  match trs with
  | nil => empty
  | cons t trs' => add t (GenTrs trs')
  end.

Fixpoint display (trs: list elt): string :=
 match trs with
 | nil => EmptyString
 | cons t trs' => match trs' with
   | nil => Transition.display t
   | cons _ _ => String.append (Transition.display t) (String.append ", " (display trs'))
   end
 end.

End TSet.

