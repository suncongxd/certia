(** element.v

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
Require Import Ascii.
Require Import Equalities.

Inductive Elt: Set :=
| lbl : string -> Elt
| cpl : string -> Elt -> Elt.

Definition beq_s (s s':string): bool := andb (prefix s s') (prefix s' s).

Definition neq_substr: forall (a:ascii) (s:string), ~(String a s =s).
induction s; simpl.
 intro. inversion H.
 intro. apply IHs. inversion H. rewrite H2. apply H2.
Defined.

Inductive eq_Elt: Elt -> Elt -> Prop :=
| eq_lbl: forall s s':string, s=s' -> eq_Elt (lbl s) (lbl s')
| eq_cpl: forall (s s':string) (e e':Elt),
    (s=s' /\ eq_Elt e e') -> eq_Elt (cpl s e) (cpl s' e').

Definition eq_Elt_refl:
  forall e:Elt, eq_Elt e e.
induction e; simpl. apply eq_lbl; auto. apply eq_cpl; auto.
Defined.

Definition eq_Elt_sym:
  forall e e':Elt, eq_Elt e e' -> eq_Elt e' e.
induction e,e'; simpl; intro H; inversion H.
 rewrite H2; apply eq_lbl; reflexivity.
 destruct H1 as [H5 H6]; rewrite H5; apply eq_cpl; split.
   reflexivity. apply IHe. apply H6.
Defined.

Definition eq_Elt_trans:
  forall e e1 e2:Elt, eq_Elt e e1 -> eq_Elt e1 e2 -> eq_Elt e e2.
induction e,e1,e2; simpl; intros H1 H2; try inversion H1; try inversion H2.
  rewrite H3.  rewrite H6. apply eq_lbl. reflexivity.
  destruct H0; destruct H7; apply eq_cpl; split. rewrite H0. apply H7.
  eapply IHe. apply H11. apply H12.
Defined.

Definition eq_Elt_dec: 
  forall e e':Elt, {eq_Elt e e'}+{~ eq_Elt e e'}.
induction e; induction e'; simpl; auto.
2: right; intro H; inversion H.
2: right; intro H; inversion H.
assert ({s=s0}+{~s=s0}).
  apply string_dec. destruct H.
  left; apply eq_lbl; auto.
  right. intro H; inversion H. apply n. apply H2.
assert ({s=s0}+{~s=s0}).
  apply string_dec.
destruct H; destruct IHe'.
  destruct (IHe e'). left. apply eq_cpl. split; auto.
  right; intro H. apply n. inversion H. destruct H1. apply H5.
  destruct (IHe e'). left. apply eq_cpl. split; auto.
  right; intro H; apply n0. inversion H. destruct H1. apply H5.
  right; intro H; apply n; inversion H. destruct H1. apply H1.
  right; intro H; apply n; inversion H. destruct H1. apply H1.
Defined.

(*Definition func (e1 e2:Elt): bool := if (eq_Elt_dec e1 e2) then true else false.
Eval compute in (func (lbl "s1") (lbl "s0")).*)

Fixpoint beq_Elt (e e':Elt): bool :=
  match e,e' with
  | lbl s,lbl s' => beq_s s s'
  | lbl _, cpl _ _ => false
  | cpl _ _, lbl _ => false
  | cpl s e1, cpl s' e2 => andb (beq_s s s') (beq_Elt e1 e2)
  end.

Module Element <: DecidableType.
Definition t:=Elt.

Definition eq: t->t->Prop := eq_Elt.

Instance eq_equiv: Equivalence eq_Elt.
 split.
 unfold Reflexive. apply eq_Elt_refl.
 unfold Symmetric. apply eq_Elt_sym.
 unfold Transitive. apply eq_Elt_trans.
Defined.

Definition eq_dec := eq_Elt_dec.

Definition beq : t->t->bool :=beq_Elt.

Fixpoint prod (e e':t) :t :=
  match e with
  | lbl s => cpl s e'
  | cpl s e'' => cpl s (prod e'' e')
  end.

(**for debugging*)
Fixpoint display (e:t): string :=
  match e with
  | lbl s => s
  | cpl s e' => append s (append "_" (display e'))
  end.
End Element.