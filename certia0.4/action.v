(* action.v

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

Require Export element.
Require Import MSets.
Require Import String.

(** define an inductive type for the label of action*)
Inductive Act : Type :=
 | act: Element.t -> Act.

Notation "'&' ac" := (act (lbl ac))  (at level 40).

(** define the module of action as a decidable type of action*)
Definition eq_Act (a a':Act):Prop :=
 match a,a' with
 | act e, act e' => Element.eq e e'
 end.

Definition eq_Act_dec : forall a a':Act, {eq_Act a a'}+{~ eq_Act a a'}.
induction a,a'; simpl.
induction t,t0; simpl.
 apply Element.eq_dec.
 right; intro H; inversion H.
 right; intro H; inversion H.
 apply Element.eq_dec.
Defined.

Definition beq_Act (x y:Act) :bool := 
  match x,y with
  | (act sx), (act sy) => Element.beq sx sy
  end.

Module Action <: DecidableType.

Definition t := Act.

Definition eq: t->t->Prop :=eq_Act.

Instance eq_equiv: Equivalence eq.
split.
 unfold Reflexive. induction x; simpl. apply eq_Elt_refl.
 unfold Symmetric. induction x,y; simpl. apply eq_Elt_sym.
 unfold Transitive. induction x,y,z; simpl. apply eq_Elt_trans.
Defined.

Definition eq_dec := eq_Act_dec.

Definition beq := beq_Act.

End Action.

(**define the set of action as a set *)
Module ASet <: WSets.
Include MSetWeakList.Make Action.

(*for the replacement of IA, find any action
both in A and X, and replace these actions in A with a*)
Fixpoint replace_actions_aux (A:list elt) (X:t) (act:Act): t :=
 match A with
 | nil => empty
 | cons a sa =>
   if (mem a X) then (add act (replace_actions_aux sa X act))
   else (add a (replace_actions_aux sa X act))
 end.
Definition replace_actions (A X:t) (act:Act) : t :=
  replace_actions_aux (elements A) X act.

(** lemmas used for the proof of set operations, e.g. shared_composable_eq of IA *)
Lemma inter_a_union_empty:
forall (A B C:t), Equal (inter C (union A B)) empty ->
  (Equal (inter C A) empty /\ Equal (inter C B) empty).
Proof.
 unfold Equal. intros. split.
 induction a; simpl; split. 
   destruct (H (act t0)). intros; apply H0.
   rewrite (inter_spec C (union A B)); rewrite (inter_spec C A) in H2. split.
   apply H2. rewrite (union_spec A B). left. apply H2.
   intro H'; inversion H'.
 induction a; simpl; split.
   destruct (H (act t0)); intros.
   apply H0. rewrite (inter_spec C (union A B)); rewrite (inter_spec C B) in H2.
   split; destruct H2. apply H2. rewrite (union_spec A B); right; apply H3.
   intro H'; inversion H'.
Qed.

Lemma inter_union_a_empty:
forall (A B C:t), Equal (inter (union A B) C) empty ->
  Equal (inter A C) empty /\ Equal (inter B C) empty.
Proof.
 unfold Equal; intros; split.
 induction a; simpl; split; intros. destruct (H (act t0)). apply H1.
  rewrite (inter_spec (union A B) C); rewrite (inter_spec A C) in H0. split; destruct H0.
  rewrite (union_spec A B). left; apply H0. apply H3. inversion H0.
 induction a; simpl; split; intros. destruct (H (act t0)). apply H1.
  rewrite (inter_spec (union A B) C); rewrite (inter_spec B C) in H0. split; destruct H0.
  rewrite (union_spec A B). right; apply H0. apply H3. inversion H0.
Qed.

Lemma inter_empty_inv:
  forall (A B:t) (e:elt), Equal (inter A B) empty -> In e A -> In e B ->False.
Proof.
 intros. unfold Equal in H. destruct (H e).
 assert (In e (inter A B)). apply inter_spec. split; auto. apply H2 in H4. inversion H4.
Qed.

(** auxiliary functions for debugging*)
Fixpoint GenActs (acts: list elt): t :=
  match acts with
  | nil => empty
  | cons a acts' => add a (GenActs acts')
  end.

Fixpoint display (l:list elt): string :=
 match l with
 | nil => EmptyString
 | cons a l' => match l' with
    | nil => match a with (act e) => Element.display e end
    | cons _ _ => match a with (act e) => 
         String.append (Element.display e) (append ", " (display l'))
         end
    end
 end.

(*test case
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Eval compute in GenActs [&"msg",&"ack",&"nack"].
Eval compute in display (elements (ASet.GenActs [&"msg",&"ack",&"nack"])).
*)

End ASet.


