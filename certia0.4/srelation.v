(** srelation.v

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

Require Import MSets.
Require Export state.
Require Export element.

Inductive SRel: Type := srel: St -> St -> SRel.

Inductive eq_SRel: SRel->SRel->Prop :=
| srel_ident: forall e:SRel, eq_SRel e e
| srel_pair: forall s1 s2 s1' s2':St, (eq_St s1 s1') -> (eq_St s2 s2') ->
  eq_SRel (srel s1 s2) (srel s1' s2').

Definition eq_SRel_dec: forall e e':SRel, {eq_SRel e e'}+{~ eq_SRel e e'}.
induction e,e'; simpl.
assert ({eq_St s s1} + {~ eq_St s s1}). apply eq_St_dec.
assert ({eq_St s0 s2} + {~ eq_St s0 s2}). apply eq_St_dec.
destruct H; destruct H0.
 left;apply srel_pair; auto.
 right. intro H; elim n. inversion H; subst.
   induction s2; simpl. apply eq_Elt_refl. apply H5.
 right. intro H; elim n. inversion H; subst.
   induction s1; simpl. apply eq_Elt_refl. apply H3.
 right. intro H; inversion H; subst. apply n0.
   induction s2; simpl. apply eq_Elt_refl. apply n0. apply H5.
Defined.

Definition eq_SRel_sym: forall e e':SRel, eq_SRel e e' -> eq_SRel e' e.
induction e,e';simpl. intro H.
apply srel_pair.
 inversion H; subst. induction s1; simpl; apply eq_Elt_refl.
   induction s,s1; simpl. inversion H3; subst. apply eq_Elt_refl. apply eq_cpl.
   destruct H0; split. auto. apply eq_Elt_sym; auto.
 inversion H; subst. induction s2; simpl; apply eq_Elt_refl.
   induction s2,s0; simpl. inversion H5; subst. apply eq_Elt_refl. apply eq_cpl.
   destruct H0; split. auto. apply eq_Elt_sym; auto.
Defined.

Definition eq_SRel_refl: forall e:SRel, eq_SRel e e.
induction e; simpl. apply srel_ident.
Defined.

Lemma eq_SRel_rev: forall s s1 s' s1':St,
 eq_SRel (srel s s1) (srel s' s1') -> eq_St s s' /\ eq_St s1 s1'.
Proof.
induction s,s1,s',s1'; simpl.
intro H; inversion H. split; apply eq_Elt_refl.
 split. inversion H3; subst. apply eq_Elt_refl. apply eq_cpl. apply H6.
 inversion H5; subst. apply eq_Elt_refl. apply eq_cpl. apply H6.
Qed.

Definition eq_SRel_trans: forall e e1 e2:SRel, eq_SRel e e1 -> eq_SRel e1 e2 -> eq_SRel e e2.
induction e,e1,e2; simpl; intros.
apply eq_SRel_rev in H. apply eq_SRel_rev in H0. destruct H; destruct H0. apply srel_pair.
  induction s,s1,s3; simpl. unfold eq_St in H,H0. eapply eq_Elt_trans. apply H. apply H0.
  induction s0,s2,s4; simpl. unfold eq_St in H1,H2. eapply eq_Elt_trans. apply H1. apply H2.
Defined.

Definition beq_SRel (e e': SRel): bool :=
  match e,e' with
  | (srel s s1),(srel s' s1') => andb (beq_St s s') (beq_St s1 s1')
  end.

Module SRelElt <: DecidableType.
Definition t := SRel.
Definition eq := eq_SRel.
Definition eq_dec := eq_SRel_dec.
Instance eq_equiv : Equivalence eq.
 split.
 unfold Reflexive. apply eq_SRel_refl.
 unfold Symmetric. apply eq_SRel_sym.
 unfold Transitive. apply eq_SRel_trans.
Defined.
Definition beq := beq_SRel.
End SRelElt.

Module SRelSet <: WSets.
Include MSetWeakList.Make SRelElt.

End SRelSet.
