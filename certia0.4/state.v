(** state.v

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
Require Import String.

Require Export element.

Inductive St:Type :=
 | st: Element.t -> St.

Notation "'$' ss" := (st (lbl ss))   (at level 40).

Definition eq_St (s s':St): Prop :=
  match s,s' with
  | st e,st e' => Element.eq e e'
  end.

Definition eq_St_dec : forall s s':St, {eq_St s s'}+{~ eq_St s s'}.
induction s,s'; simpl.
induction t,t0; simpl.
 apply Element.eq_dec.
 right; intro H; inversion H.
 right; intro H; inversion H.
 apply Element.eq_dec.
Defined.

Definition beq_St (s s':St): bool :=
  match s,s' with
  | st e,st e' => Element.beq e e'
  end.


Module State <: DecidableType.

Definition t := St.

Definition eq: t->t->Prop := eq_St.

Instance eq_equiv: Equivalence eq.
split.
 unfold Reflexive. induction x; simpl. apply eq_Elt_refl.
 unfold Symmetric. induction x,y; simpl. apply eq_Elt_sym.
 unfold Transitive. induction x,y,z; simpl. apply eq_Elt_trans.
Defined.

Definition eq_dec := eq_St_dec.

Definition beq := beq_St.

Definition prod (s s':t) :t :=
  match s,s' with
  | st e, st e' => st (Element.prod e e')
  end.

End State.

(** Module for the set of states *)
Module SSet <: WSets.
Include MSetWeakList.Make State.

(** state products *)
Fixpoint elt_prod_aux (s:elt) (l:list elt): t :=
  match l with
   | nil => empty
   | cons a l' => add (State.prod s a) (elt_prod_aux s l')
  end.
Definition elt_prod (s:elt) (l:t) :t :=
   elt_prod_aux s (elements l).

Fixpoint prod_aux (l:list elt) (l':t): t :=
  match l with
    | nil => empty
    | cons a ls => union (elt_prod a l') (prod_aux ls l')
  end.
Definition prod (l l':t): t := prod_aux (elements l) l'.

(** auxiliary functions for debugging*)
(** generate a state set*)
Fixpoint GenSts (l:list elt): t :=
  match l with
  | nil => empty
  | cons a l' => add a (GenSts l')
  end.

(*test:
Eval compute in (State.eq_dec ($ "s0") ($ "s1")).
Eval compute in eq_St ($ "s0") ($ "s1").
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Eval compute in (GenSts [$"s0",$"s1",$"s2"]).
Eval compute in (elements (GenSts [$"s0",$"s1"])).*)

Fixpoint display (l:list elt): string :=
  match l with
  | nil => EmptyString
  | cons a l => 
     match l with 
     | nil => match a with (st e) => Element.display e end
     | cons _ _ => match a with (st e) =>
        String.append (Element.display e) (String.append ", " (display l))
        end
     end
  end.

(*test
Definition l: list elt :=
  (st (lbl "a"))::(st (cpl "aa" (cpl "bb" (lbl "cc"))))::nil.
Eval compute in display l.
Definition l2: list elt := nil.
Eval compute in display l2.
*)

End SSet.









