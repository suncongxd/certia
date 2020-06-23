(* NewElement.v

   Copyright (C) 2017, Cong Sun

   This code is a part of the subset construction algorithm.

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
Require Export transition.
Require Export action.


Module NewElement <: DecidableType.
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

(* used in prod *)
Fixpoint find_in (s:string) (e':t): bool :=
  match e' with
  | lbl s' => beq_s s s'
  | cpl s' e'' => orb (beq_s s s') (find_in s e'')
  end.

(* the product of elements avoiding duplicated label *)
Fixpoint prod (e e':t) :t :=
  match e with
  | lbl s => if (find_in s e') then e' else (cpl s e')
  | cpl s e'' => if (find_in s e') then (prod e'' e')
     else (prod e'' (cpl s e'))
  end.

(* used in beq_disorder *)
Fixpoint bsubset (e e':t) {struct e}: bool :=
  match e with
  | lbl s => (find_in s e')
  | cpl s e'' => andb (NewElement.find_in s e') (bsubset e'' e')
  end.

Definition beq_disorder (e e':t): bool :=
  andb (bsubset e e') (bsubset e' e).


(*used in move_aux *)
Fixpoint prod2 (e e':t) :t :=
  if beq_Elt e' (lbl "") then e
  else 
    match e with
    | lbl s => if (find_in s e') then e' else (cpl s e')
    | cpl s e'' => if (find_in s e') then (prod e'' e')
       else (prod e'' (cpl s e'))
    end.
(* requires e0 from the set of disordered states,
   the returned Elt should be then converted to a state in the set of disordered states *)
Fixpoint move_aux (e0:t) (a0: Act) (trs: list Trans) :t :=
  match trs with
  | nil => (lbl "") (*notice*)
  | cons (trans (st q) a (st q')) trs' => 
        if andb (bsubset q e0) (beq_Act a0 a) then (prod2 q' (move_aux e0 a0 trs'))
        else (move_aux e0 a0 trs')
  end.

(**for debugging*)
Fixpoint display (e:t): string :=
  match e with
  | lbl s => s
  | cpl s e' => append s (append "_" (display e'))
  end.
End NewElement.