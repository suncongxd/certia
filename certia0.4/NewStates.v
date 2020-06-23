(* NewStates.v

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
Require Export state.
Require Export NewElement.

Module NewState <: DecidableType.
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

Definition prod (s s':t):t :=
  match s,s' with
  | st e, st e' => st (NewElement.prod e e')
  end.
End NewState.


Module NewSSet <: WSets.
Include MSetWeakList.Make NewState.

Fixpoint find_in_st (s:elt) (l: list elt): bool :=
  match l with
  | nil => false
  | cons a tl => 
     match s, a with
     | st s',st a' => if NewElement.beq_disorder s' a' then true
        else find_in_st s tl
     end
  end.

Fixpoint prod_append_aux (a:elt) (l: list elt) (current_result:t): t:=
  match l with
  | nil => current_result
  | cons b l' => let c:=(NewState.prod a b) in
     if (find_in_st c (elements current_result)) then
        prod_append_aux a l' current_result
     else (prod_append_aux a l' (add c current_result))
  end.

Fixpoint prod_append (l l':list elt) (current_res:t): t :=
  match l with
  | nil => current_res
  | cons a tl => 
      prod_append tl l' (prod_append_aux a l' current_res)
  end.

Definition prod_disorder (l l':t): t := 
  prod_append (elements l) (elements l') empty.

Fixpoint power_states_aux (l:t) (n:nat): t:=
  match n with
  | O => l
  | S p => prod_disorder l (power_states_aux l p)
  end.
Definition power_states (l:t): t :=
  power_states_aux l (cardinal l).

Fixpoint get_st (s:elt) (l: list elt): option elt :=
  match l with
  | nil => None
  | cons a tl => 
     match s, a with
     | st s',st a' => if NewElement.beq_disorder s' a' then Some a
        else get_st s tl
     end
  end.

Definition gen_Trans (q q':elt) (a:Action.t) 
                     (states: list elt): option Trans :=
  let q0:= get_st q states in
  let q1:= get_st q' states in
  match q0,q1 with
  | None,_ => None
  | Some q0',None => None
  | Some q0',Some q1' => Some (trans q0' a q1')
  end.

Definition move (s0:elt) (a0: Act) (sts:list elt) (trs: list Trans) : option elt :=
  let s:=get_st s0 sts in
  match s with
  | None => Some s0 (* impossible *)
  | Some (st e) => let e':=NewElement.move_aux e a0 trs in
     ( get_st (st e') (sts) )
  end.

(***************** subset construction ****************************)
(*vis: the set of states visited, initially {s0}
  invis: the set of states invisited, initially {s0}
  trs: the set of transitions of the NFA 
  returns the set of transitions finally derived*)
Fixpoint subset_const (vis invis: NewSSet.t) (acts:ASet.t)
              (sts: NewSSet.t) (trs: list Trans) (n:nat): TSet.t :=
match n with
| O => TSet.empty
| S p =>
  ( let s:= choose invis in
  match s with
  | None => TSet.empty
  | Some s' =>
    let invis':= remove s' invis in
      (fix f (actions: list Act): TSet.t :=
        match actions with
        | nil => TSet.empty
        | cons a actions' =>
          let s1:= move s' a (elements sts) trs in
          match s1 with
          | None =>  f actions'
          | Some s2 =>
            let tr:= gen_Trans s' s2 a (elements sts) in
            match tr with
            | None => f actions'
            | Some tr' => 
               if (mem s2 vis) then TSet.union (TSet.add tr' (f actions'))
                       (subset_const vis invis' acts sts trs p)
               else TSet.union (TSet.add tr' (f actions'))
                   (subset_const (add s2 vis) (add s2 invis') acts sts trs p)
            end
          end
        end
      ) (ASet.elements acts)   
  end )
end.

Fixpoint convertSSet2NewSSet_aux (sts: list State.t): NewSSet.t :=
  match sts with
  | nil => empty
  | cons s sts' => NewSSet.add s (convertSSet2NewSSet_aux sts')
  end.
Definition convertSSet2NewSSet (sset: SSet.t) : NewSSet.t :=
  convertSSet2NewSSet_aux (SSet.elements sset).

End NewSSet.