(* refine.v

   Copyright (C) 2017, Cong Sun

   This code is for the definition of SIR-GNNI and SME-NI.
   This code uses the coq library Certia for interface automata, 
   developed by the author.

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
Require Export IA.

Fixpoint sim_X (v u:St) (P Q:IA) (X:ASet.t) (n:nat) : SRelSet.t :=
match n with
| O => SRelSet.empty
| S p =>
 let obsAI_P := TSet.obsAI2 v (IAutomaton.get_AH P) (ASet.diff (IAutomaton.get_AI P) X) (IAutomaton.get_trans P) in
 let obsAO_P := TSet.obsAO v (IAutomaton.get_AH P) (IAutomaton.get_AO P) (IAutomaton.get_trans P) in
 let obsAO_Q := TSet.obsAO u (IAutomaton.get_AH Q) (IAutomaton.get_AO Q) (IAutomaton.get_trans Q) in
 let obsAI_Q := TSet.obsAI2 u (IAutomaton.get_AH Q) (IAutomaton.get_AI Q) (IAutomaton.get_trans Q) in
 if negb (andb (ASet.equal obsAI_P obsAI_Q) (ASet.subset obsAO_Q obsAO_P)) then
  SRelSet.add (srel (st (lbl "err")) (st (lbl "err0"))) SRelSet.empty
 else
  match (ASet.elements (ASet.union obsAI_Q obsAO_Q)) with (*forall a\in obsAI_Q(u) or obsAO_Q(u)*)
  | nil => SRelSet.empty
  | cons a acts' =>
    let destQ:= IAutomaton.ExtDest u a Q in
    let destP:= IAutomaton.ExtDest v a P in
    match (SSet.elements destQ) with  (*forall u'\in ExtDest_Q(u,a)*)
    | nil => SRelSet.empty
    | cons u' destQ' =>
      (fix f3 (u0:St) (dest_p:list St) (P Q:IA) {struct dest_p}: SRelSet.t :=
        match dest_p with  (*forall v'\in ExtDest_P(v,a)*)
        | nil => SRelSet.add (srel (st (lbl "err")) (st (lbl "err0"))) SRelSet.empty
        | cons v' dest_p' =>
          match (ASet.elements obsAI_P) with          (*forall a0\in obsAI_P(v)-X *)
          | nil =>  (* rule (3) needs not considered *)
            (let tmpSRelSet:=(sim_X v' u' P Q X p) in
             if negb (SRelSet.mem (srel (st (lbl "err")) (st (lbl "err0"))) tmpSRelSet) then
               SRelSet.add (srel v u) tmpSRelSet 
             else f3 u0 dest_p' P Q)
          | cons a0 acts'' =>                         (* rule (3) is considered *)
            let destQ0:= IAutomaton.ExtDest u a0 Q in
            let destP0:= IAutomaton.ExtDest v a0 P in
            match (SSet.elements destP0) with         (*forall v''\in ExtDest_P(v,a0)*)
            | nil =>                                  (* the postcondition of rule(3) needs not be considered *)
               (let tmpSRelSet:=(sim_X v' u' P Q X p) in        
                if negb (SRelSet.mem (srel (st (lbl "err")) (st (lbl "err0"))) tmpSRelSet) then
                 SRelSet.add (srel v u) tmpSRelSet
                else f3 u0 dest_p' P Q)
            | cons v'' destP0' =>                     (* consider the postcondition of rule (3) *)
              (fix f4 (v0:St) (dest_q:list St) (P Q:IA) {struct dest_q}: SRelSet.t :=
                 match dest_q with                    (*forall u''\in ExtDest_Q(u,a0)*)
                 | nil => SRelSet.add (srel (st (lbl "err")) (st (lbl "err0"))) SRelSet.empty
                 | cons u'' dest_q' =>
                   (let tmpSRelSet:=(sim_X v0 u'' P Q X p) in
                     if negb (SRelSet.mem (srel (st (lbl "err")) (st (lbl "err0"))) tmpSRelSet) then (*rule(3) is satisfied*)
                       (let tmpSRelSet1:=(sim_X v' u' P Q X p) in
                       if negb (SRelSet.mem (srel (st (lbl "err")) (st (lbl "err0"))) tmpSRelSet1) then
                         SRelSet.add (srel v u) tmpSRelSet              (*rule(2) is satisfied*)
                       else f3 u0 dest_p' P Q)
                     else f4 v0 dest_q' P Q)
                end
              ) v'' (SSet.elements destQ0) P Q
            end
          end
        end
      ) u' (SSet.elements destP) P Q
    end
  end
end.

Definition SIRGNNI_refinement (P Q:IA): bool :=
  andb (andb (ASet.subset (IAutomaton.get_AI P) 
             (IAutomaton.get_AI Q)) 
       (ASet.subset (IAutomaton.get_AO Q) (IAutomaton.get_AO P)))
  (
   negb (SRelSet.mem (srel (st (lbl "err")) (st (lbl "err0"))) 
     (sim_X (IAutomaton.get_init P) (IAutomaton.get_init Q) P Q ASet.empty (TSet.cardinal (IAutomaton.get_trans Q))) )
  ).

Definition SMENI_refinement (P Q:IA): bool :=
  andb (andb (ASet.subset (ASet.diff (IAutomaton.get_AI P) (ASet.add (&"tau") ASet.empty)) (IAutomaton.get_AI Q)) 
             (ASet.subset (IAutomaton.get_AO Q) (IAutomaton.get_AO P)))  
       (negb (SRelSet.mem (srel (st (lbl "err")) (st (lbl "err0"))) 
             (sim_X (IAutomaton.get_init P) (IAutomaton.get_init Q) P Q
                    (ASet.add (&"tau") ASet.empty) (TSet.cardinal (IAutomaton.get_trans Q))) )
  ).

Definition SMENI_refinement_bounded (P Q:IA) (n:nat) : bool :=
  andb (andb (ASet.subset (ASet.diff (IAutomaton.get_AI P) (ASet.add (&"tau") ASet.empty)) (IAutomaton.get_AI Q)) 
             (ASet.subset (IAutomaton.get_AO Q) (IAutomaton.get_AO P)))  
       (negb (SRelSet.mem (srel (st (lbl "err")) (st (lbl "err0"))) 
             (sim_X (IAutomaton.get_init P) (IAutomaton.get_init Q) P Q
                    (ASet.add (&"tau") ASet.empty) n) )
  ).

Definition b_unreachable_by_all_trans (ia ia':IA): bool :=
  let product := IAutomaton.IAProd ia ia' in
  let all_trans := IAutomaton.get_trans product in
  let err_states := (IAutomaton.Illegal ia ia') in
  negb (TSet.b_targets_reachable (TSet.cardinal all_trans) 
                                  err_states (SSet.add (IAutomaton.get_init product) SSet.empty) all_trans).
