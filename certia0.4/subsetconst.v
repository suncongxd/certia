(* subsetconst.v

   Copyright (C) 2017, Cong Sun

   This is an implementation of the subset construction algorithm
   to convert a NFA to a DFA. It is used in our reasearch paper
   when the replacement of action \tau may introduce nondeterministic
   transitions in the result. This implementation is not quite efficient
   yet and need further improvement.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
*)

Require Export IA.
Require Export NewStates.

Definition subset_construction (a:IA) : IA :=
  let init:= IAutomaton.get_init a in
  let states:=IAutomaton.get_states a in
  let trs:= NewSSet.subset_const 
    (NewSSet.add init NewSSet.empty) 
    (NewSSet.add init NewSSet.empty)
    (IAutomaton.get_actions a) 
    (NewSSet.power_states ( NewSSet.convertSSet2NewSSet states) )
    (TSet.elements (IAutomaton.get_trans a)) (SSet.cardinal states) in
  constr_ia (TSet.getStatesByTrans trs) (init) 
  (IAutomaton.get_AI a) (IAutomaton.get_AO a) (IAutomaton.get_AH a) trs.


