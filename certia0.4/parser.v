(* parser.v

   This code is a part of CertIA.

   this simple parser of IA takes the principle of ImpParser.v
   in the book "Software Foundations" by B.C.Pierce

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
*)

Require Import Ascii.
Require Import String.
Require Import Arith.
Require Import List.

(*Require Export state.
Require Export action.
Reuire Export transition.*)
Require Export IA.
Require Export lib.

(*Open Scope nat_scope.*)
Open Scope list_scope.

Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (beq_nat n 32) (* space *)
           (beq_nat n 9)) (* tab *)
      (orb (beq_nat n 10) (* linefeed *)
           (beq_nat n 13)). (* Carriage return. *)

Notation "x '<=?' y" := (ble_nat x y) (at level 70, no associativity) : nat_scope.

Definition isAlphaOrDigit (c:ascii):bool :=
  let n := nat_of_ascii c in orb (beq_nat n 95) (orb (andb (48 <=? n) (n <=? 57)) 
                        (orb (andb (65 <=? n) (n <=? 90)) (andb (97 <=? n) (n <=? 122)))).

Inductive chartype := white | alpha_digit | other.

Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then 
    white
  else if isAlphaOrDigit c then
    alpha_digit
  else
    other.

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)    (at level 60, right associativity).

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c::(list_of_string s)
  end.

Fixpoint string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Definition token := string.

(* acc:目前已经接受的当前字符串中的字符; xs:待扫描的字符串字符; cls:下一字符类型 *)
Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii) : list (list ascii) :=
  let tk := match acc with [] => [] | _::_ => [rev acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    | _, _, "("      => tk ++ ["("]::(tokenize_helper other [] xs') 
    | _, _, ")"      => tk ++ [")"]::(tokenize_helper other [] xs')
    | _, _, "["      => tk ++ ["["]::(tokenize_helper other [] xs') 
    | _, _, "]"      => tk ++ ["]"]::(tokenize_helper other [] xs')
    | _, white, _    => tk ++ (tokenize_helper white [] xs')
    | alpha_digit,alpha_digit,x  => tokenize_helper alpha_digit (x::acc) xs'
    | other,other,x  => tokenize_helper other (x::acc) xs'
    | _,tp,x         => tk ++ (tokenize_helper tp [x] xs')
    end
  end %char.

Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [] (list_of_string s)).

(*Eval compute in tokenize "constr_ia [s0,s1] (s0) [fail,ok] [msg] [ ] [s0->(msg)s1,s1->(ok)s0]".*)

(*forallb: find whether a boolean function (isLowerAlpha) 
  is satisfied by all the elements of a list.*)
Fixpoint build_symtable (xs : list token) (n : nat) : (token -> nat) :=
  match xs with
  | [] => (fun s => n)
  | x::xs' =>
    if (forallb isAlphaOrDigit (list_of_string x))
     then (fun s => if string_dec s x then n else (build_symtable xs' (S n) s))
     else build_symtable xs' n
  end.

(* An option with error messages. *)
Inductive optionE (X:Type) : Type :=
  | SomeE : X -> optionE X
  | NoneE : string -> optionE X.

Implicit Arguments SomeE [[X]].
Implicit Arguments NoneE [[X]].

Notation "'DO' ( x , y ) <== e1 ;; e2" :=
  (match e1 with
  | SomeE (x,y) => e2
  | NoneE err => NoneE err
  end) (right associativity, at level 60).

Notation "'DO' ( x , y ) <-- e1 ;; e2 'OR' e3" := 
  (match e1 with
  | SomeE (x,y) => e2
  | NoneE err => e3
  end) (right associativity, at level 60, e2 at next level). 

Open Scope string_scope.

Definition parser (T : Type) := 
  list token -> optionE (T * list token). 

Fixpoint many_helper {T} (p : parser T) acc steps xs :=
match steps, p xs with
| 0, _ => NoneE "Too many recursive calls"
| _, NoneE _ => SomeE ((rev acc), xs)
| S steps', SomeE (t, xs') => many_helper p (t::acc) steps' xs'
end.

(* A (step-indexed) parser which expects zero or more ps *)
Fixpoint many {T} (p : parser T) (steps : nat) : parser (list T) :=
  many_helper p [] steps.

(* A parser which expects a given token, followed by p.
when the head of the third param of firstExpect equals to t,
use the second param (a parser) to process the tail of the third param *)
Definition firstExpect {T} (t : token) (p : parser T) : parser T :=
  fun xs => match xs with
            | x::xs' => if string_dec x t then p xs' 
                          else NoneE ("expected '" ++ t ++ "'.")
            | [] =>  NoneE ("expected '" ++ t ++ "'.")
            end. 

(* A parser which expects a particular token *)
Definition expect (t : token) : parser unit :=
  firstExpect t (fun xs => SomeE(tt, xs)).

(*the parse for an IA*)

Fixpoint parseAtomicState (symtable :string->nat) (xs : list token) : optionE (St * list token) :=
  match xs with
  | [] => NoneE "Expected State"
  | x::xs' => 
    if forallb isAlphaOrDigit (list_of_string x) then
      SomeE (st (lbl x), xs')
    else
      NoneE ("Illegal State:'" ++ x ++ "'")
end.

Fixpoint parseStateSq (steps:nat) (symtable : string->nat) (xs : list token) :=
  match steps with
  | O => NoneE "Too many recursive calls"
  | S steps' =>
    match xs with
    | [] => SomeE ([],xs)
    | x::xs' => if string_dec x "]" then SomeE ([],xs')
      else
        DO (e, rest) <== parseAtomicState symtable xs ;;
        DO (es, rest') <== many (firstExpect "," (parseAtomicState symtable)) steps' rest;;
        SomeE (cons e es, rest')
    end
  end.

(*Eval compute in let ss:=tokenize "" in (parseStateSq 20 (build_symtable ss 0) (ss)).
Eval compute in let ss:=tokenize "s0,s1" in (parseStateSq 20 (build_symtable ss 0) (ss)).*)

Fixpoint parseAtomicAct (symtable :string->nat) (xs : list token) : optionE (Act * list token) :=
  match xs with
  | [] => NoneE "Expected Act"
  | x::xs' => 
    if forallb isAlphaOrDigit (list_of_string x) then
      SomeE (act (lbl x), xs')
    else
      NoneE ("Illegal Act:'" ++ x ++ "'")
end.

Fixpoint parseActSq (steps:nat) (symtable : string->nat) (xs : list token) :=
  match steps with
  | O => NoneE "Too many recursive calls"
  | S steps' =>
    match xs with
    | [] => SomeE ([],xs)
    | x::xs' => if string_dec x "]" then SomeE ([],xs)
      else 
        DO (e, rest) <== parseAtomicAct symtable xs ;;
        DO (es, rest') <== many (firstExpect "," (parseAtomicAct symtable)) steps' rest;;
        SomeE (cons e es, rest')
    end
  end.

(*Eval compute in let ss:=tokenize "fail,ok" in (parseActSq 20 (build_symtable ss 0) (ss)).
Eval compute in let ss:=tokenize "" in (parseActSq 20 (build_symtable ss 0) (ss)).*)

Fixpoint parseAtomicTrans (symtable: string->nat) (xs: list token): 
       optionE (Trans * list token) :=
    DO (frm, rest0) <== parseAtomicState symtable xs;;
    DO (u, rest1) <== expect "->" rest0;;
    DO (ac, rest2) <== firstExpect "(" (parseAtomicAct symtable) rest1;;
    DO (u, rest3) <== expect ")" rest2;;
    DO (to, rest4) <== parseAtomicState symtable rest3;;
    SomeE (trans frm ac to, rest4).

(*Eval compute in let ss:=tokenize "s1->(msg)s2" in (parseAtomicTrans (build_symtable ss 0) (ss)).*)

Fixpoint parseTransSq (steps:nat) (symtable : string->nat) (xs : list token) :=
  match steps with
  | O => NoneE "Too many recursive calls"
  | S steps' =>
    match xs with
    | [] => SomeE ([],xs)
    | x::xs' => if string_dec x "]" then SomeE ([],xs)
      else DO (e, rest) <== parseAtomicTrans symtable xs ;;
      DO (es, rest') <== many (firstExpect "," (parseAtomicTrans symtable)) steps' rest;;
      SomeE (cons e es, rest')
    end
  end.

(*Eval compute in let ss:=tokenize "s0->(msg)s1,s1->(ok)s0" in (parseTransSq 20 (build_symtable ss 0) (ss)).
Eval compute in let ss:=tokenize "" in (parseTransSq 20 (build_symtable ss 0) (ss)).*)

Fixpoint parseIA (steps:nat) (symtable:string->nat) (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' => 
    DO (u, rest0) <== expect "IA" xs;;
    DO (sts, rest1) <== firstExpect "[" (parseStateSq steps' symtable) rest0;;
    DO (u, rest2) <== expect "]" rest1;;
    DO (init, rest3) <== firstExpect "(" (parseAtomicState symtable) rest2;;
    DO (u, rest4) <== expect ")" rest3;;
    DO (act_in, rest5) <== firstExpect "[" (parseActSq steps' symtable) rest4;;
    DO (u, rest6) <== expect "]" rest5;;
    DO (act_out, rest7) <== firstExpect "[" (parseActSq steps' symtable) rest6;;
    DO (u, rest8) <== expect "]" rest7;;
    DO (act_h, rest9) <== firstExpect "[" (parseActSq steps' symtable) rest8;;
    DO (u, rest10) <== expect "]" rest9;;
    DO (trans, rest11) <== firstExpect "[" (parseTransSq steps' symtable) rest10;;
    DO (u, rest12) <== expect "]" rest11;;
    SomeE(constr_ia (SSet.GenSts sts) init 
     (ASet.GenActs act_in) (ASet.GenActs act_out) (ASet.GenActs act_h)
     (TSet.GenTrs trans), rest12)
  end.

Definition parse (str : string) : IA :=
  let tokens := tokenize str in
  match (parseIA 300 (build_symtable tokens 0) tokens) with
  | SomeE (ia, _) => ia
  | NoneE _ => (constr_ia (SSet.GenSts [$"s0"]) ($"s0")
                          ASet.empty ASet.empty ASet.empty TSet.empty)
  end.
