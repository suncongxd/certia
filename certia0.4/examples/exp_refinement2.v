Require Import IA.
Require Import parser.

Definition Prod:IA := parse
"IA [s0,s1,s2,s3,s4,s5] (s0) [name,ISBN,incdn,inus]
[cdnprice,usprice,author] []
[s0->(name)s1, s0->(ISBN)s1, s1->(inus)s2, s1->(incdn)s3,
s2->(usprice)s4, s3->(cdnprice)s4, s4->(author)s5]".

Definition Pay:IA := parse
"IA [s0,s1,s2,s3] (s0) [creditno,usprice,cdnprice]
[refno,errno] []
[s0->(cdnprice)s1, s1->(creditno)s2,
s2->(refno)s3, s2->(errno)s3]".

Definition GenPay:IA := parse
"IA [s0,s1,s2,s3] (s0) [creditno,usprice,cdnprice]
[refno,errno] []
[s0->(usprice)s1, s0->(cdnprice)s1, s1->(creditno)s2,
s2->(errno)s3, s2->(refno)s3]".

Definition c1: IA := IAutomaton.composition Prod GenPay.
Definition c2: IA := IAutomaton.composition Prod Pay.

Eval compute in :> c1.
Eval compute in :> c2.

Eval compute in IAutomaton.bRefine c2 c1.