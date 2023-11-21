
Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_i386.
Require Import wcsspn_i386.

Import X86Notations.
(* binary natural number *)
Open Scope N.

(* question regarding parameter types *)
(* check definition correctness *)
(* forall i, i < n /\ m [p +i] != 0 /\ m[p+n] = 0 *)
(* m Ⓓ[ a  ] *)
Definition haslength (m : addr -> N) (p: addr) (n: N) : Prop :=
   forall i, i< n /\  m Ⓓ[ p + i ] <> 0 /\ m Ⓓ[ p + n ]  = 0.

(* question regarding parameter types *)
(* forall n,exists i, haslength m p n ->  i < n -> m[p+i] = c *)
Definition contains (m: addr -> N) (p: addr) (c:N) : Prop :=
    forall n, exists i, haslength m p n -> i < n -> m Ⓓ[p+i] = c.

(* question regarding parameter types *)
(* p1 = s1 src, p2 = s2 dictionary, r returned prefix length s1 *)
Definition post_condition (m: addr -> N) (p1 p2: addr) (r:N): Prop :=
    forall n, haslength m p1 n -> r <= n /\ 
    forall i, i < r -> contains m p2 (m Ⓓ[p1 + i] ) /\
    ( (m Ⓓ[p1 + r] ) = 0 \/ ~contains m p2 (m Ⓓ[p1 + r] )).