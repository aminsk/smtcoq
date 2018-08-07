(* [Require Import SMTCoq.SMTCoq.] loads the SMTCoq library.
   If you are using native-coq instead of Coq 8.6, replace it with:
     Require Import SMTCoq.
 *)






Add Rec LoadPath "/users/vals/bousalem/tools/github.com/aminsk/smtcoq/src" as SMTCoq.


Require Import SMTCoq.SMTCoq.
Require Import Bool.
Local Open Scope int63_scope.
Require Import Arith.EqNat.
Require Import PArith.
Require Import BinPos BinInt.
Require Import Omega.

Require Import ZArith.
Open Scope Z_scope.





Goal forall a b c,
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  zchaff.
Qed.

Goal forall i j k,
  let a := i == j in
  let b := j == k in
  let c := k == i in
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  zchaff.
Qed.

(* Examples of the verit tactic (requires verit in your PATH environment
   variable):
   - with booleans
   - in logics QF_UF and QF_LIA *)

Goal forall a b c, ((a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)) = false.
Proof.
  verit.
Qed.


Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
  (negb (Zeq_bool (f a) b)) || (negb (P (f a))) || (P b).
Proof.
  verit.
Qed.


Goal forall b1 b2 x1 x2,
  implb
  (ifb b1
    (ifb b2 (Zeq_bool (2*x1+1) (2*x2+1)) (Zeq_bool (2*x1+1) (2*x2)))
    (ifb b2 (Zeq_bool (2*x1) (2*x2+1)) (Zeq_bool (2*x1) (2*x2))))
  ((implb b1 b2) && (implb b2 b1) && (Zeq_bool x1 x2)).
Proof.
  verit.
Qed.
Goal forall (a b : nat) (P : nat -> bool) (f : nat -> nat),
  (negb (beq_nat (f a) b)) || (negb (P (f a))) || (P b).
Proof.
 NattoZ_tac. 
 verit.
Qed.


Goal forall (a b : positive) (P : positive -> bool) (f : positive -> positive),
  (negb (Pos.eqb(f a) b)) || (negb (P (f a))) || (P b).
Proof.
  PostoZ_tac.
  verit.
Qed.



Goal forall b1 b2 x1 x2,
  implb
  (ifb b1
    (ifb b2 (Pos.eqb (2*x1+1) (2*x2+1)) (Pos.eqb (2*x1+1) (2*x2)))
    (ifb b2 (Pos.eqb (2*   x1) (2*x2+1)) (Pos.eqb (2*x1) (2*x2))))
  ((implb b1 b2) && (implb b2 b1) && (Pos.eqb x1 x2)).
Proof.
  PostoZ_tac.
  verit.
Qed.



 Goal forall (a b : nat) (P : nat -> bool) (f : nat -> nat),
  (negb (beq_nat (f a) b)) || (negb (P (f a))) || (P b).
Proof.
NattoZ_tac.
  verit.
Qed.

Goal forall (a b : N) (P : N -> bool) (f : N -> N),
  (negb (N.eqb (f a) b)) || (negb (P (f a))) || (P b).
Proof.
NtoNat_tac;NattoZ_tac.
  verit.
Qed.


(*?????????il fait pas les transformations des nombres *)
Goal forall b1 b2 x1 x2,
  implb
  (ifb b1
    (ifb b2 (beq_nat (2*x1+1) (2*x2+1)) (beq_nat (2*x1+1) (2*x2)))
    (ifb b2 (beq_nat (2*x1) (2*x2+1)) (beq_nat (2*x1) (2*x2))))
  ((implb b1 b2) && (implb b2 b1) && (beq_nat x1 x2)).
Proof.
  NattoZ_tac.
  





