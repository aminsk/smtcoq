(* [Require Import SMTCoq.SMTCoq.] loads the SMTCoq library.
   If you are using native-coq instead of Coq 8.6, replace it with:
     Require Import SMTCoq.
 *)






Add Rec LoadPath "/users/vals/bousalem/tools/github.com/aminsk/smtcoq/src" as SMTCoq.


Require Import SMTCoq.SMTCoq.
Require Import Bool.
Local Open Scope int63_scope.

(* Examples that check ZChaff certificates *)
(*
Zchaff_Checker "sat.cnf" "sat.log".
Zchaff_Theorem sat "sat.cnf" "sat.log".


Zchaff_Checker "hole4.cnf" "hole4.log".
*)

(* Example that checks a VeriT certificate, for logic QF_UF *)
(*Section Verit.
  Verit_Checker "euf.smt2" "euf.log".
End Verit.
*)
(* Examples of the zchaff tactic (requires zchaff in your PATH
   environment variable):
   - with booleans
   - with concrete terms *)
Goal forall a b c,
    
 eqb (( a || b ||  c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) )false.
Proof.
  zchaff.
Qed.

Goal forall i j k,
  let a := i == j in
  let b := j == k in
  let c := k == i in
 orb( orb a  b ) c  && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  zchaff.
Qed.

(* Examples of the verit tactic (requires verit in your PATH environment
   variable):
   - with booleans
   - in logics QF_UF and QF_LIA *)

Goal forall a b c, ((a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)) = false.
Proof.
  zchaff.
Qed.
 

  
Goal forall a b c,
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)=false .
Proof.
  verit.
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


 


Goal forall a b c, (negb (negb ( ((negb a) || b) && ((negb b) || c) ) || ((negb a) || c))) = false.
Proof.
  verit.
Qed. 



(*zify ça marche pas avce  autres types que Z*)
Goal  forall (x y:Z),
            ( x = (y + 1)%Z)%Z.
Proof.
  intros.
  zify.
  Abort.


Goal   forall (x y:nat)(f :nat -> nat),
    f x = f (y + 1)%nat.
Proof.
intros.
zify.  
Abort.


Goal   forall (x y:nat)(f :nat -> nat),
    x = (y+1)%nat -> f (x+2)%nat = f (y + 3)%nat.
Proof.
intros.
zify.  
Abort.


 (*buts avec la transoformation de positive vers Z*)

Goal  Peqb (4+1)(4+7)=false.
Proof.
 Pos2Z.
Qed.


Goal forall x :positive ,(x+4)%positive =(x-4)%positive.
Proof.
  zify.
  