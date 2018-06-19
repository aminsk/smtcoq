
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



(*zify ça marche pas avec  autres types que Z?????????*)
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


Goal forall a b c, ((a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)) = false.
Proof.
  verit.
Qed.

Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
  (negb (Zeq_bool (f a) b)) || (negb (P (f a))) || (P b).
Proof.  
  verit.
Qed.

Goal forall (x y :Z) ( f :Z -> bool)  ,
    (negb(Z.gtb x x ))  .
  Proof.
   verit.
Qed.
  (*buts avec la transformation de positive vers Z*)

  Goal forall (x :positive) (a b : Z) (P : Z -> bool) (f : Z -> Z),
  (negb (Zeq_bool (f a) b)) || (negb (P (f a))) || (P b)  &&  (negb(Pos.ltb x x) ).
          Proof.
    repeat match goal with
         |[ |-forall _:positive , _ ] => intro
         | [ |- forall _ : _ -> _, _] => intro
         | [ |- forall _ : Z, _] => intro
         | [ |- forall _ : bool, _] => intro
         | [ |- forall _ : Type, _] => intro
       
      | [ |- context[ Pos.ltb ?X ?Y ]] => change (Pos.ltb X Y) with (Z.ltb (Zpos X) (Zpos Y))
      |_ => easy;idtac
         end.
    pose (n :=Zpos x).
   fold n.
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


Lemma Zeq_bool_Zeqb a b : Z.eqb a b = Zeq_bool a b.
Proof.
  case_eq (a =? b).
  - rewrite Z.eqb_eq. intros ->. symmetry. now rewrite <- Zeq_is_eq_bool.
  - rewrite Z.eqb_neq. intro H. case_eq (Zeq_bool a b); auto. now rewrite <- Zeq_is_eq_bool.
Qed.

 Goal forall (x y :Z) (P:Z -> bool) (f:Z -> Z),

     Zeq_bool (f(x+1)%Z) (f(1+x)%Z) -> Zeq_bool (y+1)%Z  (1 + y)%Z.
  Proof.
    verit.
Qed.



Lemma  inj_add x y :Zpos(x+y) =(Zpos x +Zpos y)%Z. 
Proof.
  admit.
Qed.
 


Goal forall  x y :positive  ,
    (Pos.eqb(Pos.add y 2) (Pos.add 2 y)) && true.
  Proof.
  repeat
    match goal with
         | [ |-forall _:positive , _ ] => intro
         | [ |- forall _ : _ -> _, _] => intro
         | [ |- forall _ : Z, _] => intro
         | [ |- forall _ : bool, _] => intro
         | [ |- forall _ : Type, _] => intro
         | [ |- context[ Pos.eqb ?X ?Y ]  ]=>change (Pos.eqb X Y) with (Z.eqb (Zpos X) (Zpos Y));rewrite Zeq_bool_Zeqb
         | [ |- context [Pos.add ?X ?Y ] ] => change (Pos.add X Y) with (Z.add (Zpos X) (Zpos Y))  
         | |-context [Zpos (?A +?B)] =>rewrite Zpos_plus_distr
         | |-context [Zpos ?X] =>let n := fresh n in pose (n:=Zpos X);fold n 
    end.
  verit.
  Qed.

 

  (*********le cas des symboles non reconnus***********)
  
(*cas 1 :Z ->positive *)
  (*le cas de (f x ) il marche juste en remplaçant f x par fresh varible*)
  Definition rew_pos f (g : Type -> positive) :=forall (u :_), Zpos (g u) = f u.
 Print Z.
 Goal forall(g:Z -> positive) (x:Z)(y:positive),
implb (Pos.eqb (g(x+2)%Z) (g(2+x)%Z)) (Zeq_bool (x+2)%Z (2+x)%Z )&&(Pos.ltb(Pos.add y 2) (Pos.add 3 y))  &&true.
Proof.
  repeat
    match goal with
         |[ |-forall _:positive , _ ] => intro
         | [ |- forall _ : _ -> _, _] => intro
         | [ |- forall _ : Z, _] => intro
         | [ |- forall _ : bool, _] => intro
         | [ |- forall _ : Type, _] => intro
         | [ |- context[ Pos.eqb ?X ?Y ]  ]=>change (Pos.eqb X Y) with (Z.eqb (Zpos X) (Zpos Y));rewrite Zeq_bool_Zeqb
         | [ |- context [Pos.add ?X ?Y ] ] => change (Pos.add X Y) with (Z.add (Zpos X) (Zpos Y))
        
         | [ |-context [Zpos (?X ?Y)] ] =>let f := fresh f in pose (f:= fun u => Zpos (X u));
                                                           assert (G : forall u, Zpos (g u) = f u);
                                                           unfold f; auto;
  repeat rewrite G
        | [ |- context[ Pos.ltb ?X ?Y ]  ]=> change (Pos.ltb X Y) with (Z.ltb (Zpos X) (Zpos Y))
        | [ |-context [Zpos (?A +?B)] ] => rewrite Zpos_plus_distr
        | [ |-context [Zpos (Psucc ?X)] ]=> rewrite (Zpos_succ_morphism X)
        (********ne marche pas dans le cas des nombres****)
        (*| [ |-context [Zpos ?X] ] => let n := fresh n in pose (n:=Zpos X);fold n
           *)                                 
    end.
pose (n :=Zpos y) ; fold n.
  verit.
Qed.




(*cas 2 : positive -> Z *) (*cas 3:positive -> positive*)
Lemma positive_nat_Z p :Z.of_nat (Pos.to_nat p) =Zpos p.
Proof.
  destruct (Pos2Nat.is_succ p) as (n ,H).
  rewrite H. simpl. f_equal. now apply SuccNat2Pos.inv.
Qed.

(*Lemma inj_add n m : 0<=n -> 0<=m -> Z.to_nat(n+m)%nat =(Z.to_nat n +Z.to_nat m)%nat.*)
Goal forall (x y :positive )(f :positive -> positive),Pos.eqb (f(x+2)%positive) (f(x+2)%positive).
Proof.
  repeat match goal with
         |[ |-forall _:positive , _ ] => intro
         | [ |- forall _ : _ -> _, _] => intro
         | [ |- forall _ : Z, _] => intro
         | [ |- forall _ : bool, _] => intro
         | [ |- forall _ : Type, _] => intro
      (*   | [ |-context [(?X ?Y)] ]  =>  match Y with
                                     |Pos.add ?A ?B => change( Pos.add A B) with (Z.add(Z.to_nat (Z.of_nat(Pos.to_nat A))) (Z.to_nat (Z.of_nat (Pos.to_nat B))) ) ; rewrite inj_add 
                                     | _ => idtac                                                          *)                              end;change (?X ?Y) with (Z.to_nat(Z.of_nat (X Y)))
                                                                                          
         | [ |- context[ Pos.eqb ?X ?Y ]  ]=>change (Pos.eqb X Y) with (Z.eqb (Zpos X) (Zpos Y));rewrite Zeq_bool_Zeqb
         | [ |- context [Pos.add ?X ?Y ] ] => change (Pos.add X Y) with (Z.add (Zpos X) (Zpos Y))                                                      
                                                                                                            | [ |-context [Zpos (?X ?Y)] ] =>let f := fresh f in pose (f:= fun u => Zpos (X u));
                                                           assert (G : forall u, Zpos (g u) = f u);
                                                           unfold f; auto;
                                                             repeat rewrite G
         | [ |- context[ Pos.ltb ?X ?Y ]  ]=> change (Pos.ltb X Y) with (Z.ltb (Zpos X) (Zpos Y))
         | [ |-context [Zpos (?A +?B)] ] => rewrite Zpos_plus_distr                                                            
         | [ |-context [Zpos ?X] ] =>let n := fresh n in pose (n:=Zpos X);fold n                                                                   
    end.
verit.        
Qed.


                       





(*transformation des nat vers Z
Goal forall x y:nat , (ltb x%nat y%nat) =true .
Proof.
  intros.
  match goal with
  | [ |- context[N.ltb ?X ?Y]] => change  (N.ltb X Y)  with(Z.ltb (Zpos (Pos.of_nat X )) (Zpos (Pos.of_nat Y)))
  | _ => easy;idtac
              end.

  Admitted.
    *)