
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






Ltac reduce x := let red := eval cbv in x in change x with red.


(*******************Nat vers Z****************)
Ltac fold_func a b c :=
  repeat match goal with
         | |- context [ a (b ?X) ] => change (a (b X)) with (c X)
         end.

Lemma Zeq_bool_Zeqb a b : Z.eqb a b = Zeq_bool a b.
Proof.
  case_eq (a =? b).
  - rewrite Z.eqb_eq. intros ->. symmetry. now rewrite <- Zeq_is_eq_bool.
  - rewrite Z.eqb_neq. intro H. case_eq (Zeq_bool a b); auto. now rewrite <- Zeq_is_eq_bool.
Qed.

Tactic Notation "if" tactic(t) "then" tactic(t1) "else" tactic(t2) :=
  first [ t; first [ t1 | fail 2 ] | t2 ].

Ltac hide_Nat_var X:= let z := fresh X in pose (z:= Z.of_nat X) ;fold z.

Lemma inj_0 : Z.of_nat 0 = 0.
Proof.
 reflexivity.
Qed.

(** [Z.of_N] produce non-negative integers *)

Lemma is_nonneg_nat n : 0 <= Z.of_nat n.
Proof.
 now induction n.
Qed.

(*Lemma id_NattoZ n : Z.to_nat (Z.of_nat n) = n.
Proof.
 now rewrite <- nat_N_Z, <- Z_N_nat, N2Z.id, Nat2N.id.
Qed.
 *)

Ltac isNatcst t :=
  match t with
    O  => idtac
  | S ?n => isNatcst n
  | _ => fail
  end.

Definition new_var_Nat : forall A : Prop, (nat -> A) -> A := fun A f => f O.

Ltac NattoZEnForm1 :=
(* on crée un nom frais *)
  let var := fresh "var" in
(* on crée artificiellement une prémisse de type nat à notre théorème*)
  apply new_var_Nat;
(* On l'introduit en lui donnant notre nom frais *)
  intro var;
(* On arrive au coeur de la tactique *)
repeat  
(* Si on a un sous-terme n dans le but *)
  match goal with
(* On capture le contexte, i.e. le but est C[n] *)
    | |- context C[?n]  =>
(* Si n est de type N *)
      match type of n with
        | nat  =>
          match n with
(* Si jamais il commence par of_nat to_nat on abandonne le match, ce
qui est fait avec le "1" du fail *)
            | Z.to_nat(Z.of_nat _) => idtac "1"; idtac n; fail 1
(* Si jamais il commence par plus ou mult on abandonne le match, ce
qui est fait avec le "1" du fail *)
            | plus _ _ => idtac "1"; idtac n; fail 1
            | mult _ _ => idtac "1"; idtac n; fail 1
            | _ =>
(* On construit notre but dans lequel on a remplacé n par notre
variable fraîche *)
              let t := context C[var] in
              match context C[var] with
(* Si ce but contient le terme N.of_nat (N.to_nat var) cela signifie
que le contexte C[] est de la forme C'[N.of_nat (N.to_nat [])] et donc
on abandonne le match *)
                | context [Z.to_nat (Z.of_nat var)] => idtac "2"; idtac n; idtac t; fail 1
(* Si ce but contient le terme S var cela signifie
que le contexte C[] est de la forme C'[S []] et donc
on abandonne le match *)
                | context [S var] => idtac "3"; idtac n; idtac t; fail 1
(* Sinon on réécrit *)
                | _ => rewrite <- (Nat2Z.id n); idtac "4"; idtac n; idtac t
              end
          end
      end
  end;
(* On efface notre variable fraîche*) 
clear var;
repeat match goal with
           | |- context [ S (Z.to_nat (Z.of_nat ?t))] =>change (S(Z.to_nat (Z.of_nat t))) with (S  t)
  end.

Ltac check_pos x :=
  match x with
  | Z.of_nat ?X => apply Nat2Z.is_nonneg
  | Z.add ?X ?Y => apply Z.add_nonneg_nonneg; [ check_pos X | check_pos Y ]
  | Z.mul ?X ?Y => apply Z.mul_nonneg_nonneg; [ check_pos X | check_pos Y ]
  end.

Ltac NattoZEnForm2 :=
  match goal with
         |  |-context [plus (Z.to_nat ?X) (Z.to_nat ?Y) ] =>  rewrite <- (Z2Nat.inj_add X Y); [ | check_pos X | check_pos Y ]
         |  |-context [mult (Z.to_nat ?X) (Z.to_nat ?Y) ] =>  rewrite <- (Z2Nat.inj_mul X Y); [ | check_pos X | check_pos Y ]
         |  |-context [ltb (Z.to_nat ?X) (Z.to_nat ?Y) ] =>  change (ltb (Z.to_nat X) (Z.to_nat Y)) with (Z.to_nat (Z.ltb( X  Y)))
         |  |-context [beq_nat (Z.to_nat ?X) (Z.to_nat ?Y) ] => rewrite <- (change_eqbNat_Z X Y); [ rewrite Zeq_bool_Zeqb | check_pos X | check_pos Y ]
  end.
 
Ltac NattoZEnForm3 :=
  match goal with
  |  |-context [Z.of_nat ?X] => if is_var X then (hide_Nat_var X) else fail
  |  |-context [Z.of_nat ?X] => if isNatcst X then (reduce (Z.of_nat X)) else fail
  |  |-context [?X (Z.to_nat ?Y)] => let f := fresh X in pose (f := fun y => X (Z.to_nat y)); fold_func X Z.to_nat f
  |  |-context [Z.of_nat (?X ?Y)] => let f := fresh X in pose (f := fun y => Z.of_nat (X y));  fold_func Z.of_nat X f
  end.

Ltac NattoZ_tac := intros ; NattoZEnForm1 ; repeat NattoZEnForm2; repeat NattoZEnForm3.


Goal forall (a b : nat) (P : nat -> bool) (f : nat -> nat), 
    (negb (beq_nat (f a) b)) || (negb (P (f a))) || (P b). 
Proof. 
  NattoZ_tac. 
  verit.
Qed.

(*?????????il fait pas les transformations des nombres *)
Goal forall b1 b2 x1 x2,
  implb
  (ifb b1
    (ifb b2 (Zeq_bool (2*x1+1) (2*x2+1)) (Zeq_bool (2*x1+1) (2*x2)))
    (ifb b2 (Zeq_bool (2*x1) (2*x2+1)) (Zeq_bool (2*x1) (2*x2))))
  ((implb b1 b2) && (implb b2 b1) && (Zeq_bool x1 x2)).
Proof.
  verit.
Qed.

Goal forall b1 b2 x1 x2,
  implb
  (ifb b1
    (ifb b2 (beq_nat (2*x1+1) (2*x2+1)) (beq_nat (2*x1+1) (2*x2)))
    (ifb b2 (beq_nat (2*x1) (2*x2+1)) (beq_nat (2*x1) (2*x2))))
  ((implb b1 b2) && (implb b2 b1) && (beq_nat x1 x2)).
Proof.
  NattoZ_tac.
  verit.
Qed.