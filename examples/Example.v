
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
 orb( orb a  b ) c  && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) =false .
Proof.
  zchaff.
Qed.


(* Examples of the verit tactic (requires verit in your PATH environment
   variable):
   - with booleans
   - in logics QF_UF and QF_LIA *)

  
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





(****************Tactic pour transformer N to nat******************************)
Fixpoint nat_of_pos p:=
  match p with
  |xO p => (nat_of_pos p)* 2
  |xI p => (nat_of_pos p)*2+1
  |xH => 1
  end.

  Lemma change_eqb a b:
    (beq_nat a b) = N.eqb (N.of_nat a) (N.of_nat b). 
  Admitted.
  Lemma changeN0:
    O%nat = N.to_nat 0.
    Admitted.

Lemma positive_nat_Z p :Z.of_nat (Pos.to_nat p) =Zpos p.
Proof.
  destruct (Pos2Nat.is_succ p) as (n ,H).
  rewrite H. simpl. f_equal. now apply SuccNat2Pos.inv.
Qed.


 
Ltac fold_rec1 a b c :=
  repeat match goal with
         | |- context [ a (b ?X) ] => change (a (b X)) with (c X)
         end.

Ltac fold_rec a b c d :=
  repeat match goal with
         | |- context [ a (b (c ?X)) ] => change (a (b (c X))) with (d X)
         end.

(*******************transformation d'un but qui n'est pas en forme***********************)
(*************méthode 1*************
Ltac mem x acc :=
  match acc with
  | nil => constr:(false)
  | cons x _ => constr:(true)
  |cons _ ?l => mem x l
   end.
Ltac find_N  acc :=
  match goal with
  | |-context [(?n)] =>
    match type of n with
    |N =>
      match mem n acc with
      |true => fail
      |false => find_N(n::acc)
      end
    |_ => fail
    end
  | _=> acc
  end.
Ltac rev l acc :=
  match l with
  |nil => acc
  |?x::?xs => rev xs (x::acc)
  end.

Ltac Ntonat_rewrite acc :=
  match acc with
  |nil => idtac
  |cons ?x ?l =>try rewrite <- (Nnat.N2Nat.id x); Ntonat_rewrite l
  end.

Ltac Ntonat :=
  let acc := find_N (@nil N) in
  let l :=rev acc (@nil N) in
  idtac acc;
  Ntonat_rewrite l.

 *)


 (*********************2ème méthode******************)
  
Lemma new_var : forall A : Prop, (N -> A) -> A.
  intros A H.
  apply H.
  exact N0.
Qed.

Ltac Ntonat2 :=
(* on crée un nom frais *)
  let var := fresh "var" in
(* on crée artificiellement une prémisse de type N à notre théorème*)
  apply new_var;
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
        | N =>
          match n with
(* Si jamais il commence par of_nat to_nat on abandonne le match, ce
qui est fait avec le "1" du fail *)
            | N.of_nat (N.to_nat _) => idtac "1"; idtac n; fail 1
            | _ =>
(* On construit notre but dans lequel on a remplacé n par notre
variable fraîche *)
              let t := context C[var] in
              match context C[var] with
(* Si ce but contient le terme N.of_nat (N.to_nat var) cela signifie
que le contexte C[] est de la forme C'[N.of_nat (N.to_nat [])] et donc
on abandonne le match *)
                | context [N.of_nat (N.to_nat var)] => idtac "2"; idtac n; idtac t; fail 1
(* Sinon on réécrit *)
                | _ => rewrite <- (Nnat.N2Nat.id n); idtac "3"; idtac n; idtac t
              end
          end
      end
  end;
(* On efface notre variable fraîche *)
  clear var.




  (*******************un but qui est en forme**************************)
Tactic Notation "if" tactic(t) "then" tactic(t1) "else" tactic(t2) :=
  first [ t; first [ t1 | fail 2 ] | t2 ].

Ltac hide_N_var X:= is_var X;let z := fresh X in pose (z:=N.to_nat X) ;fold z.
Ltac is_N_cst t :=
  match t with
  | N0 => idtac
  | Npos ?p => is_N_cst p
  | xI ?p => is_N_cst p
  | xO ?p => is_N_cst p
  | xH => idtac
  | _ => fail
  end.
   Ltac hide_N_cst x := let red := eval cbv in x in change x with red.

 Ltac N_to_nat_en_form1 :=
   match goal with
           | [ |-forall _:positive , _ ] => intro
         | [ |- forall _ : _ -> _, _] => intro
         | [ |- forall _ : Z, _] => intro
         | [ |- forall _ : bool, _] => intro
         | [ |- forall _ : Type, _] => intro
         |  |-context [N.add (N.of_nat ?X) (N.of_nat ?Y) ] =>           
          replace (N.add (N.of_nat X) (N.of_nat Y)) with (N.of_nat (plus X Y));
            [ |apply Nnat.Nat2N.inj_add ]
         | |-context[N.sub (N.of_nat ?X)(N.of_nat ?Y) ] => replace (N.sub (N.of_nat X )(N.of_nat Y)) with (N.of_nat (minus X Y));[ |apply Nnat.Nat2N.inj_sub]
         | |-context[N.mul (N.of_nat ?X)(N.of_nat ?Y) ] => replace (N.mul(N.of_nat X )(N.of_nat Y)) with (N.of_nat (mul X Y));[ |apply Nnat.Nat2N.inj_mul]
         |  |-context [N.eqb (N.of_nat ?X) (N.of_nat ?Y) ] =>
          replace (N.eqb (N.of_nat X) (N.of_nat Y)) with (beq_nat X Y);
          [ | apply change_eqb]
           
         end.
Print Nnat.Nat2N.inj_add.
Ltac N_to_nat_en_form2 :=
  match goal with
  |  |-context [N.to_nat ?X] => if is_var X then (hide_N_var X) else fail
  |  |-context [N.to_nat ?X] => if is_N_cst X then (hide_N_cst (N.to_nat X)) else fail
  |  |-context [?X (N.of_nat ?Y)] => let f := fresh X in pose (f := fun y => X (N.of_nat y)); fold_rec1 X N.of_nat f
  |  |-context [N.to_nat (?X ?Y)] => let f := fresh X in pose (f := fun y => N.to_nat (X y));  fold_rec1 N.to_nat X f
(*  |  |-context [N.to_nat (?X (N.of_nat ?Y))] => let f := fresh X in pose (f := fun y => N.to_nat (X (N.of_nat y)));  fold_rec N.to_nat X N.of_nat f*)
  end.
         

(*Ltac FromNtonat := Ntonat2 ; repeat  N_to_nat_en_form1;  repeat N_to_nat_en_form2; repeat rewrite Nnat.Nat2N.id.
Goal forall (x y :N )(f :N ->N),N.eqb (f(x+1)%N) (f(1+x)%N).
  Proof.
    intros.
    Ntonat2.
Ntonat2.

Goal   forall (x y:N)(f :N -> N),
N.eqb (f x)  (f (y + 1)%N).
Proof.
  intros.
  FromNtonat.*)


  (*********************transoformations buts avec pos en Z*************************)
  
  Definition ZtoPos (z : Z) : positive :=
  match z with
  | Zpos p => p
  | _      => 1%positive
  end.

Lemma ZtoPosid : forall (p : positive),
  ZtoPos (Zpos p) = p.
Proof.
  intros p.
  reflexivity.
Qed.


Lemma PostoZid:forall (z:Z),
    Zpos(ZtoPos z) = z.
Admitted.

Lemma Zeq_bool_Zeqb a b : Z.eqb a b = Zeq_bool a b.
Proof.
  case_eq (a =? b).
  - rewrite Z.eqb_eq. intros ->. symmetry. now rewrite <- Zeq_is_eq_bool.
  - rewrite Z.eqb_neq. intro H. case_eq (Zeq_bool a b); auto. now rewrite <- Zeq_is_eq_bool.
Qed.




Ltac hide_Pos_var X:= is_var X;let z := fresh X in pose (z:=Zpos X) ;fold z.
 Ltac hide_Pos_cst x := let red := eval cbv in x in change x with red.

   
Ltac isPcst t :=
  match t with
  | xI ?p => isPcst p
  | xO ?p => isPcst p
  | xH => constr:true
  | _ => constr:false
  end.


Ltac PostoZ2 :=
(* on crée un nom frais *)
  let var := fresh "var" in
(* on crée artificiellement une prémisse de type N à notre théorème*)
  apply new_var;
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
        | positive =>
          match n with
(* Si jamais il commence par of_nat to_nat on abandonne le match, ce
qui est fait avec le "1" du fail *)
            | ZtoPos(Zpos _) => idtac "1"; idtac n; fail 1
            | _ =>
(* On construit notre but dans lequel on a remplacé n par notre
variable fraîche *)
              let t := context C[var] in
              match context C[var] with
(* Si ce but contient le terme N.of_nat (N.to_nat var) cela signifie
que le contexte C[] est de la forme C'[N.of_nat (N.to_nat [])] et donc
on abandonne le match *)
                | context [ZtoPos (Zpos var)] => idtac "2"; idtac n; idtac t; fail 1
(* Sinon on réécrit *)
                | _ => rewrite <- (ZtoPosid n); idtac "3"; idtac n; idtac t
              end
          end
      end
  end;
(* On efface notre variable fraîche *)
  clear var.
Lemma inj_add_Z : forall n n' : Z, ZtoPos(n + n') = (ZtoPos n + ZtoPos n')%positive.
 Admitted.
Lemma inj_sub_Z : forall n n' : Z, ZtoPos(n - n') = (ZtoPos n - ZtoPos n')%positive.
  Admitted.
Lemma inj_mul_Z : forall n n' : Z, ZtoPos(n * n') = (ZtoPos n * ZtoPos n')%positive.
  Admitted.
Lemma change_eqbZ a b:
    (Z.eqb a b) = Pos.eqb (ZtoPos a) (ZtoPos b). 
  Admitted.

Lemma pos_is_nonneg p : 0 <= Zpos p.
  Admitted.
Ltac Pos_to_Z_en_form1 :=
  match goal with
         |[ |-forall _:positive , _ ] => intro
         | [ |- forall _ : _ -> _, _] => intro
         | [ |- forall _ : Z, _] => intro
         | [ |- forall _ : bool, _] => intro
         | [ |- forall _ : Type, _] => intro
                                               
         
         |  |-context [Pos.add (ZtoPos ?X) (ZtoPos ?Y) ] =>  replace (Pos.add (ZtoPos X) (ZtoPos Y)) with (ZtoPos ( X + Y));  [ |apply inj_add_Z ]
         |  |-context [Pos.sub  (ZtoPos ?X) (ZtoPos ?Y) ] =>  change (Pos.sub (ZtoPos X) (ZtoPos Y)) with (ZtoPos ( X - Y)); pose proof (pos_is_nonneg (sub X Y)); [ |apply inj_sub_Z ]
         |  |-context [Pos.mul (ZtoPos ?X) (ZtoPos ?Y) ] =>  change (Pos.mul (ZtoPos X) (ZtoPos Y)) with (ZtoPos ( X * Y)); pose proof (pos_is_nonneg (mul X Y)); [ |apply inj_mul_Z ]
                                                                                                            |  |-context [Pos.ltb (ZtoPos ?X) (ZtoPos ?Y) ] =>  change (Pos.ltb (ZtoPos X) (ZtoPos Y)) with (ZtoPos (Z.ltb( X  Y)))

   
         |  |-context [Pos.eqb (ZtoPos ?X) (ZtoPos ?Y) ] =>    replace (Pos.eqb (ZtoPos X) (ZtoPos Y)) with (Z.eqb X Y); [ | apply change_eqbZ];rewrite Zeq_bool_Zeqb
      
           
 end.   


 Ltac Pos_to_Z_en_form2 :=
  match goal with
  |  |-context [Zpos ?X] => if is_var X then (hide_Pos_var X) else fail
  |  |-context [Zpos ?X] => if isPcst X then (hide_Pos_cst (Zpos X)) else fail
  |  |-context [?X (ZtoPos?Y)] => let f := fresh X in pose (f := fun y => X (ZtoPos y)); fold_rec1 X ZtoPos f
  |  |-context [Zpos (?X ?Y)] => let f := fresh X in pose (f := fun y => Zpos (X y));  fold_rec1 Zpos X f

  end.

Ltac FromPostoZ := PostoZ2 ; repeat Pos_to_Z_en_form1;  repeat Pos_to_Z_en_form2; repeat rewrite PostoZid.
             
Goal forall (x y :positive )(f :positive-> Z),Zeq_bool (f(x+1)%positive) (f(1+x)%positive).
Proof.
  intros.
  FromPostoZ.
  verit. 
Qed.






(*****************transformation des entiers nat to Z*****************)

SearchAbout nat.
Ltac hide_nat_var X:= is_var X;let z := fresh X in pose (z:=  X) ;fold z.
Ltac hide_nat_cst x := let red := eval cbv in x in change x with red.

   



Ltac NattoZ2 :=
(* on crée un nom frais *)
  let var := fresh "var" in
(* on crée artificiellement une prémisse de type N à notre théorème*)
  apply new_var;
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
            | Z.of_nat(Zpos _) => idtac "1"; idtac n; fail 1
            | _ =>
(* On construit notre but dans lequel on a remplacé n par notre
variable fraîche *)
              let t := context C[var] in
              match context C[var] with
(* Si ce but contient le terme N.of_nat (N.to_nat var) cela signifie
que le contexte C[] est de la forme C'[N.of_nat (N.to_nat [])] et donc
on abandonne le match *)
                | context [ZtoPos (Zpos var)] => idtac "2"; idtac n; idtac t; fail 1
(* Sinon on réécrit *)
                | _ => rewrite <- (ZtoPosid n); idtac "3"; idtac n; idtac t
              end
          end
      end
  end;
(* On efface notre variable fraîche *)
  clear var.
Lemma inj_add_Z : forall n n' : Z, ZtoPos(n + n') = (ZtoPos n + ZtoPos n')%positive.
 Admitted.
Lemma inj_sub_Z : forall n n' : Z, ZtoPos(n - n') = (ZtoPos n - ZtoPos n')%positive.
  Admitted.
Lemma inj_mul_Z : forall n n' : Z, ZtoPos(n * n') = (ZtoPos n * ZtoPos n')%positive.
  Admitted.
Lemma change_eqbZ a b:
    (Z.eqb a b) = Pos.eqb (ZtoPos a) (ZtoPos b). 
  Admitted.

Lemma pos_is_nonneg p : 0 <= Zpos p.
  Admitted.
Ltac Pos_to_Z_en_form1 :=
  match goal with
         |[ |-forall _:positive , _ ] => intro
         | [ |- forall _ : _ -> _, _] => intro
         | [ |- forall _ : Z, _] => intro
         | [ |- forall _ : bool, _] => intro
         | [ |- forall _ : Type, _] => intro
                                               
         
         |  |-context [nat.add (ZtoPos ?X) (ZtoPos ?Y) ] =>  replace (Pos.add (ZtoPos X) (ZtoPos Y)) with (ZtoPos ( X + Y));  [ |apply inj_add_Z ]
         |  |-context [Pos.sub  (ZtoPos ?X) (ZtoPos ?Y) ] =>  change (Pos.sub (ZtoPos X) (ZtoPos Y)) with (ZtoPos ( X - Y)); pose proof (pos_is_nonneg (sub X Y)); [ |apply inj_sub_Z ]
         |  |-context [Pos.mul (ZtoPos ?X) (ZtoPos ?Y) ] =>  change (Pos.mul (ZtoPos X) (ZtoPos Y)) with (ZtoPos ( X * Y)); pose proof (pos_is_nonneg (mul X Y)); [ |apply inj_mul_Z ]
                                                                                                            |  |-context [Pos.ltb (ZtoPos ?X) (ZtoPos ?Y) ] =>  change (Pos.ltb (ZtoPos X) (ZtoPos Y)) with (ZtoPos (Z.ltb( X  Y)))

   
         |  |-context [Pos.eqb (ZtoPos ?X) (ZtoPos ?Y) ] =>    replace (Pos.eqb (ZtoPos X) (ZtoPos Y)) with (Z.eqb X Y); [ | apply change_eqbZ];rewrite Zeq_bool_Zeqb
      
           
 end.   


 Ltac Pos_to_Z_en_form2 :=
  match goal with
  |  |-context [Zpos ?X] => if is_var X then (hide_Pos_var X) else fail
  |  |-context [Zpos ?X] => if isPcst X then (hide_Pos_cst (Zpos X)) else fail
  |  |-context [?X (ZtoPos?Y)] => let f := fresh X in pose (f := fun y => X (ZtoPos y)); fold_rec1 X ZtoPos f
  |  |-context [Zpos (?X ?Y)] => let f := fresh X in pose (f := fun y => Zpos (X y));  fold_rec1 Zpos X f

  end.

Ltac FromPostoZ := PostoZ2 ; repeat Pos_to_Z_en_form1;  repeat Pos_to_Z_en_form2; repeat rewrite PostoZid.