Require Export Int63 List PArray.
Require Export State SMT_terms Trace.
Export Atom Form Sat_Checker Cnf_Checker Euf_Checker.
Require Import Bool.
Local Open Scope int63_scope.
Require Import Arith.EqNat.
Require Import PArith.
Require Import BinPos BinInt.
Require Import Omega.
Require Import ZArith.
Open Scope Z_scope.

Declare ML Module "smtcoq_plugin".


(*******************transformation d'un but qui n'est pas en forme***********************)
Ltac fold_rec1 a b c :=
  repeat match goal with
         | |- context [ a (b ?X) ] => change (a (b X)) with (c X)
         end.

Ltac fold_rec a b c d :=
  repeat match goal with
         | |- context [ a (b (c ?X)) ] => change (a (b (c X))) with (d X)
         end.

Lemma new_var_P : forall A : Prop, (positive-> A) -> A.
  intros A H.
  apply H.
  exact xH.
Qed.

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


Lemma PostoZid:forall (z:Z),  Zpos(ZtoPos z) = z.
 (* 0 < x -> Z.pos (Z.to_pos x) = x*)
Proof.
   destruct z. admit.
   intros; admit.
   admit.
Qed.

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
Ltac isVar t :=
  match isPcst t with
  |true => constr :false
  | _ => constr :true
end. 
 Lemma inj_add_Z : forall n n' : Z, ZtoPos(n + n') = (ZtoPos n + ZtoPos n')%positive.
 Admitted.
Lemma inj_sub_Z : forall n n' : Z, ZtoPos(n - n') = (ZtoPos n - ZtoPos n')%positive.
  Admitted.
Lemma inj_mul_Z : forall n n' : Z, ZtoPos(n * n') = (ZtoPos n * ZtoPos n')%positive.
  Admitted.
Lemma change_eqbP_Z a b:
    (Z.eqb a b) = Pos.eqb (ZtoPos a) (ZtoPos b). 
  Admitted.
Lemma is_pos p : 0 < Zpos p.
Proof.
easy.
Qed.
Lemma pos_is_nonneg p : 0 <= Zpos p.
Proof.
easy.
Qed.
(*************méthode 1************
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


Tactic Notation "if" tactic(t) "then" tactic(t1) "else" tactic(t2) :=
  first [ t; first [ t1 | fail 2 ] | t2 ].

(********************************pos -> Z*************************)
Ltac PostoZ2 :=
(* on crée un nom frais *)
  let var := fresh "var" in
(* on crée artificiellement une prémisse de type N à notre théorème*)
  apply new_var_P;
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
              (* Idem: si le contexte contient xI ou xH, c'est qu'on est à l'intérieur d'une constante *)
              | context [xO var] => idtac "3"; idtac n; idtac t; fail 1
              | context [xI var] => idtac "4"; idtac n; idtac t; fail 1
                (* Sinon on réécrit *)
              | _ => rewrite <- (ZtoPosid n); idtac "5"; idtac n; idtac t
                     (* let u := context C[n] in *)
                     (* let v := context C[ZtoPos (Zpos n)] in *)
                     (* replace u with v  by (rewrite (ZtoPosid n); reflexivity); idtac "5"; idtac n; idtac t *)
              end
          end
      end
  end;
(* On efface notre variable fraîche *)
  clear var;
 repeat match goal with
         | |- context [ xO (ZtoPos (Zpos ?t)) ] => change (xO (ZtoPos (Zpos t))) with (xO t)
         | |- context [ xI (ZtoPos (Zpos ?t)) ] => change (xI (ZtoPos (Zpos t))) with (xI t)
         end.

Goal (2 = 1)%positive.
  (* replace (eq (xO xH) xH) with (eq (xO xH) (ZtoPos (Zpos xH))) by now rewrite !ZtoPosid. *)
  (* Focus 2. *)
  (* rewrite !ZtoPosid. *)
  PostoZ2.
Abort.
  
Ltac Pos_to_Z_en_form1 :=
  match goal with
         |  [ |-forall _:positive , _ ] => intro
         | [ |- forall _ : _ -> _, _] => intro
         | [ |- forall _ : Z, _] => intro
         | [ |- forall _ : bool, _] => intro
         | [ |- forall _ : Type, _] => intro
         |  |-context [Pos.add (ZtoPos ?X) (ZtoPos ?Y) ] =>  change (Pos.add (ZtoPos X) (ZtoPos Y)) with (ZtoPos ( X + Y))
         |  |-context [Pos.sub  (ZtoPos ?X) (ZtoPos ?Y) ] =>  change (Pos.sub (ZtoPos X) (ZtoPos Y)) with (ZtoPos ( X - Y))
         |  |-context [Pos.mul (ZtoPos ?X) (ZtoPos ?Y) ] =>  change (Pos.mul (ZtoPos X) (ZtoPos Y)) with (ZtoPos ( X * Y))
         |  |-context [Pos.ltb (ZtoPos ?X) (ZtoPos ?Y) ] =>  change (Pos.ltb (ZtoPos X) (ZtoPos Y)) with (ZtoPos (Z.ltb( X  Y)))
         |  |-context [Pos.eqb (ZtoPos ?X) (ZtoPos ?Y) ] =>    replace (Pos.eqb (ZtoPos X) (ZtoPos Y)) with (Z.eqb X Y); [ | apply change_eqbP_Z];rewrite Zeq_bool_Zeqb
      
    end.

 (*Lemma1 : forall p : positive, Z.gtb (Zpos p) 0 = true *)
  (*Lemma1 x1 : Z.gtb x0 0 = true*)
(*goal = true ---> implb (Z.gtb x0 0) goal = true*)


 Ltac Pos_to_Z_en_form2 :=
   match goal with 
  |  |-context [Zpos ?X] => if is_var X then (hide_Pos_var X) else fail
  (* |  |-context [Zpos ?X] => if isPcst X then (hide_Pos_cst (Zpos X)) else fail *)
  |  |-context [?X (ZtoPos?Y)] => let f := fresh X in pose (f := fun y => X (ZtoPos y)); fold_rec1 X ZtoPos f
  |  |-context [Zpos (?X ?Y)] => let f := fresh X in pose (f := fun y => Zpos (X y));  fold_rec1 Zpos X f
   end.

 (*Ltac Pos_to_Z_en_form3 :=
   match goal with
       | [ H := (Zpos ?T) : Z |- _ ] =>let h = fresh h in  assert (h :  (Z.gtb  (T) 0 )=true      )by auto;refine(_ h)
  *)


 Ltac ZtoPos_tac :=intros; PostoZ2 ; repeat Pos_to_Z_en_form1;  repeat Pos_to_Z_en_form2; repeat rewrite PostoZid.