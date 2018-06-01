Require Import ZArith PArith.
(*transformer positve en Z :zify de pos vers z*)

Ltac Pos2Z :=
     repeat
       match goal with
        |[ |-forall _:positive , _ ] => change positive with Z
        |H:context[Plt ?X ?Y] |- _ => change(Plt X Y) with (Zlt(Zpos X)(Zpos Y)) in H
        | H:context[Ple ?X ?Y] |- _ => change(Ple X Y) with (Zle(Zpos X)(Zpos Y) )in H
        |H:context[Plt ?X ?Y] |- _ => change(Plt X Y) with (Zlt(Zpos X)(Zpos Y)) in H
        |H:context[Pgt ?X ?Y] |- _ => change(Pgt X Y) with (Zgt(Zpos X)(Zpos Y)) in H
        |H:context[Peqb ?X ?Y] |- _ => change(Peqb X Y) with (Z.eqb(Zpos X)(Zpos Y)) in H

        | |- context[Pos.ltb ?X ?Y] => replace (Pos.ltb X Y) with (Z.ltb (Zpos X) (Zpos Y))
        | |- context[Ple ?X ?Y] => change (Ple X Y) with (Zle (Zpos X) (Zpos Y))
        | |- context[Pgt ?X ?Y] => change (Pgt X Y) with (Zgt(Zpos X) (Zpos Y))
        | |- context[Peqb ?X ?Y] => change(Peqb X Y) with (Z.eqb(Zpos X) (Zpos Y)) 

        | |- context[Pcompare ?X ?Y Eq = Lt] => change (Pcompare X Y Eq = Lt) with (Zlt (Zpos X) (Zpos Y))
  
        | |- context[Pcompare ?X ?Y Eq = Gt] => change (Pcompare X Y Eq = Gt) with (Zgt (Zpos X) (Zpos Y))
        | |- context[Pcompare ?X ?Y Eq = Eq] => rewrite (Pcompare_eq_iff X Y)
         | |- context[Pos.add ?X ?Y] => change(Pos.add X Y) with (Z.add(Zpos X) (Zpos Y))
  end.

Unset Printing Notations.
Goal forall( x y :positive) ( f :positive -> bool),
    (negb(Pos.ltb(Pos.add x 1) (Pos.add x 2)) )=true.

Proof.
  intros.
  Pos2Z.
  rewrite Z.ltb_irrefl.
  reflexivity.
  Qed.