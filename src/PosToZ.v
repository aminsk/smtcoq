Require Import ZArith.
  (*transformer positve en Z :zify de pos vers z*)
    Ltac Pos2Z :=
     repeat
       match goal with
        |H:context[Plt ?X ?Y] |- _ => change(Plt X Y) with (Zlt(Zpos X)(Zpos Y)) in H
        | H:context[Ple ?X ?Y] |- _ => change(Ple X Y) with (Zle(Zpos X)(Zpos Y) )in H
        | |- context[Plt ?X ?Y] => change (Plt X Y) with (Zlt (Zpos X) (Zpos Y))
        | |- context[Ple ?X ?Y] => change (Ple X Y) with (Zle (Zpos X) (Zpos Y))
        | |- context[Pcompare ?X ?Y Eq = Lt] => change (Pcompare X Y Eq = Lt) with (Zlt (Zpos X) (Zpos Y))
        | |- context[Pcompare ?X ?Y Eq = Gt] => change (Pcompare X Y Eq = Gt) with (Zgt (Zpos X) (Zpos Y))
        | |- context[Pcompare ?X ?Y Eq = Eq] => rewrite (Pcompare_eq_iff X Y)
        | |- context[Zpos (Psucc ?X)] => rewrite (Zpos_succ_morphism X)
      | H : context[Zpos (Psucc ?X)] |- _ => rewrite (Zpos_succ_morphism X) in H
      (* inversion of equalities between positive *)
      | H : (?X~0)%positive = (?Y~0)%positive |- _ => inversion H;try subst;try clear H
      | H : (?X~1)%positive = (?Y~1)%positive |- _ =>  inversion H;try subst;try clear H
      | H : (?X~0)%positive = (?Y~1)%positive |- _ => discriminate  H
      | H : (?X~1)%positive = (?Y~0)%positive |- _ => discriminate  H
      | H : xH = (?Y~0)%positive |- _ => discriminate  H
      | H : xH = (?Y~1)%positive |- _ => discriminate  H
      | H : (?Y~0)%positive = xH |- _ => discriminate  H
      | H : (?Y~1)%positive = xH |- _ => discriminate  H
      (* inversion of pairs *)
      | H :  (?X1,?Y1) = (?X2,?Y2)  |- _ => inversion H;try subst;try clear H
      (* inversion of existT *)
    end ; auto with zarith.

                                                                 