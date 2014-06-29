Require Import HoTT.

Section Exercise1.

  Definition compose {A B C:Type} (g : B -> C) (f : A -> B) :=
      fun x => g (f x).

  Theorem compose_assoc : forall (A B C D : Type) (f : A -> B) (g : B-> C) (h : C -> D),
      compose h (compose g f) = compose (compose h g) f.
  Proof.
    trivial.
  Qed.
End Exercise1.

Section Exercise2a.
  Context {A B : Type}.

  Definition recprod (C : Type) (g : A -> B -> C) (p : A * B) :=
      g (fst p) (snd p).

  Goal forall C g a b, recprod C g (a, b) = g a b. trivial. Qed.

End Exercise2a.

Section Exercise2b.
  Context {A : Type}.
  Context {B : A -> Type}.

  Definition recsm (C : Type) (g : forall (x : A), B x -> C) (p : exists (x : A), B x) :=
      g (projT1 p) (projT2 p).

  Goal forall C g a b, recsm C g (a; b) = g a b. trivial. Qed.

End Exercise2b.

Section Exercise3a.
  Context {A B : Type}.

  Definition uppt (x : A * B) : (fst x, snd x) = x.
    destruct x; reflexivity.
  Defined.

  Definition indprd (C : A * B -> Type) (g : forall (x:A) (y:B), C (x, y)) (z : A * B) :=
        (uppt z) # (g (fst z) (snd z)).

  Goal forall C g a b, indprd C g (a, b) = g a b. trivial. Qed.

End Exercise3a.

Section Exercise3b.
  Context {A : Type}.
  Context {B : A -> Type}.

  Definition upst (p : {x:A & B x}) : (projT1 p; projT2 p) = p.
    destruct p; reflexivity.
  Defined.

  Definition indsm (C : {x:A & B x} -> Type) (g : forall (a:A) (b:B a), C (a; b)) 
                   (p : {x:A & B x}) :=
       (upst p) # (g (projT1 p) (projT2 p)).

  Goal forall C g a b, indsm C g (a; b) = g a b. trivial. Qed.

End Exercise3b.
