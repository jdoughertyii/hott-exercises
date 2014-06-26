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

Section Exercise2_prd.

Variable A B : Type.

Definition recprod (C : Type) (g : A -> B -> C) (p : A * B) :=
    g (fst p) (snd p).

Goal recprod A (fun a => fun b => a) = fst. trivial. Qed.
Goal recprod B (fun a => fun b => b) = snd. trivial. Qed.

End Exercise2_prd.

Section Exercise2_sm.

Variable A : Type.
Variable B : A -> Type.

Definition recsm (C : Type) (g : forall (x : A), B x -> C) (p : exists (x : A), B x) :=
    g (projT1 p) (projT2 p).

