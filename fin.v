Require Import Eqdep List Omega.

Set Implicit Arguments.

Inductive fin : nat -> Type :=
| FO : forall n, fin (S n)
| FS : forall n, fin n -> fin (S n).

Implicit Arguments FO [n].

Definition cardLe (T : Type) (n : nat) :=
  exists ls, length ls = n
             /\ forall x : T, In x ls.

Fixpoint buildAll (n : nat) : list (fin n) :=
  match n return list (fin n) with
    | O => nil
    | S n' => FO :: map ( @FS _) (buildAll n')
  end.

Hint Rewrite map_length : fin.

Ltac t' := try subst; simpl in *; intuition.
:xa

Lemma in_map_inv : forall A B (f : A -> B) x ls,
                     In x (map f ls)
                     -> exists y, x = f y /\ In y ls.
  induction ls; t'; firstorder; eauto.
Qed.

Implicit Arguments in_map_inv [A B f x ls].

Lemma FS_inv : forall n (f1 f2 : fin n),
                 FS f1 = FS f2
                 -> f1 = f2.
  injection 1; intro Heq; apply (inj_pair2 _ _ _ _ _ Heq).
Qed.

Ltac t := t'; repeat progress (autorewrite with fin in *;
                                repeat match goal with
                                         | [ |- context[if ?E then _ else _] ] => destruct E
                                         | [ _ : context[if ?E then _ else _] |- _ ] => destruct E
                                         | [ H : In _ (map _ _) |- _ ] => destruct (in_map_inv H); clear H
                                                                                                 | [ H : FS _ = FS _ |- _ ] => generalize (FS_inv H);
                                         clear H
                                       end;
                               t'); eauto.

Lemma buildAll_length : forall n, length (buildAll n) = n.
  induction n; t.
Qed.

Hint Rewrite buildAll_length : fin.

Hint Resolve in_map.

Lemma buildAll_full : forall n f, In f (buildAll n).
  induction f; t.
Qed.

Hint Resolve buildAll_length buildAll_full.
Hint Unfold cardLe.

Theorem fin_cardLe : forall n, cardLe (fin n) n.
  eauto.
Qed.

Definition fin_dest : forall n (f : fin (S n)),
                        { f' : _ | f = FS f'} + { f = FO }.
  exact (fun n f =>
           match f in fin n' return match n' return fin n' -> Set with
                                      | O => fun _ => unit
                                      | S n => fun f => { f' : _ | f = FS f'} + 
                                                        { f = FO }
                                    end f with
             | FO _ => inright _ (refl_equal _)
             | FS _ f' => inleft _ (exist _ f' (refl_equal _))
           end).
Qed.

Hint Extern 1 False => discriminate.
Hint Extern 1 (_ <> _) => discriminate.

Lemma FS_eq' : forall n (f1 f2 : fin n),
                 (f1 = f2 -> False)
                 -> FS f1 = FS f2 -> False.
  t.
Qed.

Hint Resolve FS_eq'.

Lemma FS_eq : forall n (f1 f2 : fin n),
                {f1 = f2} + {f1 <> f2}
                -> {FS f1 = FS f2} + {FS f1 <> FS f2}.
  intuition; subst; intuition eauto.
Qed.

Hint Resolve FS_eq.

Definition fin_eq : forall n (f1 f2 : fin n), {f1 = f2} + {f1 <> f2}.
  induction f1; intro f2; destruct (fin_dest f2) as [[? ?] | ?]; subst; 
  auto.
Qed.

Fixpoint remove n (f : fin n) (fs : list (fin n)) {struct fs} : list 
                                                                  (fin n) :=
  match fs with
    | nil => nil
    | f' :: fs => if fin_eq f' f then remove f fs
                  else f' :: remove f fs
  end.

Fixpoint diff n (fs1 fs2 : list (fin n)) {struct fs2} : list (fin n) :=
  match fs2 with
    | nil => fs1
    | f :: fs2 => remove f (diff fs1 fs2)
  end.

Fixpoint dupFree n (fs : list (fin n)) {struct fs} : Prop :=
  match fs with
    | nil => True
    | f :: fs => ~In f fs /\ dupFree fs
  end.

Lemma buildAll_dupFree' : forall n (fs : list (fin n)),
                            dupFree fs
                            -> dupFree (map ( @FS _) fs).
  induction fs; t.
Qed.

Hint Resolve buildAll_dupFree'.

Theorem buildAll_dupFree : forall n, dupFree (buildAll n).
  induction n; t.
Qed.

Hint Resolve buildAll_dupFree.

Lemma remove_not_there : forall n (f : fin n) fs,
                           (In f fs -> False)
                           -> length (remove f fs) = length fs.
  induction fs; t.
Qed.

Hint Rewrite remove_not_there using assumption : fin.

Lemma remove_length : forall n (f : fin n) fs,
                        dupFree fs
                        -> length (remove f fs) >= pred (length fs).
  induction fs; t.
Qed.

Hint Resolve remove_length.

Lemma In_remove : forall n (f f' : fin n) fs,
                    In f (remove f' fs)
                    -> In f fs.
  induction fs; t.
Qed.

Hint Resolve In_remove.

Lemma remove_dupFree : forall n (f : fin n) fs,
                         dupFree fs
                         -> dupFree (remove f fs).
  induction fs; t.
Qed.

Hint Resolve remove_dupFree.

Lemma diff_dupFree : forall n (fs1 fs2 : list (fin n)),
                       dupFree fs1
                       -> dupFree (diff fs1 fs2).
  induction fs2; t.
Qed.

Hint Resolve diff_dupFree.

Lemma pred_S : forall n m1 m2,
                 n >= pred (m1 - m2)
                 -> n >= m1 - S m2.
  t.
Qed.

Hint Resolve pred_S.

Theorem diff_length : forall n (fs1 fs2 : list (fin n)),
                        dupFree fs1
                        -> length (diff fs1 fs2) >= length fs1 - length fs2.
  induction fs2; t;
  match goal with
    | [ |- context[remove ?f (diff ?fs1 ?fs2)] ] =>
      elim (remove_length f (diff fs1 fs2)); t
  end.
Qed.

Hint Resolve diff_length.

Lemma length_pos : forall A (ls : list A) n,
                     length ls >= n
                     -> n > 0
                     -> exists x, In x ls.
  destruct ls; t; elimtype False; omega.
Qed.

Implicit Arguments length_pos [A ls n].

Lemma In_remove' : forall n (f : fin n) fs,
                     In f (remove f fs)
                     -> False.
  induction fs; t.
Qed.

Hint Resolve In_remove'.

Lemma In_diff : forall n (f : fin n) fs1 fs2,
                  In f (diff fs1 fs2)
                  -> In f fs2
                  -> False.
  induction fs2; t.
Qed.

Hint Resolve In_diff.

Theorem fin_cardGt : forall n m, m > n -> ~cardLe (fin m) n.
  unfold cardLe, not; firstorder;
  match goal with
    | [ ls : list (fin _) |- _ ] =>
      assert (Hge : length (diff (buildAll m) ls)
                    >= length (buildAll m) - length ls); auto;
      match goal with
        | [ H : _ = _ |- _ ] => rewrite H in Hge
      end;
      t;
      destruct (length_pos Hge); t
  end.
  Grab Existential Variables.
  
Qed.

Hint Extern 1 (_ > _) => omega.

Theorem fin_inj : forall n m, fin n = fin m -> n = m.
  intros; destruct (eq_nat_dec n m); t; destruct (le_lt_dec n m); t; 
  elimtype False;
  match goal with
    | [ n : nat, m : nat, H : fin _ = fin _ |- _ ] =>
      solve [ generalize (fin_cardLe n);
              generalize ( <at> fin_cardGt n m); 
              rewrite H; t ]
  end.
Qed.
