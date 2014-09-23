(* begin hide *)
Require Export HoTT Ch09.
(* end hide *)
(** printing <~> %\ensuremath{\eqvsym}% **)
(** printing <~=~> %\ensuremath{\cong}% **)
(** printing == %\ensuremath{\sim}% **)
(** printing ^-1 %\ensuremath{^{-1}}% **)
(** * Set theory *)

(** %\exer{10.1}{364}% *)

(** %\exer{10.2}{364}% 
Show that if every surjection has a section in the category $\uset$, then the
axiom of choice holds.
*)

(** %\exer{10.3}{364}% *)

(** %\exer{10.4}{365}% 
Prove that if $(A, <_{A})$ and $(B, <_{B})$ are well-founded, extensional,
or ordinals, then so is $A + B$, with $<$ defined by
%\begin{alignat*}{3}
  (a < a') &\defeq (a <_{A} a') &\qquad\qquad \text{for $a, a' : A$} \\
  (b < b') &\defeq (b <_{B} b') &\qquad\qquad \text{for $b, b' : B$} \\
  (a < b) &\defeq \unit &\qquad\qquad \text{for $a: A$, $b : B$} \\
  (b < a) &\defeq \emptyt &\qquad\qquad \text{for $a : A$, $b : B$}
\end{alignat*}%
*)

(** %\soln%
Suppose that $(A, <_{A})$ and $(B, <_{B})$ are well-founded.  To show that $(A
B, <)$ is well-founded, we need to show that $\acc(z)$ for all $z : A+B$.
There are two cases: $z \equiv \inl(a)$ and $z \equiv \inl(b)$.  To show that
$\acc(\inl(a))$, consider any $z' : A + B$, which is either of the form $z'
\equiv \inl(a')$ or $z' \equiv \inl(b')$.  If the first, then 
*)

Inductive acc {A : hSet} {L : A -> A -> hProp} : A -> Type :=
  | accL : forall a : A, (forall b : A, (L b a) -> acc b) -> acc a.

Definition set_sum (A B : hSet) := default_HSet (A + B) hset_sum.

Definition sum_order {A B : hSet} (LA : A -> A -> hProp) 
           (LB : B -> B -> hProp) (z z' : set_sum A B)
  : hProp
  := match z with
       | inl a => match z' with
                    | inl a' => LA a a'
                    | inr b' => Unit_hp
                  end
       | inr b => match z' with
                    | inl a' => False_hp
                    | inr b' => LB b b'
                  end
     end.


Definition well_founded {A : hSet} (L : A -> A -> hProp) := 
  forall a : A, @acc A L a.

Theorem wf_sum (A B : hSet) (LA : A -> A -> hProp) (LB : B -> B -> hProp) 
        (HA : well_founded LA) (HB : well_founded LB)
        : well_founded (sum_order LA LB).
Proof.
Admitted.
  

Definition extensional {A : hSet} (LA : A -> A -> hProp) `{well_founded LA}
  := forall a a', (forall c, (LA c a) <-> (LA c a')) -> (a = a').

Theorem ext_sum (A B : hSet) (LA : A -> A -> hProp) (LB : B -> B -> hProp)
        (HA : well_founded LA) (HB : well_founded LB)
        (HApB : well_founded (sum_order LA LB))
        (H'A : @extensional _ LA HA) (H'B : @extensional _ LB HB)
        : @extensional _ (sum_order LA LB) HApB.
Proof.
  intros z z' H.
  destruct z as [a | b], z' as [a' | b']. simpl in *.
  apply (ap inl). apply H'A. intros a''. apply (H (inl a'')).
  admit. admit.
  

  apply (ap inr). apply H'B. intros b''. apply (H (inr b'')).
Defined.

  
  
  


(** %\exer{10.5}{365}% *)
(** %\exer{10.6}{365}% *)
(** %\exer{10.7}{365}% *)
(** %\exer{10.8}{365}% *)
(** %\exer{10.9}{365}% *)
(** %\exer{10.10}{365}% *)
(** %\exer{10.11}{365}% *)
(** %\exer{10.12}{366}% *)
(** %\exer{10.13}{366}% *)
