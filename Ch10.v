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

Lemma hprop_acc {A : hSet} {L : A -> A -> hProp} 
  : forall a, IsHProp (@acc _ L a).
Proof.
  intro a. apply hprop_allpath. intros s1 s2.
  induction s1 as [a1 h1 k1]. 
  induction s2 as [a2 h2 k2]. apply (ap (accL a2)).
  apply path_forall; intro b. apply path_forall; intro l.
  apply k1.
Defined.

Definition well_founded {A : hSet} (L : A -> A -> hProp) := 
  forall a : A, @acc A L a.

Definition WFRel := {A : hSet & {L : A -> A -> hProp & @well_founded A L}}.

Lemma hprop_wf {A : hSet} (L : A -> A -> hProp) : IsHProp (well_founded L).
Proof.
  apply hprop_dependent. apply hprop_acc.
Defined.

Lemma path_wfrel (AL BL : WFRel) (p : AL.1 = BL.1) : 
  (transport _ p AL.2).1 = BL.2.1 -> AL = BL.
Proof.
  intro q. apply path_sigma_uncurried. exists p.
  apply (@path_sigma_hprop _ _ (hprop_wf) _).
  apply q.
Defined.

Lemma path_wfrel_uncurried (AL BL : WFRel) :
  {p : AL.1 = BL.1 & (transport _ p AL.2).1 = BL.2.1} -> AL = BL.
Proof.
  intro H. destruct H as [p q]. apply (path_wfrel _ _ p q).
Defined.

Definition extensional (AL : WFRel)
  := forall a a', (forall c, (AL.2.1 c a) <-> (AL.2.1 c a')) -> (a = a').

Lemma hprop_extensional (AL : WFRel) : IsHProp (extensional AL).
Proof.
  apply hprop_dependent; intro a.
  apply hprop_dependent; intro b.
  apply hprop_arrow. apply hprop_allpath. apply set_path2.
Defined.

Definition ExtWFRel := {AL : WFRel & extensional AL}.


Definition strict_nat_order : nat -> nat -> hProp
  := fun n m => hp (lt n m) (hprop_lt n m).

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



(** %\exer{10.5}{365}% *)
(** %\exer{10.6}{365}% *)
(** %\exer{10.7}{365}% 
Note that $\bool$ is an ordinal, under the obvious relation $<$ such that
$0_{\bool} < 1_{\bool}$ only.
%\begin{enumerate}
  \item Define a relation $<$ on $\prop$ which makes it into an ordinal.
  \item Show that $\bool =_{\ord} \prop$ if and only if $\LEM{}$ holds.
\end{enumerate}%
*)

(** %\soln%
For $P, Q : \prop$, define $(P < Q) \defeq (P \to Q)$.  We must show that this
$<$ is well-founded, extensional, and transitive.  To show that it's
well-founded, suppose that $Q : \prop$; we show that $P$ is accessible for all
$P < Q$.
*)


(** %\exer{10.8}{365}% *)
(** %\exer{10.9}{365}% *)
(** %\exer{10.10}{365}% *)
(** %\exer{10.11}{365}% *)
(** %\exer{10.12}{366}% *)
(** %\exer{10.13}{366}% *)
