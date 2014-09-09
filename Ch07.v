(* begin hide *)
Require Export HoTT Ch06_3.
(* end hide *)
(** printing <~> %\ensuremath{\eqvsym}% **)
(** printing == %\ensuremath{\sim}% **)
(** printing ^-1 %\ensuremath{^{-1}}% **)
(** * Homotopy $n$-types *)

(** %\exer{7.1}{250}% 
(i) Use Theorem 7.2.2 to show that if $\brck{A} \to A$ for every type $A$, then
    every type is a set.
(ii) Show that if every surjective function (purely) splits, i.e.%~%if
    $\prd{b:B}\brck{\hfib{f}{b}} \to \prd{b:B}\hfib{f}{b}$ for every $f : A \to
    B$, then every type is a set.
*) 

(** %\soln%
(i)  Suppose that $f : \prd{A:\UU}\brck{A} \to A$, and let $X$ be some type. To
apply Theorem 7.2.2, we need a reflexive mere relation on $X$ that implies
identity.  Let $R(x, y) \defeq \brck{x = y}$, which is clearly a reflexive mere
relation.  Moreoever, it implies the identity, since for any $x, y : X$ we have
%\[
  f(x = y) : R(x, y) \to (x = y)
\]%
So by Theorem 7.2.2, $X$ is a set.

(ii)  Again, let $X$ be a typeV and $R$ the relation $R(x, y) \defeq \brck{x =
y}$.  Suppose that $p : R(x, y)$.  Then for all $a : A$, there merely exists an
$a' : A$ such that $a' = a$.  But since every surjective function purely
splits, that means that for every $a : A$ there exists some $a' : A$ such that
$a' = a$.  So, in particular, 

*) 

(** %\exer{7.2}{250}% *)
(** %\exer{7.3}{250}% *)
(** %\exer{7.4}{250}% *)
(** %\exer{7.5}{250}% *)
(** %\exer{7.6}{250}% *)
(** %\exer{7.7}{250}% *)
(** %\exer{7.8}{250}% *)
(** %\exer{7.9}{251}% *)
(** %\exer{7.10}{251}% *)
(** %\exer{7.11}{251}% *)

(** %\exerdone{7.12}{251}% 
Show that $X \mapsto (\lnot \lnot X)$ is a modality.
*) 

(** %\soln%
We must show that there are
%\begin{enumerate}
  \item functions $\eta^{\lnot \lnot}_{A} : A \to \lnot\lnot A$ for every type
  $A$,
  \item for every $A : \UU$ and every family $B : \lnot\lnot A \to \UU$, a
  function
  \[
    \ind{\lnot\lnot} : 
    \left(\prd{a : A}\lnot\lnot(B(\eta^{\lnot\lnot}_{A}(a)))\right)
    \to
    \prd{z : \lnot\lnot A}\lnot\lnot(B(z))
  \]
  \item A path $\ind{\lnot\lnot}(f)(\eta^{\lnot\lnot}_{A}(a)) = f(a)$ for each
  $f : \prd{a : A}\lnot\lnot(B(\eta^{\lnot\lnot}_{A}(a)))$, and
  \item For any $z, z' : \lnot \lnot A$, the function $\eta^{\lnot\lnot}_{z =
  z'} : (z = z') \to \lnot\lnot(z = z')$ is an equivalence.
\end{enumerate}%
Some of this has already been done.  The functions $\eta^{\lnot\lnot}_{A}$ were
given in Exercise 1.12; recall:
%\[
  \eta^{\lnot\lnot}_{A} \defeq \lam{a}{f}f(a)
\]%
Now suppose that we have an element $f$ of the antecedent of
$\ind{\lnot\lnot}$, and let $z : \lnot\lnot A$.  Suppose furthermore
that $g : \lnot B(z)$; we derive a contradiction.  It suffices to
construct an element of $\lnot A$, for then we can apply $z$ to obtain
an element of $\emptyt$.  So suppose that $a : A$.  Then 
%\[
  f(a) : \lnot \lnot B(\eta^{\lnot\lnot}_{A}(a))
\]%
but $\lnot X$ is a mere proposition for any type $X$, so $z =
\eta^{\lnot\lnot}_{A}(a)$, and transporting gives an element of $\lnot \lnot
B(z)$.  Applying this to $g$ gives a contradiction.

For (iii), suppose that $a : A$ and $f : \prd{a :
A}\lnot\lnot(B(\eta^{\lnot\lnot}_{A}(a)))$.  Then $f(a) : \lnot \lnot
(B(\eta^{\lnot\lnot}_{A}(a)))$, making this type contractible, giving a
canonical path $\ind{\lnot\lnot}(f)(\eta^{\lnot\lnot}_{A}(a)) = f(a)$.

Finally, for (iv), let $z, z' : \lnot\lnot A$.  Since $\lnot\lnot A$ is a mere
proposition, so is $z = z'$.  $\lnot\lnot(z = z')$ is also a mere proposition,
so if there is an arrow $\lnot\lnot(z = z') \to (z = z')$, then it is
automatically a quasi-inverse to $\eta^{\lnot\lnot}_{z = z'}$.  Such an arrow
is immediate from the fact that $\lnot \lnot A$ is a mere proposition.
*)

Definition eta_nn (A : Type) : A -> ~ ~ A := fun a f => f a.

Lemma hprop_arrow (A B : Type) : IsHProp B -> IsHProp (A -> B).
Proof.
  intro HB.
  apply hprop_allpath. intros f g. apply path_forall. intro a. apply HB.
Defined.

Lemma hprop_neg {A : Type} : IsHProp (~ A).
Proof.
  apply hprop_arrow. apply hprop_Empty.
Defined.
  

Definition ind_nn (A : Type) (B : ~ ~ A -> Type) : 
  (forall a : A, ~ ~ (B (eta_nn A a))) -> forall z : ~ ~ A, ~ ~ (B z). 
Proof.
  intros f z. intro g.
  apply z. intro a.
  apply ((transport (fun x => ~ ~ (B x)) 
                    (@allpath_hprop _ hprop_neg _ _)
                    (f a)) g).
Defined.

Definition nn_modality_iii (A : Type) (B : ~ ~ A -> Type)
  (a : A) (f : forall a, ~ ~ (B (eta_nn A a))) :
    ind_nn A B f (eta_nn A a) = f a.
Proof.
  apply allpath_hprop.
Defined.

Lemma isequiv_hprop (P Q : Type) (HP : IsHProp P) (HQ : IsHProp Q)
      (f : P -> Q) :
  (Q -> P) -> IsEquiv f.
Proof.
  intro g.
  refine (isequiv_adjointify f g _ _).
  intro q. apply allpath_hprop.
  intro p. apply allpath_hprop.
Defined.

Lemma hprop_hprop_path (A : Type) (HA : IsHProp A) (x y : A) : IsHProp (x = y).
Proof.
  apply hprop_allpath.
  apply set_path2.
Defined.

Definition nn_modality_iv (A : Type) (z z' : ~ ~ A) : IsEquiv (eta_nn (z = z')).
Proof.
  apply isequiv_hprop.
  apply hprop_hprop_path. apply hprop_neg. apply hprop_neg.
  intro f. apply hprop_neg.
Defined.
  

(** %\exer{7.13}{251}% *)
(** %\exer{7.14}{251}% *)
(** %\exer{7.15}{251}% *)
