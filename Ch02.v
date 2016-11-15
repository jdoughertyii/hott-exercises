(* begin hide *)
Require Export Ch01.
Open Scope type_scope.
(* end hide *)
(** printing <~> %\ensuremath{\eqvsym}% **)
(** printing == %\ensuremath{\sim}% **)
(** printing ^-1 %\ensuremath{^{-1}}% **)
(** * Homotopy type theory *)



(** %\exerdone{2.1}{103}%  
Show that the three obvious proofs of Lemma 2.1.2 are pairwise equal.
 *)

(** %\soln%
Lemma 2.1.2 states that for every type $A$ and every $x, y, z : A$, there is a
function
%\[
  (x = y) \to (y = z) \to (x = z)
\]%
written $p \mapsto q \mapsto p \ct q$ such that $\refl{x} \ct \refl{x} =
\refl{x}$ for all $x : A$.  Each proof is an object $\ct_{i}$ of type
%\[
  \ct_{i} : \prd{x,y,z:A} (x=y)\to(y=z)\to(x=z)
\]%
So we need to show that $\ctu = \ctd = \ctt$.

The first proof is induction over $p$.  Consider the family
%\[
  C_{1}(x, y, p) \defeq 
  \prd{z:A} (y=x) (x=z)
\]%
we have
%\[
\lam{z}{q}q :
\left(\prd{z:A} (x=z) \to (x=z)\right)
  \equiv
  C_{1}(x, x, \refl{x})
\]%
So by path induction, there is a function
%\[
  p \ctu q : (x=z)
\]%
such that $\refl{x} \ctu q \equiv q$. 

For the shorter version, we say that by induction it suffices to consider the
case where $y$ is $x$ and $p$ is $\refl{x}$.  Then given some $q : x = z$, we
want to construct an element of $x=z$; but this is just $q$, so induction gives
us a function $p \ctu q : x = z$ such that $\refl{x} \ctu q \defeq q$.
*)

Module Altcats.

Definition cat' {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z.
  induction p. apply q.
Defined.

(** For the second, consider the family
%\[
  C_{2}(y, z, q) \defeq 
  \prd{z:A} (x=y) \to (x=z)
\]%
and element
%\[
  \lam{z}{p}p
  :
  \left(
    \prd{z:A} (x=z)\to (x=z)
  \right)
  \equiv
  C_{2}(z,z,\refl{z})
\]%
Induction gives us a function
%\[
  p \ctd q : (x = z)
\]%
such that
%\[
  p \ctd \refl{z} = \refl{z}
\]% *)
Definition cat'' {A:Type} {x y z : A} (p : x = y) (q : y = z) : x = z.
  induction q. apply p.
Defined.

(** 
Finally, for $\ctt$, we have the construction from the text.  Take the type
families
%\[
  D(x,y,p) \defeq 
  \prd{z:A}(y=z) \to  (x=z)
\]%
and
%\[
  E(x, z, q) \defeq (x = z)
\]%
Since $E(x,x,\refl{x}) \equiv (x=x)$, we have $e(x) \defeq \refl{x} :
E(x,x,\refl{x})$, and induction gives us a function
%\[
  d : \left(\prd{x,z:A}\prd{q:x=z}(x=z)\right) 
  \equiv
  \prd{x:A}D(x, x, \refl{x})
\]%
So path induction again gives us a function
%\[
  f : \prd{x,y,z:A}(x=y) \to(y=z) \to (x=z)
\]%
Which we can write $p \ctt q : (x=z)$.  By the definitional equality of $f$, we
have that $\refl{x} \ct q \equiv d(x)$, and by the definitional equality of
$d$, we have $\refl{x} \ct \refl{x} \equiv \refl{x}$. *)

Definition cat''' {A:Type} {x y z : A} (p : x = y) (q : y = z) : x = z.
  induction p, q. reflexivity.
Defined.

(**
Now, to show that $p \ctu q = p \ctd q = p \ctt q$, which we will do by
induction on $p$ and $q$.  For the first pair, we want to construct for every
$x, y, z : A$, $p : x = y$, and $q : y = z$, an element of $p \ctu q = p \ctd
q$.  By induction on $p$, it suffices to assume that $y$ is $x$ and $p$ is
$\refl{x}$; similarly, by induction on $q$ it suffices to assume that $z$ is
also $x$ and $q$ is $\refl{x}$.  Then by the computation rule for $\ctu$,
$\refl{x} \ctu \refl{x} \equiv \refl{x}$, and by the computation rule for
$\ctd$, $\refl{x} \ctd \refl{x} \equiv \refl{x}$.  Thus we have
%\[
  \refl{\refl{x}} : (\refl{x} \ctu \refl{x} = \refl{x} \ctd \refl{x})
\]%
which provides the necessary data for induction.

Writing this out a bit more fully for practice, we have the family
%\[
  C : \prd{x, y : A} (x = y) \to \UU
\]%
defined by
%\[
  C(x, y, p) \defeq 
  \prd{z:A}\prd{q:y=z}(p \ctu q = p \ctd q)
\]% 
and in order to apply induction, we need an element of
%\[
  \prd{x:A}C(x, x, \refl{x}) 
  \equiv
  \prd{x, z:A}\prd{q:x=z}(\refl{x} \ctu q = \refl{x} \ctd q)
  \equiv
  \prd{x, z:A}\prd{q:x=z}(q = \refl{x} \ctd q)
\]%
Define $D(x, z, q) \defeq (q = \refl{x} \ctd q)$.  Then
%\[
  \refl{\refl{x}} : 
  D(x, x, \refl{x}) 
  \equiv
  (\refl{x} = \refl{x} \ctd \refl{x})
  \equiv
  (\refl{x} = \refl{x})
\]%
So by induction we have a function $f:\prd{x, z: A}\prd{p:x=z}(q = \refl{x}
\ctd q)$ with $f(x, x, \refl{x}) \defeq \refl{\refl{x}}$.  Thus we have the
element required for induction on $p$, and there is a function 
%\[
  f' : \prd{x, y, z:A}\prd{p:x=y}\prd{q:y=z}(p \ctu q = p \ctd q)
\]%
which we wanted to show.  *) 

Theorem cat'_eq_cat'' : forall {A:Type} {x y z : A} (p : x = y) (q : y = z), 
  (cat' p q) = (cat'' p q).
Proof.
  induction p, q. reflexivity.
Defined.

(** For the next pair, we again use induction.  For all $x, y, z : A$,
$p : x = y$, and $q : y = z$, we need to construct an element of $p
\ctd q = p \ctt q$.  By induction on $p$ and $q$, it suffices to consider the
case where $y$ and $z$ are $x$ and $p$ and $q$ are $\refl{x}$.  Then
$(\refl{x} \ctd \refl{x} = \refl{x} \ctt \refl{x}) \equiv (\refl{x} =
\refl{x})$, and $\refl{\refl{x}}$ inhabits this type.
 *)

Theorem cat''_eq_cat''' : forall {A:Type} {x y z : A} (p : x = y) (q : y = z), 
  (cat'' p q) = (cat''' p q).
Proof.
  induction p, q. reflexivity.
Defined.


(** The third proof goes exactly the same. *)

Theorem cat'_eq_cat''' : forall {A:Type} {x y z : A} (p : x = y) (q : y = z), 
  (cat' p q) = (cat''' p q).
Proof.
  induction p, q. reflexivity.
Defined.

(** %\noindent%
Note that all three of these proofs must end with [Defined] instead of [Qed] if
we want to make use of the computational identity (e.g., $p \ctu \refl{x}
\equiv p$)
that they produce, as we will in the next exercise.
 *)


(** %\exerdone{2.2}{103}%  
Show that the three equalities of proofs constructed in the previous
exercise form a commutative triangle.  In other words, if the three
definitions of concatenation are denoted by $(p \ctu q)$, $(p \ctd
q)$, and $(p \ctt q)$, then the concatenated equality
%\[
  (p \ctu q) = (p \ctd q) = (p \ctt q)
\]%
is equal to the equality $(p \ctu q) = (p \ctt q)$.
 *)

(** %\soln%
Let $x, y, z : A$, $p : x = y$, $q : y = z$, and let $r_{12} : (p \ctu q = p
\ctd q)$, $r_{23} : (p \ctd q = p \ctt q)$, and $r_{13} : (p \ctu q = p
\ctt q)$ be the proofs from the last exercise.  We want to show that $r_{12}
\ct r_{23} = r_{13}$, where $\ct = \ct_{3}$ is the concatenation operation from
the book.  By induction on $p$ and $q$, it suffices to consider the case where
$y$ and $z$ are $x$ and $p$ and $q$ are $\refl{x}$.  Then we have $r_{12}
\equiv \refl{\refl{x}}$, $r_{23} \equiv \refl{\refl{x}}$, and
$r_{13} \equiv \refl{\refl{x}}$ by the definitions.  But then the type we're
trying to witness is
%\[
    (\refl{\refl{x}} \ct \refl{\refl{x}} = \refl{\refl{x}})
    \equiv
    (\refl{\refl{x}} = \refl{\refl{x}})
\]%
from the definition of $\ct$, so $\refl{\refl{\refl{x}}}$ is our witness.
*)

Theorem comm_triangle : forall (A:Type) (x y z : A) (p : x = y) (q : y = z),
  (cat'_eq_cat'' p q) @ (cat''_eq_cat''' p q) = (cat'_eq_cat''' p q).
Proof.
  induction p, q. reflexivity.
Qed.


(** %\exerdone{2.3}{103}%  
Give a fourth, different proof of Lemma 2.1.2, and prove that it is equal to
the others.
*)

(** %\soln%
Let $x, y : A$ and $p : x = y$.  Rather than fixing some $q$ and
constructing an element of $x = z$ out of that, we can directly
construct an element of
%\[
  \prd{z:A} (y = z) \to (x = z)
\]%
by induction on $p$.  It suffices to consider the case where $y$ is
$x$ and $p$ is a $\refl{x}$, which then makes it easy to produce such
an element; namely,
%\[
  \lam{z}\idfunc{x=z} : \prd{z:A} (x = z) \to (x = z)
\]%
Induction then gives us a function $p \ctq q : (x = z)$ such that
$\lam{q}(\refl{x} \ctq q) \defeq \idfunc{x=z}$.
*)

Definition cat'''' {A:Type} {x y z : A} (p : x = y) (q : y = z) : x = z.
  generalize q.  generalize z.
  induction p.  trivial.
Defined.

(** To prove that it's equal to the others, we can just show that it's
equal to $\ct$ and then use concatenation.  Again by induction on $p$
and $q$, it suffices to consider the case where $y$ and $z$ are $x$
and $p$ and $q$ are $\refl{x}$.  Then we have
%\[
  \left((\refl{x} \ctt \refl{x}) = (\refl{x} \ctq \refl{x})\right)
  \equiv
  \left(\refl{x} = \idfunc{x=x}(\refl{x})\right)
  \equiv
  \left(\refl{x} = \refl{x}\right)
\]% 
So $\refl{\refl{x}}$ is again our witness.*)

Theorem cat'''_eq_cat'''' : forall {A:Type} {x y z : A} (p : x = y) (q : y = z),
  (cat''' p q) = (cat'''' p q).
Proof.
  induction p, q. reflexivity.
Qed.

End Altcats.


(** %\exerdone{2.4}{103}% 
Define, by induction on $n$, a general notion of $n$-dimensional path
in a type $A$, simultaneously with the type of boundaries for such paths. *)

(** %\soln%
A $0$-path in $A$ is an element $x : A$, so the type of $0$-paths is $A$.  A
$1$-path is an ordinary path $a = a'$ for some $a, a' : A$, so the type of
$1$-paths is $\sm{a, a':\text{$0$-\textsf{path}}}(a=a')$.  So, in general, the
type of $(n+1)$-paths should be $\sm{p, q : \text{$n$-\textsf{path}}}(p = q)$.

As for the boundaries, one option is to say that the boundary of an
$(n+1)$-path is the ordered pair of its endpoints, so that an $n$-boundary
is a term of type $\text{$n$-\textsf{path}} \times \text{$n$-\textsf{path}}$.  I'd like to define this be mutual induction, but [fst] doesn't want to act on [(boundary A n)], so I can't.

On the other hand, thinking in terms of a simplicial complex, an $n$-path is an
$n$-simplex, so its boundary should be an $(n-1)$-chain.  The type of
boundaries is then the image of the boundary map restricted to $n$-simplices.
To define the boundary map, send an $n$-path $r : p = q$ between $p, q : x = y$
to the $(n-1)$-path $p \ct q^{-1} : x = x$.  So the type of boundaries is the
type of loops that factor as $p \ct q^{-1}$.  But this is equivalent to the
product type of the previous paragraph, so this definition ends up being the
same.

Thanks to Kabelo Moiloa for pointing out that my original answer was wrong.
*)

Fixpoint npath (A:Type) (n:nat) : Type :=
  match n with
    | O => A
    | S n' => {bd : npath A n' * npath A n' & fst bd = snd bd}
  end.

Definition boundary (A:Type) (n:nat) : Type := (npath A n) * (npath A n).


(** %\exerdone{2.5}{103}% 
Prove that the functions
%\begin{align*}
 (f(x) = f(y)) &\to (p_{*}(f(x)) = f(y)) \qquad\qquad\text{and} \\
 (p_{*}(f(x)) = f(y)) &\to (f(x) = f(y))
\end{align*}%
are inverse equivalences. *)

(** %\soln% 
Suppose that $x, y : A$, $p : x = y$, and $f : A
\to B$.  Then we have the objects 
%\[
  \mapfunc{f}(p) : (f(x) = f(y)) \\
  \transconst{B}{p}{f(x)} : (p_{*}(f(x)) = f(x))
\]%
thus
%\begin{align*}
  \left(\transconst{B}{p}{f(x)} \ct -\right)
  &:
  (f(x)=f(y))
  \to
  (p_{*}(f(x)) = f(y))
  \\
  \left((\transconst{B}{p}{f(x)})^{-1} \ct -\right)
  &:
  (p_{*}(f(x))=f(y))
  \to
  (f(x) = f(y))
\end{align*}%
Which are our maps.  Composing the first with the second, we obtain an element
%\[
  \left(\transconst{B}{p}{f(x)} \ct
  \left((\transconst{B}{p}{f(x)})^{-1} \ct -\right)\right)
\]%
of $f(x) = f(y)$.  Using Lemma 2.1.4, we can show that this is homotopic to the
identity:
%\begin{align*}
  &\prd{q:f(x)=f(y)}
  \left(
  \transconst{B}{p}{f(x)} \ct
  \left((\transconst{B}{p}{f(x)})^{-1} \ct q\right)
  =
  q\right)
  \\&= 
  \prd{q:f(x)=f(y)}
  \left(
  \left(\transconst{B}{p}{f(x)} \ct
  (\transconst{B}{p}{f(x)})^{-1}\right) \ct q
  =
  q\right)
  \\&= 
  \prd{q:f(x)=f(y)}
  \left(
  q
  =
  q\right)
\end{align*}%
which is inhabited by $\refl{q}$.  The same argument goes the other way, so
this concatenation is an equivalence.
*)


Definition eq2_3_6 {A B : Type} {x y : A} (f : A -> B) (p : x = y) (q : f x = f y) : 
    (@transport _ (fun _ => B) _ _ p (f x) = f y) := 
    (transport_const p (f x)) @ q.

Definition eq2_3_7 {A B : Type} {x y : A} (f : A -> B) (p : x = y)
  (q : @transport _ (fun _ => B) _ _ p (f x) = f y) : 
  (f x = f y) :=
  (transport_const p (f x))^ @ q.

Lemma isequiv_transportconst (A B:Type) (x y z : A) (f : A -> B) (p : x = y) : 
  IsEquiv (eq2_3_6 f p).
Proof.
  refine (isequiv_adjointify _ (eq2_3_7 f p) _ _); intro q;
    unfold eq2_3_6, eq2_3_7; path_induction; reflexivity.
Qed.


(** %\exerdone{2.6}{103}% 
Prove that if $p : x = y$, then the function $(p \ct -) : (y = z) \to (x = z)$
is an equivalence.
*)

(** %\soln%
Suppose that $p : x = y$.  To show that $(p \ct -)$ is an equivalence, we need
to exhibit a quasi-inverse to it.  This is a triple $(g, \alpha, \beta)$ of a
function $g:(x = z) \to (y = z)$ and homotopies $\alpha : (p \ct -) \circ g \sim
\idfunc{x=z}$ and $\beta : g \circ (p \ct -) \sim \idfunc{y=z}$.  For $g$, we
can take $(p^{-1} \ct -)$.  For the homotopies, we can use the results of Lemma
2.1.4.  So we have
%\[
((p \ct -) \circ g) \sim \idfunc{x=z}
\equiv
\prd{q:x=z}(p \ct (p^{-1} \ct q) = q)
=
\prd{q:x=z}((p \ct p^{-1}) \ct q = q)
=
\prd{q:x=z}(\refl{x} \ct q = q)
=
\prd{q:x=z}(q = q)
\]%
which is inhabited by $\refl{q}$ and
%\[
(g \circ (p \ct -)) \sim \idfunc{y=z}
\equiv
\prd{q:y=z}(p^{-1} \ct (p \ct q) = q)
=
\prd{q:y=z}((p^{-1} \ct p) \ct q = q)
=
\prd{q:y=z}(\refl{y} \ct q = q)
=
\prd{q:y=z}(q = q)
\]%
which is inhabited by $\refl{q}$.  So $(p \ct -)$ has a quasi-inverse, hence it
is an equivalence.
*)

Module Altequivcat.

Lemma isequiv_concat (A:Type) (x y z : A) (p : x = y) 
  : IsEquiv (@concat A x y z p).
Proof.
  refine (isequiv_adjointify _ (concat p^) _ _); intro q;
    by path_induction.
Defined.

End Altequivcat.

(** %\exerdone{2.7}{104}% 
State and prove a generalization of Theorem 2.6.5 from cartesian products to
$\Sigma$-types.
*)

(** %\soln%
Suppose that we have types $A$ and $A'$ and type families $B:A\to\UU$ and
$B':A'\to\UU$, along with a function $g:A \to A'$ and a dependent function
$h:\prd{x:A} B(x) \to B'(f(x))$.  We can then define a function $f :
(\sm{x:A}B(x)) \to (\sm{x:A'}B'(x))$ by $f(x) \defeq (g(\fst x), h(\fst x, \snd
x))$.  
Let $x, y : \sm{a:A}B(a)$, and 
suppose that $p : \fst x = \fst y$ and that $q : p_{*}(\snd x) =
\snd y$.  The left-side of Theorem 2.6.5 generalizes directly to
$f(\pair^{=}(p, q))$, where now $\pair^{=}$ is given by the backward direction
of Theorem 2.7.2.  
    
The right hand side is trickier.  It ought to represent the application of $g$
and $h$, followed by the application of $\pair^{=}$, as Theorem 2.6.5 does.
Applying $g$ produces the first argument to $\pair^{=}$, $\apfunc{g}(p) \equiv
g(p)$.  For $h$, we'll need to construct the right object.  We need one of type
%\[
  (g(p))_{*}(h(\fst x, \snd x)) = h(\fst y, \snd y)
\]%
Which we'll construct by induction.  It suffices to consider the case where $x
\equiv (a, b)$, $y \equiv (a', b')$, $p \equiv \refl{a}$, and $q \equiv
\refl{b}$.  Then we need an object of type
%\[
  \left((g(\refl{a}))_{*}(h(a, b)) = h(a', b')\right)
  \equiv
  \left(h(a, b) = h(a', b')\right)
\]%
which we can easily construct by applying $h$ to $p$ and $q$.  So by induction, we have an object
%\[
  T(h, p, q) : 
  (g(p))_{*}(h(\fst x, \snd x)) = h(\fst y, \snd y)
\]%
such that $T(h, \refl{a}, \refl{b}) \equiv \refl{h(a, b)}$.

Now we can state the generalization.  We show that
%\[
  f(\pair^{=}(p, q)) = \pair^{=}(g(p), T(h, p, q))
\]%
by induction.  So let $x \equiv (a, b)$, $y \equiv (a', b')$, $p
\equiv \refl{a}$, and $q \equiv \refl{b}$.  Then we need to show that
%\[
  \refl{f((a, b))} = \refl{(g(a), h(a, b))}
\]%
But from the definition of $f$, this is a judgemental equality.  So we're done.
*)

Module Ex7.

Local Definition T {A A' : Type} {B : A -> Type} {B' : A' -> Type}
           {g : A -> A'} (h : forall a, B a -> B' (g a))
           {x y : {a:A & B a}}
           (p : x.1 = y.1) (q : p # x.2 = y.2)
  : (ap g p) # (h x.1 x.2) = h y.1 y.2.
Proof.
  destruct x as [a b], y as [a' b'].
  simpl in p. induction p.
  simpl in *. f_ap.
Defined.


Definition functor_sigma {A A' : Type} {B : A -> Type} {B' : A' -> Type}
           (g : A -> A') (h : forall a, B a -> B' (g a)) 
  : {x : A & B x} -> {x : A' & B' x}
  := fun z => (g z.1; h z.1 z.2).

Theorem ap_functor_sigma {A A' : Type} {B : A -> Type} {B' : A' -> Type}
                       (g : A -> A') (h : forall a, B a -> B' (g a))
                       (x y : {a:A & B a})
                       (p : x.1 = y.1) (q : p # x.2 = y.2)
  :  ap (functor_sigma g h) (path_sigma B x y p q) 
     = path_sigma B' (functor_sigma g h x) (functor_sigma g h y) 
                  (ap g p) (T h p q). 
Proof.
  intros. 
  destruct x as [a b], y as [a' b']. 
  simpl in p. induction p. 
  simpl in q. induction q. 
  reflexivity.
Defined.

End Ex7.



(** %\exerdone{2.8}{104}% 
State and prove an analogue of Theorem 2.6.5 for coproducts.
*)

(** %\soln%
Let $A, A', B, B' : \UU$, and let $g: A \to A'$ and $h: B \to B'$.  These allow
us to construct a function $f : A + B \to A' + B'$ given by
%\[
  f(\inl(a)) \defeq \inl'(g(a))
  \qquad\qquad
  f(\inr(b)) \defeq \inr'(h(b))
\]%

Now, we want to show that $\apfunc{f}$ is functorial, which requires something
corresponding to $\pair^{=}$.  The type of this function will vary depending on
which two $x, y : A+B$ we consider. Suppose that $p : x = y$; there are four
cases:

- $x = \inl(a_{1})$ and $y = \inl(a_{2})$.  Then $\pair^{=}$ is given by
  $\apfunc{\inl}$, and we must show that
  %\[
    f(\inl(p)) = \inl'(g(p))
  \]%
  which is easy with path induction; it suffices to consider $p \equiv
  \refl{a}$, which reduces our equality to
  %\[
    \refl{f(\inl(a))} = \refl{\inl'(g(a))}
  \]%
  and this is a judgemental equality, given the definition of $f$.

- $x = \inl(a)$ and $y = \inr(b)$.  Then by 2.12.3 $(x = y) \eqvsym \emptyt$,
  and $p$ allows us to construct anything we like.

- $x = \inr(b)$ and $y = \inl(a)$ proceeds just as in the previous case.

- $x = \inr(b)$ and $y = \inr(b)$ proceeds just as in the first case.

Since these are all the cases, we've proven an analogue to Theorem 2.6.5 for
coproducts.  A closer analogue would not involve $p : x = y$, but rather
equalities $p : a =_{A} a'$ and $q : b =_{B} b'$, and then would show that for
all the different cases, $\mapfunc{f}$ is functorial.  However, this follows
from the version proven, which is more simply stated.
*)

Theorem ap_functor_sum : 
  forall (A A' B B' : Type) (g : A -> A') (h : B -> B') (x y : A+B) (p : x = y),
  ap (functor_sum g h) p
  = path_sum (functor_sum g h x) (functor_sum g h y)
             (path_sum_inv (ap (functor_sum g h) p)).
Proof.
  intros.
  destruct x as [a | b], y as [a' | b'].
  induction p. reflexivity.
  contradiction ((equiv_path_sum _ _)^-1 p).
  contradiction ((equiv_path_sum _ _)^-1 p).
  induction p. reflexivity.
Defined.
  
     
(** %\exerdone{2.9}{104}% 
Prove that coproducts have the expected universal property,
%\[
  (A + B \to X) \eqvsym (A \to X) \times (B \to X).
\]%
Can you generalize this to an equivalence involving dependent functions?
*)

(** %\soln%
To define the ex2_9_f map, let $h : A+B \to X$ and define $f : (A+B\to X) \to
(A\to X) \times (B \to X)$ by
%\[
  f(h) \defeq (\lam{a}h(\inl(a)), \lam{b}h(\inr(b)))
\]%
To show that $f$ is an equivalence, we'll need a quasi-inverse, given by
%\[
 g(h) \defeq \rec{A+B}(X, \fst h, \snd h)
\]%
As well as the homotopies $\alpha : f\circ g \sim \idfunc{(A\to X)\times(B \to
X)}$ and $\beta : g \circ f \sim \idfunc{A+B\to X}$.  For $\alpha$ we need a
witness to
%\begin{align*}
  &\prd{h:(A\to X) \times (B\to X)} (f(g(h)) 
  = \idfunc{(A\to X) \times (B\to X)}(h))
  \\&\equiv
  \prd{h:(A\to X) \times (B\to X)} (
  (\lam{a}\rec{A+B}(X, \fst h, \snd h, \inl(a)),
   \lam{b}\rec{A+B}(X, \fst h, \snd h, \inr(b)))
  = h)
  \\&\equiv
  \prd{h:(A\to X) \times (B\to X)} ((\fst h, \snd h) = h)
\end{align*}%
and this is inhabited by $\uppt$.  For $\beta$, we need an inhabitant of
%\begin{align*}
  &\prd{h:A+B\to X} (g(f(h)) = \idfunc{A+B\to X}(h))
  \\&\equiv
  \prd{h:A+B\to X} (
  \rec{A+B}(X, \lam{a}h(\inl(a)), \lam{b}h(\inr(b)))
  = h)
\end{align*}%
which, assuming function extensionality, is inhabited.  So $(g,
\alpha, \beta)$ is a quasi-inverse to $f$, giving the universal property.
*)

Module Ex2_9.

Theorem equiv_sum_distributive `{Funext} (A B X : Type)
: (A + B -> X) <~> (A -> X) * (B -> X).
Proof.

  simple refine (equiv_adjointify _ _ _ _).
  - intro f. split.
    + intro a. apply (f (inl a)).
    + intro b. apply (f (inr b)).
      
  - intros [f g] [a | b].
    + apply (f a).
    + apply (g b).

  - intro f. reflexivity.
  
  - intro f. apply path_arrow. intros [a | b]; reflexivity.
Defined.

End Ex2_9.


Theorem equiv_forall_distributive `{Funext} (A B : Type) (C : A + B -> Type)
  : (forall p, C p) <~> (forall a, C (inl a)) * (forall b, C (inr b)).
Proof.
  simple refine (equiv_adjointify _ _ _ _).
  
  (* forward *)
  intro f. split. 
    intro a. exact (f (inl a)).
    intro b. exact (f (inr b)).

  (* back *)
  intro f. destruct f as [f g]. intro p. destruct p as [a | b].
    exact (f a). exact (g b).
  
  (* section *)
  intro f. reflexivity.

  (* retract *)
  intro f. apply path_forall. intro p. destruct p as [a | b]; reflexivity.
Defined.
  


(** %\exerdone{2.10}{104}% 
Prove that $\Sigma$-types are ``associative'', in that for any $A:\UU$ and
families $B : A \to \UU$ and $C : (\sm{x:A} B(x)) \to \UU$, we have
%\[
  \left(\sm{x:A}\sm{y:B(x)}C((x, y))\right)
  \eqvsym
  \left(\sm{p:\sm{x:A}B(x)}C(p)\right)
\]%
*)

(** %\soln%
The map
%\[
  f(a, b, c) \defeq ((a, b), c)
\]%
where $a:A$, $b:B(a)$, and $c : C((a, b))$ is an equivalence.  For a
quasi-inverse, we have
%\[
  g(p, c) \defeq (\fst p, \snd p, c)
\]%
As proof, by induction we can consider the case where $p \equiv (a, b)$.  Then
we have
%\[
  f(g((a, b), c))
  =
  f(a, b, c)
  =
  ((a, b), c)
\]%
and
%\[
  g(f(a, b, c))
  =
  g((a, b), c)
  =
  (a, b, c)
\]%
So $f$ is an equivalence.
*)

Module Ex2_10.

Theorem equiv_sigma_assoc (A : Type) (P : A -> Type) (Q : {a : A & P a} -> Type)
  : {a : A & {p : P a & Q (a; p)}} <~> {x : _ & Q x}.
Proof.
  simple refine (equiv_adjointify _ _ _ _).
  
  (* forward *)
  intro w. destruct w as [a [p q]]. apply ((a; p); q).
  
  (* back *)
  intro w. destruct w as [[a p] q]. apply (a; (p; q)).

  (* section *)
  intro w. reflexivity.

  (* retract *)
  intro w. reflexivity.
Defined.

End Ex2_10.

(** %\exerdone{2.11}{104}% 
A (homotopy) commutative square
%\[
  \xymatrix{
  P \ar[r]^{h} \ar[d]_{k} & A \ar[d]^{f} \\
  B \ar[r]_{g} & C
  }
\]%
consists of functions $f$, $g$, $h$, and $k$ as shown, together with a path $f
\circ h = g \circ k$.  Note that this is exactly an element of the pullback $(P
\to A) \times_{P \to C} (P \to B)$ as defined in 2.15.11.  A commutative square
is called a (homotopy) pullback square if for any $X$, the induced map
%\[
  (X \to P) \to (X \to A) \times_{X \to C} (X \to B)
\]%
is an equivalence.  Prove that the pullback $P \defeq A \times_{C} B$ defined
in 2.15.11 is the corner of a pullback square.
*)

(** %\soln%
I'll start using the usual notation $\proj{n}^{j}$ for the $j$th projection
from an $n$-tuple.  So, for example, $\proj{3}^{2} \defeq \fst \circ \snd$.
To show that $P$ is the corner of a pullback square, we need to produce the
three other corners and show that it is a pullback.  Given $f : A \to C$ and $G
: B \to C$, we define
%\[
  P \defeq \sm{a:A}\sm{b:B} (f(a) = g(b))
\]%
I claim this is the corner of the following pullback square:
%\[
  \xymatrix @R=.5in @C=.5in {
  P \ar[r]^{\proj{3}^{2}} \ar[d]_{\proj{3}^{1}} & B \ar[d]^{g} \\
  A \ar[r]_{f} & C
  }
\]%
To show that it's commutative, it suffices to consider an element $(a, b, p)$
of $P$.  We then have
%\[
  g(\proj{3}^{2}(a, b, p)) = g(b) = f(a) = f(\proj{3}^{1}(a, b, p))
\]%
making the square commutative.

To show that it has the required universal property, we need to construct the
equivalence.  Suppose that $h : X \to P$.  Then we can compose it in either
direction around the square to give
%\[
  f \circ \proj{3}^{1} \circ h : X \to C
  \qquad\qquad
  g \circ \proj{3}^{2} \circ h : X \to C
\]%
If we can show that these two maps are equal, then we can produce an element of
$(X \to A) \times_{X \to C} (X \to B)$.  And we can, using function
extensionality.  Suppose that $x:X$.  Then $h(x) : P$, which by induction we
can assume is of the form $h(x) \equiv (a, b, p)$, with $p : f(a) = g(b)$.
This means that
%\[
 f(\proj{3}^{1}(h(x))) \equiv f(\proj{3}^{1}(a, b, p)) \equiv f(a)
\]%
and
%\[
  g(\proj{3}^{2}(a, b, c)) \equiv g(b)
\]%
and $p$ proves that these are equal.  So by function extensionality,
%\[
  f \circ \proj{3}^{1} \circ h = g \circ \proj{3}^{2} \circ h
\]%
meaning that we can define
%\[
  h \mapsto (\proj{3}^{1} \circ h, \proj{3}^{2} \circ h, \funext(\proj{3}^{3}
  \circ h))
\]%
giving the forward map $(X \to P) \to (X \to A) \times_{X \to C} (X \to B)$.

We now need to exhibit a quasi-inverse.  Suppose that $h' : (X \to A)
\times_{X \to C} (X \to B)$.  By induction, we may assume that $h' = (h_{A},
h_{B}, q)$, where $q : f \circ h_{A} = g \circ h_{B}$.  We want to construct a
function $X \to P$, so suppose that $x:X$.  Then we can construct an element of
$P$ like so:
%\[
  h(x) \defeq (h_{A}(x), h_{B}(x), \happly(q)(x))
\]%
Note that this expression is well-typed, since $h_{A}(x) : A$, $h_{B}(x) : B$,
and $\happly(q)(x) : f(h_{A}(x)) = g(h_{B}(x))$.

In order to show that this is a quasi-inverse, we need to show that the two
possible compositions are homotopic to the identity.  Suppose that $h : X \to
P$; then applying the forward and backward constructions gives
%\[
  (x \mapsto (\proj{3}^{1}(h(x)), \proj{3}^{2}(h(x)),
  \happly(\funext(\proj{3}^{3} \circ h))(x)))
  \equiv
  (x \mapsto (\proj{3}^{1}(h(x)), \proj{3}^{2}(h(x)), \proj{3}^{3}(h(x))))
\]%
which by function extensionality is clearly equal to $h$.

For the other direction, suppose that $h' : (X \to A) \times_{X \to C} (X \to
B)$, which by induction we may suppose is of the form $(h_{A}, h_{B}, p)$.
Going back and forth gives
%\begin{align*}
  &\left(
    \proj{3}^{1} \circ (x \mapsto (h_{A}(x), h_{B}(x), \happly(p)(x))),
    \right.\\&\phantom{---}\left.
    \proj{3}^{2} \circ (x \mapsto (h_{A}(x), h_{B}(x), \happly(p)(x))),
    \right.\\&\phantom{---}\left.
    \funext(\proj{3}^{3} \circ (x \mapsto (h_{A}(x), h_{B}(x), \happly(p)(x))))
  \right)
\end{align*}%
applying function extensionality again results in
%\[
  (h_{A}, h_{B}, \funext(\happly(p)))
  \equiv
  (h_{A}, h_{B}, p)
\]%
So we have an equivalence.
*)


Section Ex11.

Context {A B C : Type} (X : Type) (f: A -> C) (g: B -> C). 

Local Definition square_commutes `{Funext} 
  : f o (fun p : (Pullback f g) => p.1) = g o (fun p : (Pullback f g) => p.2.1).
Proof.
  apply path_forall. intro p. destruct p as [a [b p]]. apply p.
Defined.

Lemma pullback_uprop `{Funext}  
  : (X -> (Pullback f g)) <~> Pullback (fun h : X -> A => f o h) 
                                       (fun h : X -> B => g o h).
Proof.
  simple refine (equiv_adjointify _ _ _ _).
  
  (* forward *)
  intro h. exists (fun x => pr1 (h x)). exists (fun x => pr1 (pr2 (h x))).
  apply path_forall. intro x. apply (h x).2.2.

  (* backward *)
  intros h x. destruct h as [h1 [h2 q]]. refine (h1 x; (h2 x; apD10 q x)).

  (* section *)
  intro h. destruct h as [h1 [h2 q]].
  apply path_sigma_uncurried. simpl. exists 1.
  apply path_sigma_uncurried. simpl. exists 1. simpl.
  apply (ap apD10)^-1. apply eisretr.

  (* retract *)
  intro h. simpl.
  apply path_forall. intro x.
  apply path_sigma_uncurried. exists 1. simpl.
  apply path_sigma_uncurried. exists 1. simpl.
  change (h x).2.2 with ((fun x' => (h x').2.2) x). f_ap.
  apply eisretr.
Defined.
  
End Ex11.


(** %\exerdone{2.12}{104}% 
Suppose given two commutative squares
%\[\xymatrix{
  A \ar[r] \ar[d] & C \ar[r] \ar[d] & E \ar[d] \\
  B \ar[r] & D \ar[r] & F
}\]%
and suppose that the right-hand square is a pullback square.  Prove that the
left-hand square is a pullback square if and only if the outer rectangle is a
pullback square.
*)

(** %\soln%
Label the arrows
%\[\xymatrix{
  A \ar[r] \ar[d] & C \ar[r]^{j} \ar[d]_{g} & E \ar[d]^{k} \\
  B \ar[r]_{f} & D \ar[r]_{h} & F
}\]%
Suppose that the right-hand square is a pullback.  That is, suppose we have
%\[
  (X \to C) \eqvsym (X \to D) \times_{(X \to F)} (X \to E)
\]%
We want to show that
%\[
  \eqv{(X \to A)}{(X \to B) \times_{(X \to D)} (X \to C)}
\]%
if and only if
%\[
  \eqv{(X \to A)}{(X \to B) \times_{(X \to F)} (X \to E)}
\]%
It suffices to show that 
%\[
  \eqv{(X \to B) \times_{(X \to D)} (X \to C)}{(X \to B) \times_{(X \to F)} (X \to E)}
\]%
because $\eqvsym$ is an equivalence relation.  And for this it suffices to show
that for any $l : X \to B$,
%\[
  \left(
    \sm{m : X \to C}(f \circ l = g \circ m)
  \right)
  \eqvsym
  \left(
    \sm{m : X \to E}(h \circ f \circ l = k \circ m)
  \right)
\]%
by the functorality of the $\Sigma$-type former.  Similarly, by our hypothesis
that the right square is a pullback, we have
%\[
  \left(
    \sm{m : (X \to D) \times_{(X \to F)} (X \to E)}(f \circ l = \fst(m))
  \right)
  \eqvsym
  \left(
    \sm{m : X \to E}(h \circ f \circ l = k \circ m)
  \right)
\]%
But, since the fiber product is symmetric and $\Sigma$-types associative and
commutative on constant type families, this is the same as the condition that
%\[
  \left(
    \sm{m : X \to E} \sm{p : \sm{n : X \to D}(h \circ n = k \circ m)}
        (f \circ l = \fst(p))
  \right)
  \eqvsym
  \left(
    \sm{m : X \to E}(h \circ f \circ l = k \circ m)
  \right)
\]%
So again by the functorality of the $\Sigma$ former, it suffices to show that
for any $m : X \to E$ we have
%\[
  \left(
    \sm{p : \sm{n : X \to D}(h \circ n = k \circ m)}
        (f \circ l = \fst(p))
  \right)
  \eqvsym
  \left(
    h \circ f \circ l = k \circ m
  \right)
\]%
or, by associativity of the $\Sigma$ former and symmetry of products,
%\[
  \left(
    \sm{p : \sm{n : X \to D} (f \circ l = n)}
    (h \circ \fst(p) = k \circ m)
  \right)
  \eqvsym
  \left(
    h \circ f \circ l = k \circ m
  \right)
\]%
Finally, these are equivalent by Lemma 3.11.9.  That's next chapter, but it's
also straightforward to construct an explicit equivalence.
*)

Lemma equiv_const_sigma_prod (A B : Type) : {a : A & B} <~> A * B.
Proof.
  simple refine (equiv_adjointify _ _ _ _).
  intro w. apply (w.1, w.2).
  intro w. apply (fst w; snd w).
  intro w. apply eta_prod.
  intro w. apply eta_sigma.
Defined.

Lemma equiv_sigma_comm (A B : Type) (P : A -> B -> Type)
  : {a : A & {b : B & P a b}} <~> {b : B & {a : A & P a b}}.
Proof.
  simple refine (equiv_adjointify _ _ _ _).
  intro w. apply (w.2.1; (w.1; w.2.2)).
  intro w. apply (w.2.1; (w.1; w.2.2)).
  intro w. simpl. apply eta_sigma.
  intro w. simpl. apply eta_sigma.
Defined.
  

Lemma equiv_sigma_contr_base (A : Type) (P : A -> Type) (HA : Contr A)
  : {a : A & P a} <~> P (center A).
Proof.
  simple refine (equiv_adjointify _ _ _ _).
  intro w. apply (transport _ (contr w.1)^). apply w.2.
  intro p. apply (center A; p).

  intro p. simpl.
  transparent assert (H: (center A = center A)). apply contr_paths_contr.
  transparent assert (H': ((contr (center A))^ = 1)). apply path_ishprop.
  path_via (transport P 1 p). f_ap.

  intro w. apply path_sigma_uncurried.
  simpl. exists (contr w.1).
  apply transport_pV.
Defined.


Module pullback_lemma.

Variables (A B C D E F X : Type) 
          (f : B -> D) (g : C -> D) (h : D -> F) (j : C -> E) (k : E -> F)
          (r : h o g = k o j).

Local Definition xc_to_plbk 
  : (X -> C) -> Pullback (fun f : X -> D => h o f) (fun f : X -> E => k o f).
Proof.
  intro l. refine (g o l; (j o l; ap (fun m => m o l) r)).
Defined.
  
Variable (He : IsEquiv xc_to_plbk).

Theorem pbl_helper `{Funext}
  : Pullback (fun m : X -> B => f o m) (fun m : X -> C => g o m)
    <~>
    Pullback (fun m : X -> B => (h o f) o m) (fun m : X -> E => k o m).
Proof.
  refine (equiv_functor_sigma_id _). intro j.

  equiv_via {c : Pullback (fun m : X -> D => h o m) 
                          (fun m : X -> E => k o m) & f o j = c.1}.
  simple refine (equiv_functor_sigma' _ _). 
  apply (BuildEquiv _ _ xc_to_plbk He). intro l.
  apply equiv_idmap.

  equiv_via {c : {c : X -> E & {b : X -> D & h o b = k o c}} & f o j = c.2.1}.
  simple refine (equiv_functor_sigma' _ _).
  simple refine (equiv_sigma_comm _ _ _). intro c. apply equiv_idmap.

  equiv_via {c : X -> E & {l : {b : X -> D & h o b = k o c} & f o j = l.1}}.
  apply equiv_inverse. refine (equiv_sigma_assoc _ _).

  refine (equiv_functor_sigma_id _). intro m.
  
  equiv_via {l : X -> D & {_ : h o l = k o m & f o j = l}}.
  apply equiv_inverse. refine (equiv_sigma_assoc _ _).

  equiv_via {l : X -> D & {_ : f o j = l & h o l = k o m}}.
  refine (equiv_functor_sigma_id _). intro l.
  equiv_via ((h o l = k o m) * (f o j = l)).
  apply equiv_const_sigma_prod.
  equiv_via ((f o j = l) * (h o l = k o m)).
  apply equiv_prod_symm.
  apply equiv_inverse. apply equiv_const_sigma_prod.

  equiv_via {l : {n : X -> D & f o j = n} & h o l.1 = k o m}.
  refine (equiv_sigma_assoc _ _).

  equiv_via (h o (center {n : X -> D & f o j = n}).1 = k o m).
  refine (equiv_sigma_contr_base _ _ _).

  simple refine (equiv_adjointify _ _ _ _).
  intro eq. refine (_ @ eq). apply (ap (compose h)).
  apply (center {n : X -> D & f o j = n}).2.
  intro eq. refine (_ @ eq). apply (ap (compose h)).
  apply (center {n : X -> D & f o j = n}).2^.
  intro eq. apply moveR_Mp. refine (whiskerR _ eq). refine (ap_V (compose h) _).
  intro eq. apply moveR_Mp. refine (whiskerR _ eq). 
  refine (_ @ (ap_V (compose h) _)). f_ap.
Defined.

  

Lemma pullback_lemma `{Funext}
  : (X -> A) <~> Pullback (fun m : X -> B => f o m) 
                          (fun m : X -> C => g o m)
    <->
    (X -> A) <~> Pullback (fun m : X -> B => (h o f) o m) 
                          (fun m : X -> E => k o m).
Proof.
  split.
  intro H'.
  equiv_via (Pullback (fun m : X -> B => f o m) (fun m : X -> C => g o m)).
  apply H'. apply pbl_helper.
  intro H'.
  equiv_via (Pullback (fun m : X -> B => (h o f) o m) 
                      (fun m : X -> E => k o m)).
  apply H'. apply equiv_inverse. apply pbl_helper.
Defined.
  
End pullback_lemma.



(** %\exerdone{2.13}{104}% 
Show that $(\bool \eqvsym \bool) \eqvsym \bool$.
*)

(** %\soln%
The result essentially says that $\bool$ is equivalent to itself in two ways:
the identity provides one equivalence, and negation gives the other.  So we
first define these.  $\idfunc{\bool}$ is its own quasi-inverse; we have
$\idfunc{\bool} \circ \idfunc{\bool} \equiv \idfunc{\bool}$, so $\idfunc{\bool}
\circ \idfunc{\bool}
\sim \idfunc{\bool}$ easily.  $\lnot$ is also its own quasi-inverse, since for
any $x$, $\lnot\lnot x = x$.

To show the result, we need to map $\idfunc{\bool}$ and $\lnot$ onto $\bool$ is
a quasi-invertible way.  But we need to define this map on all of $\bool
\eqvsym \bool$.  So for any $h : \bool\eqvsym\bool$, let $f(h) = h(0_{\bool})$,
and define $g : \bool \to (\bool \eqvsym \bool)$ by
%\[
  g(0_{\bool}) = \idfunc{\bool} 
  \qquad\qquad
  g(1_{\bool}) = \lnot
\]%

To show that these are quasi-inverses,
note first that whatever else is the case, an equivalence
$\bool \eqvsym \bool$ can't be a constant function, which we can prove by a case
analysis.  Each of $f(0_{\bool})$ and $f(1_{\bool})$ is in $\bool$, so it is
either $0_{\bool}$ or $1_{\bool}$.  So we have the cases:
 - $f(0_{\bool}) = f(1_{\bool})$, in which case we can apply $f^{-1}$ to either side to get a contradiction, or
 - $f(0_{\bool}) = \lnot f(1_{\bool})$. In which case we have the result
Showing that $f \circ g \sim \idfunc{\bool}$ is easy, since we can do it by
cases.  We have
%\begin{align*}
  f(g(0_{\bool})) &= f(\idfunc{\bool}) = \idfunc{\bool}(0_{\bool}) = 0_{\bool}
  \\
  f(g(1_{\bool})) &= f(\lnot) = \lnot 0_{\bool} = 1_{\bool}
\end{align*}%
For the other direction, suppose that $h : \bool \eqvsym \bool$ and that
function extensionality holds.
$h(0_{\bool})$ is either $0_{\bool}$ or $1_{\bool}$.  If the first, then
because $h$ isn't constant we have $h(1_{\bool}) = \lnot h(0_{\bool}) =
1_{\bool}$, hence $h = \idfunc{\bool}$.  Furthermore,
%\[
  g(f(h)) = g(h(0_{\bool})) = g(0_{\bool}) = \idfunc{\bool} = h
\]%
The same argument works for the other case.  So $f$ is an equivalence, and
$(\bool \eqvsym \bool) \eqvsym \bool$.

*)

Lemma equiv_not_const (f : Bool -> Bool) `{IsEquiv Bool Bool f} : 
  f false = negb (f true).
Proof.
  assert (f^-1 (f true) = true) as Ht by apply eissect.
  assert (f^-1 (f false) = false) as Hf by apply eissect.
  destruct (f true), (f false).
  contradiction (true_ne_false (Ht^ @ Hf)).
  reflexivity. reflexivity.
  contradiction (true_ne_false (Ht^ @ Hf)).
Defined.

Theorem equiv_bool_equiv_bool `{Funext} : (Bool <~> Bool) <~> Bool.
Proof.
  simple refine (equiv_adjointify _ _ _ _).
  - intro f. apply (f false).
  - intro b. destruct b.
    (* Case : b true; send to negation *)
    + refine (equiv_adjointify negb negb _ _); intro b; destruct b; reflexivity.
    (* Case : b false; send to identity *)
    + refine (equiv_adjointify idmap idmap _ _); intro b; reflexivity.
  - intro b. destruct b; reflexivity.
  - intro f. apply path_equiv. apply path_arrow. intro b.
    assert (f false = negb (f true)) as Hf by apply (equiv_not_const f).
    destruct b, (f true), (f false);
      try (reflexivity);
      try (contradiction (true_ne_false Hf));
      try (contradiction (false_ne_true Hf)).
Defined.
    
    
  
(** %\exerdone{2.14}{104}% 
Suppose we add to type theory the equality reflection rule which says that if
there is an element $p : x = y$, then in fact $x \equiv y$.  Prove that for any
$p : x = x$ we have $p \equiv \refl{x}$.
*)

(** %\soln%
Suppose that $p : x = x$; we show that $p = \refl{x}$, by path induction.  It
suffices to consider the case where $p \equiv \refl{x}$, in which case we have
$\refl{\refl{x}} : \refl{x} = \refl{x}$.  Thus $p = \refl{x}$ is inhabited, so
by the equality reflection rule, $p \equiv \refl{x}$.
*)

(** %\exerdone{2.15}{105}%
Show that Lemma 2.10.5 can be strengthened to
%\[
  \transfib{B}{p}{-} =_{B(x)\to B(y)} \idtoeqv(\mapfunc{B}(p))
\]%
without using function extensionality.
*)

(** %\soln% 
By induction on $p$, we have
%\begin{align*}
  \transfib{B}{\refl{B(x)}}{-}
  &\equiv
  \idfunc{B(x)}
  \\&\equiv
  \transfib{X \mapsto X}{\refl{B(x)}}{-}
  \\&\equiv
  \transfib{X \mapsto X}{\mapfunc{B}(\refl{x})}{-}
  \\&\equiv
  \idtoeqv(\mapfunc{B}(\refl{x}))
\end{align*}%
**)

Definition idtoeqv {A B : Type} : (A = B) -> (A <~> B).
  intro X.
  refine (equiv_adjointify (transport idmap X) (transport idmap X^) _ _);
  intro b; [ apply (transport_pV idmap X) | apply (transport_Vp idmap X)].
Defined.

Lemma ex2_15 : forall (A : Type) (B : A -> Type) (x y : A) (p : x = y),
                 transport B p = idtoeqv (ap B p).
Proof.
  intros. unfold idtoeqv. induction p. reflexivity.
Defined.


(** %\exerdone{2.16}{105}%
Suppose that rather than function extensionality, we suppose only the existence
of an element
%\[
  \funext : \prd{A:\UU}\prd{B:A\to\UU}\prd{f, g : \prd{x:A}B(x)}
    (f \sim g) \to (f = g)
\]%
(with no relationship to $\happly$ assumed).  Prove that in fact, this is
sufficient to imply the whole function extensionality axiom (that $\happly$ is
an equivalence).
*)

(** %\soln%
Suppose that we have such an element, and let $A:\UU$, $B:A \to \UU$, and $f, g
: \prd{x:A}B(x)$.  I will suppress the $A$ and $B$ throughout.  If this implies the whole function extensionality
axiom, then it must be the case that we can construct the $\funext$
from the book, which has a particular computation rule.  This is not
too difficult; define
%\[
  \funext'(f, g, h) 
  \defeq 
  \funext(f, g, h) \ct (\funext(g, g, h))^{-1}
\]%
Then we have
%\begin{align*}
  \funext'(f, f, \lam{x}\refl{f(x)})
  &\equiv
  \funext(f, f, \lam{x}\refl{f(x)}) \ct (\funext(f, f,
  \lam{x}\refl{f(x)}))^{-1}
  \\&\equiv
  \refl{f}
\end{align*}%
by Lemma 2.1.4.  So now we need to show that $\funext'$ is a quasi-inverse to
$\happly$.  One direction is easy; since $\happly$ computes on $\refl{}$, by
induction we have
%\[
  \funext'(f, f, \happly(\refl{f}))
  \equiv
  \funext'(f, f, \lam{x}\refl{f(x)})
  \equiv
  \refl{f}
\]%
and thus $\funext'(f, g) \circ h \sim \idfunc{f=g}$.  The other direction
is more difficult.  We need to show that for all $h : f \sim g$,
$\happly(\funext(f, g, h)) = h$.  However, since $h$ isn't an inductive type,
we can't really do induction on it.  In the special case that $g \equiv f$ and
$h \equiv \lam{x}\refl{f(x)}$, we have
%\[
  \happly(\funext(f, f, \lam{x}\refl{f(x)}))
  \equiv
  \happly(\refl{f})
  \equiv
  \lam{x}\refl{f(x)}
\]%
So if we could find a way to reduce to this case, then we'd have the result.
One way to do this is to show that $(g, h) = (f, \lam{x}\refl{f(x)})$; since
we'd need to show this for all $g$ and $h$, this would be the same as showing
that the type
%\[
  \sm{g:\prd{x:A}B(x)}(f \sim g)
  \equiv
  \sm{g:\prd{x:A}B(x)}\prd{x:A}(f(x) = g(x))
\]%
is contractible, in the sense discussed in Exercise 1.7.  From Theorem 2.15.7,
this is equivalent to
%\[
  \prd{x:A}\sm{y:B(x)} (f(x) = y)
\]%
So if we can show that this type is contractible, then we can get the reduction
to the special case.

Now, we know from the previously-discussed Lemma 3.11.8 that for any $x$,
$\sm{y:B(x)} (f(x) = y)$ is contractible.  Now we want to apply Lemma 3.11.6,
but the proof requires function extensionality, so we'll have to try to recap
it.  Suppose that $j, k : \prd{x:A}\sm{y:B(x)}(f(x)=y)$.  For any $x : A$, we
have $j(x) = k(x)$ because $\sm{y:B(x)}(f(x) = y)$ is contractible.  Hence
there's some $p: j \sim k$, so $\funext'(j, k, p) : (j=k)$.  This means that
%\[
  \prd{x:A}\sm{y:B(x)} (f(x) = y)
\]%
is contractible.  So, transporting across the equivalence,
%\[
  \sm{g:\prd{x:A}B(x)}\prd{x:A}(f(x) = g(x))
  \equiv
  \sm{g:\prd{x:A}B(x)}(f \sim g)
\]%
is contractible.  Since any two contractible types are equivalent, this means
%\[
  \left(\tsm{g:\prd{x:A}B(x)} (f=g)\right)   
  \eqvsym
  \left(\tsm{g:\prd{x:A}B(x)} (f \sim g)\right)   
\]%
Since the first is contractible by Lemma 3.11.8.  Thus, we've shown
that $\total{\happly(f)}$, as defined in Definition 4.7.5, is an
equivalence.  By Theorem 4.7.7, this makes $\happly(f, g)$ an
equivalence for all $g$, proving the result. *)

Section Ex16.

Hypothesis funext : forall (A : Type) (B : A -> Type) (f g : forall (x:A), B x),
                      (f == g) -> (f = g).

Definition funext' {A : Type} {B : A -> Type} (f g : forall (x:A), B x) : 
  (f==g) -> (f=g) :=
  (fun h : (f==g) => (funext A B f g h) @ (funext A B g g (fun _ => 1))^).

Lemma funext'_beta {A : Type} {B : A -> Type} (f : forall (x:A), B x) : 
  funext' f f (fun _ => 1) = 1.
Proof.
  unfold funext'. rewrite concat_pV. reflexivity.
Defined.

Lemma Lemma3118 {C} : forall (c:C), Contr {x:C & c = x}.
Proof.
  intro c. exists (c; 1).
  intro x. destruct x as [x p]. path_induction. reflexivity.
Defined.

Lemma Lemma3116 A B f : Contr (forall x:A, {y : B x & f x = y}).
Proof.
  exists (fun x:A => (f x; 1)).
  intro k. apply (funext' (fun x => (f x; 1)) k); intro x.
  assert (Contr {y : B x & f x = y}). apply Lemma3118.
  destruct X. destruct center. rewrite <- (contr (k x)).
  apply path_sigma_uncurried. exists proj2_sig.
  induction proj2_sig. reflexivity.
Defined.  

Definition choice {A B f} : 
  (forall (x:A), {y : B x & f x = y}) -> {g : forall (x:A), B x & f == g}.
  intro k. exists (fun x:A => (k x).1).
  intro x. apply (k x).2.
Defined.

Definition choice_inv {A B f} :  
  ({g : forall (x:A), B x & f == g}) -> (forall (x:A), {y : B x & f x = y}).
  intros k x. apply (k.1 x; k.2 x).
Defined.

Lemma Theorem2157 {A B f} : IsEquiv(@choice A B f).
Proof.
  refine (isequiv_adjointify choice choice_inv _ _); intro k;
  unfold choice, choice_inv; simpl; [| apply funext'; intro x];
  apply path_sigma_uncurried; exists 1; reflexivity.
Defined.

Lemma contr_equiv_commute {A B} : A <~> B -> Contr A -> Contr B.
Proof.
  intros f k.
  exists (f (center A)). intro x. transitivity (f (f^-1 x)).
  apply (ap f). apply (contr (f^-1 x)).
  apply eisretr.
Defined.

Lemma reduce_to_refl {A B f} : Contr {g : forall x:A, B x & f == g}.
Proof.
  apply (@contr_equiv_commute (forall (x:A), {y : B x & f x = y})).
  refine (BuildEquiv _ _ choice Theorem2157).
  apply Lemma3116.
Defined.
  
Definition total_happly {A B f} : 
  {g : forall x:A, B x & f = g} -> {g : forall x:A, B x & f == g}.
  intros. destruct X. exists proj1_sig. apply apD10. apply proj2_sig.
Defined.

Definition total_happly_inv {A B f} : 
  {g : forall x:A, B x & f == g} -> {g : forall x:A, B x & f = g}.
  intros. destruct X. exists proj1_sig. apply funext'. apply proj2_sig.
Defined.

Lemma total_equivalence {A B f} : IsEquiv(@total_happly A B f).
Proof.
  refine (isequiv_adjointify total_happly total_happly_inv _ _); intro k.
  - assert (Contr {g : forall x:A, B x & f == g}). apply reduce_to_refl.
    destruct X. rewrite (contr k)^. 
    apply (contr (total_happly (total_happly_inv center)))^.
  - assert (Contr {g : forall x:A, B x & f = g}). apply Lemma3118.
    destruct X. rewrite (contr k)^. 
    apply (contr (total_happly_inv (total_happly center)))^.
Defined.

Definition total {A P Q} (f : forall (x:A), P x -> Q x) := fun w => (w.1; f w.1 w.2).

Lemma total_happly_is {A B f} : (@total_happly A B f) = total (@apD10 A B f).
Proof.
  unfold total_happly. 
  apply funext'; intro. 
  destruct x. 
  reflexivity.
Qed.

Lemma Theorem477 (A : Type) (P Q : A -> Type) (f : forall x:A, P x -> Q x) : 
  IsEquiv (total f) -> forall x:A, IsEquiv (f x).
Proof.
  intros e a.
  simple refine (isequiv_adjointify _ _ _ _).

  (* quasi-inverse *)
  destruct e. intro q.
  change a with (a; q).1.
  apply (transport _ (pr1_path (eisretr (a; q)))).
  apply (equiv_inv (a; q)).2.

  (* section *)
  destruct e. intro p.
  refine ((ap_transport _ _ _) @ _).
  apply (pr2_path (eisretr (a; p))).

  (* retract *)
  destruct e. intro p.
  change p with (a; p).2.
  refine (_ @ (pr2_path (eissect (a; p)))).
  unfold pr1_path. f_ap. simpl.
  change (a; f a p) with (total f (a; p)).
  rewrite eisadj. 
  refine ((ap_compose (total f) _ _)^ @ _).
  reflexivity.
Defined.
   

Theorem ex2_16 {A B} (f g : forall (x:A), B x) : IsEquiv(@apD10 A B f g).
Proof.
  apply Theorem477.
  rewrite <- total_happly_is.
  apply total_equivalence.
Qed.
  
End Ex16.

(** %\exerdone{2.17}{105}%
%\begin{enumerate}
  \item Show that if $A \eqvsym A'$ and $B \eqvsym B'$, then $(A \times B)
      \eqvsym (A' \times B')$.
  \item Give two proofs of this fact, one using univalence and one not using
  it, and show that the two proofs are equal.
  \item Formulate and prove analogous results for the other type formers:
  $\Sigma$, $\to$, $\Pi$, and $+$.
\end{enumerate}%
*)

(** %\soln%
(i)
Suppose that $g : A \eqvsym A'$ and $h : B \eqvsym B'$.  By the univalence
axiom, this means that $A = A'$ and $B = B'$.  But then $A \times B = A' \times
B'$, so again by univalence $(A \times B) \eqvsym (A' \times B')$. 
*)

Module Ex17.

Theorem equiv_functor_prod `{Univalence}: forall (A A' B B' : Type),
  A <~> A' -> B <~> B' -> (A * B) <~> (A' * B').
Proof.
  intros A A' B B' f g. 
  apply equiv_path_universe in f.
  apply equiv_path_universe in g.
  apply equiv_path_universe.
  apply (transport (fun x:Type => A * B = A' * x) g).
  apply (transport (fun x:Type => A * B = x * B) f).
  reflexivity.
Defined.

(**
%\noindent%
(ii) To prove this without univalence, we construct an explicit
equivalence.  Suppose that $f : A \to A'$ and $g : B \to B'$ are both equivalences, and define $h : A \times B \to A' \times B'$ by
%\[
  h(a, b) \defeq (f(a), g(b))
\]%
with the appropriate inverse
%\[
  h^{-1}(a', b') \defeq (f^{-1}(a'), g^{-1}(b'))
\]%
Clearly these are quasi-inverses, since
%\[
  h(h^{-1}(a', b')) 
  \equiv h(f^{-1}(a'), g^{-1}(b'))
  \equiv (f(f^{-1}(a')), g(g^{-1}(b')))
  \equiv (a', b')
\]%
and vice versa.
*)

Theorem equiv_functor_prod' : forall (A A' B B' : Type),
  A <~> A' -> B <~> B' -> (A * B) <~> (A' * B').
Proof.
  intros A A' B B' f g.
  refine (equiv_adjointify (fun z => (f (fst z), g (snd z)))
                           (fun z => (f^-1 (fst z), g^-1 (snd z)))
                           _ _); 
    intro z; destruct z; apply path_prod; simpl;
    try (apply eisretr); try (apply eissect).
Defined.

(** %\noindent%
To prove that the proofs are equivalent, it suffices to show that the
underlying functions are equal, by Lemma 3.5.1.  
*)

Theorem equal_proofs `{Univalence} : equiv_functor_prod = equiv_functor_prod'.
Proof.
  unfold equiv_functor_prod, equiv_functor_prod'. simpl. 
  apply path_forall; intro A.  apply path_forall; intro A'.
  apply path_forall; intro B.  apply path_forall; intro B'.
  apply path_forall; intro f.  apply path_forall; intro g.
  

  unfold equiv_path, equiv_adjointify.
  apply path_equiv. simpl. apply path_forall; intro z.
  destruct z as [a b]. simpl.
  rewrite transport_paths_Fr. rewrite transport_paths_Fr.
  refine ((transport_pp _ _ _ _) @ _).
  refine ((transport_idmap_ap _ _ _ _ _ _)^ @ _).
  refine ((transport_prod _ _) @ _). 
  apply path_prod; simpl.
    (* fst *)
    refine ((transport_const _ _) @ _).
    rewrite transport_pp. 
    rewrite <- (transport_idmap_ap Type (fun y => y * B)).
    rewrite transport_prod. simpl.
    refine ((transport_path_universe_uncurried _ _) @ _).
    reflexivity.

    (* snd *)
    refine ((transport_path_universe_uncurried _ _) @ _). f_ap.
    path_via (snd (f a, b)). f_ap.
    refine ((transport_pp _ _ _ _) @ _).
    refine ((transport_idmap_ap _ _ _ _ _ _)^ @ _).
    refine ((transport_prod _ _) @ _).
    apply path_prod; simpl. f_ap.
    apply transport_idmap_path_universe_uncurried.
    apply transport_const.
Defined.
    
    
    

(** %\noindent%
(iii)  The proofs of the rest of these are pretty much routine.  With
univalence, we can just convert everything to equality, rewrite, and then
convert back to equivalences.  However, since Coq's rewriting approach can be
fiddly, we sometimes have to write things out explicitly.  Most of the
conceptual work in this problem is just stating the generalizations, though,
which are as follows:
%\begin{description}
\item[$\Sigma$]  If $f : A \eqvsym A'$ and for all $x:A$ we have $B(x) \eqvsym
B'(f(x))$, then $(\sm{x:A}B(x)) \eqvsym (\sm{x':A'} B'(x'))$.  Another way to
state the second assumption is that there is a fiberwise equivalence $g:
\prd{x:A} B(x) \eqvsym B'(f(x))$.

\item[$\to$] If $A \eqvsym A'$ and $B \eqvsym B'$, then $(A \to B) \eqvsym (A'
\to B')$.

\item[$\Pi$] If $f : A \eqvsym A'$ and there is a fiberwise equivalence $g :
\prd{x:A}B(x) \eqvsym B'(f(x))$, then 
\[
  \left(\prd{x:A} B(x)\right) \eqvsym \left(\prd{x':A'} B'(f(x'))\right)
\]

\item[$+$] If $A \eqvsym A'$ and $B \eqvsym B'$, then $A + B \eqvsym A' + B'$.
\end{description}%
*)

Definition sigma_f `{Univalence} {A A' : Type} {B : A -> Type} {B' : A' -> Type} 
        (f : A <~> A') (g : forall x : A, B x <~> B' (f x)) :
  {x : A & B x} -> {x' : A' & B' x'}.
Proof.
  intros. exists (f X.1). apply (g X.1 X.2).
Defined.

Definition sigma_f_inv `{Univalence} {A A' : Type} {B : A -> Type} {B' : A' -> Type} 
    (f : A <~> A') (g : forall x : A, B x <~> B' (f x)) (X : {x' : A' & B' x'}) 
    := 
    (f^-1 X.1; (g (f^-1 X.1))^-1 ((eisretr f X.1)^ # X.2)).

Theorem ex2_17_sigma `{Univalence} (A A' : Type) (B : A -> Type) (B' : A' -> Type) 
        (f : A <~> A') (g : forall x : A, B x <~> B' (f x)) :
  {x : A & B x} <~> {x' : A' & B' x'}.
Proof.
  intros. 
  refine (equiv_adjointify (sigma_f f g) (sigma_f_inv f g) _ _); intro h; 
  unfold sigma_f, sigma_f_inv; simpl; apply path_sigma_uncurried; simpl.
  exists (eisretr f h.1). simpl. 
  rewrite (eisretr (g (f^-1 h.1))). rewrite transport_pV. reflexivity.
  exists (eissect f h.1).
  refine ((ap_transport (eissect f h.1) (fun x' => (g x') ^-1)
                        (transport B' (eisretr f (f h.1)) ^ (g h.1 h.2)))^ @ _).
  rewrite transport_compose, eisadj, transport_pV. apply eissect.
Defined.
  

Theorem ex2_17_maps `{Univalence} : forall (A A' B B' : Type),
  A <~> A' -> B <~> B' -> (A -> B) <~> (A' -> B').
Proof.
  intros A A' B B' HA HB.
  apply equiv_path_universe in HA.
  apply equiv_path_universe in HB.
  apply equiv_path_universe.
  rewrite HA, HB. reflexivity.
Defined.


Definition pi_f {A A' : Type} {B : A -> Type} {B' : A' -> Type}
        (f : A <~> A') (g : forall x : A, B x <~> B' (f x)) :
  (forall x:A, B x) -> (forall x':A', B' x').
  intros.
  apply ((eisretr f x') # ((g (f^-1 x')) (X (f^-1 x')))).
Defined.
  
Definition pi_f_inv {A A' : Type} {B : A -> Type} {B' : A' -> Type}
           (f : A <~> A') (g : forall x : A, B x <~> B' (f x)) :
  (forall x':A', B' x') -> (forall x:A, B x).
  intros.
  apply (g x)^-1. apply (X (f x)).
Defined.

Theorem ex2_17_pi `{Funext} {A A' : Type} {B : A -> Type} {B' : A' -> Type}
           (f : A <~> A') (g : forall x : A, B x <~> B' (f x)) :
  (forall x:A, B x) <~> (forall x':A', B' x').
Proof.
  refine (equiv_adjointify (pi_f f g) (pi_f_inv f g) _ _); intro h;
  unfold pi_f, pi_f_inv.
  apply path_forall; intro x'.
  rewrite (eisretr (g (f^-1 x'))). induction (eisretr f x'). reflexivity.
  apply path_forall; intro x.
  apply (ap (g x))^-1. rewrite (eisretr (g x)).
  rewrite eisadj. rewrite <- transport_compose.
  induction (eissect f x). reflexivity.
Qed.


Theorem ex2_17_sum `{Univalence} : forall (A A' B B' : Type), 
  A <~> A' -> B <~> B' -> (A + B) <~> (A' + B').
Proof.
  intros A A' B B' HA HB.
  apply equiv_path_universe in HA.
  apply equiv_path_universe in HB.
  apply equiv_path_universe.
  rewrite HA, HB. reflexivity.
Qed.

End Ex17.
