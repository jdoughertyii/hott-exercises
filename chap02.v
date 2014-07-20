(* begin hide *)
Require Import HoTT.
(* end hide *)

(** printing <~> %\ensuremath{\eqvsym}% *)
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
Show that the three equalities of proofs constructed in the previous exercise form a commutative triangle.  In other words, if the three definitions of concatenation are denoted by $(p \ctu q)$, $(p \ctd q)$, and $(p \ctt q)$, then the concatenated equality
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
Let $x, y : A$ and $p : x = y$.  Rather than fixing some $q$ and constructing an element of $x = z$ out of that, we can directly construct an element of
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

(** To prove that it's equal to the others, we can just show that it's equal to $\ct$ and then use concatenation.  Again by induction on $p$ and $q$, it suffices to consider the case where $y$ and $z$ are $x$ and $p$ and $q$ are $\refl{x}$.  Then we have
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


(** %\exerdone{2.4}{103}% 
Define, by induction on $n$, a general notion of $n$-dimensional path
in a type $A$, simultaneously with the type of boundaries for such paths. *)

(** %\soln%
A $0$-path in $A$ is an element $x : A$, so the type of $0$-paths is just $A$.
If $p$ and $q$ are $n$-paths, then so is $p = q$.  In the other
direction, the boundary of a $0$-path is empty, and the boundary of an
$n+1$ path is an $n$-path.
*)

Fixpoint npath (A:Type) (n:nat) : Type :=
  match n with
    | O => A
    | S n' => {p : (boundary A n') & {q : (boundary A n') & p = q}}
  end

with boundary (A:Type) (n:nat) : Type :=
  match n with
    | O => Empty
    | S n' => (npath A n')
  end.


(** %\exerdone{2.5}{103}% 
Prove that the functions
%\begin{align*}
 (f(x) = f(y)) &\to (p_{*}(f(x)) = f(y)) \qquad\qquad\text{and} \\
 (p_{*}(f(x)) = f(y)) &\to (f(x) = f(y))
\end{align*}%
are inverse equivalences. *)

(** %\soln% 
I take it that ``inverse equivalences'' means that each of the maps is the
quasi-inverse of the other.  Suppose that $x, y : A$, $p : x = y$, and $f : A
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

Definition alpha2_5 : forall {A B:Type} {x y : A} (f: A -> B) (p:x=y) q, 
  (eq2_3_6 f p (eq2_3_7 f p q)) = q. 
  unfold eq2_3_6, eq2_3_7. path_induction. reflexivity.
Defined.

Definition beta2_5 : forall {A B:Type} {x y : A} (f: A -> B) (p:x=y) q, 
  (eq2_3_7 f p (eq2_3_6 f p q)) = q. 
  unfold eq2_3_6, eq2_3_7. path_induction. reflexivity.
Defined.

Lemma isequiv_transportconst (A B:Type) (x y z : A) (f : A -> B) (p : x = y) : 
  IsEquiv (eq2_3_6 f p).
Proof.
  apply (isequiv_adjointify _ (eq2_3_7 f p) (alpha2_5 f p) (beta2_5 f p)).
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

Definition alpha2_6 {A:Type} {x y z:A} (p:x=y) (q:x=z) : p @ (p^ @ q) = q.
  path_induction. reflexivity.
Defined.

Definition beta2_6 {A:Type} {x y z:A} (p:x=y) (q:y=z) : p^ @ (p @ q) = q.
  path_induction. reflexivity.
Defined.

Lemma isequiv_eqcat (A:Type) (x y z : A) (p : x = y) : IsEquiv (fun q:(y=z) => p @ q).
Proof.
  apply (isequiv_adjointify _ (fun q:(x=z) => p^ @ q) (alpha2_6 p) (beta2_6 p)).
Qed.

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
  \left[(g(\refl{a}))_{*}(h(a, b)) = h(a', b')\right]
  \equiv
  \left[h(a, b) = h(a', b')\right]
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

Coq takes of a bit of coaxing to get the types right.
*)

Definition T {A A' : Type} {B : A -> Type} {B' : A' -> Type}
           {g : A -> A'} (h : forall a, B a -> B' (g a))
           {x y : {a:A & B a}}
           (p : x.1 = y.1) (q : p # x.2 = y.2)
  : (ap g p) # (h x.1 x.2) = h y.1 y.2.
  transitivity (h y.1 (p # x.2));
  destruct x; destruct y; simpl in *; induction p; [|rewrite q]; reflexivity.
Defined.

Theorem ex2_7 : forall {A A' : Type} {B : A -> Type} {B' : A' -> Type}
                       (g : A -> A') (h : forall a, B a -> B' (g a))
                       (x y : {a:A & B a})
                       (p : x.1 = y.1) (q : p # x.2 = y.2),
let f z := (g z.1; h z.1 z.2) in
  ap f (path_sigma B x y p q) = path_sigma B' (f x) (f y) (ap g p) (T h p q). 
intros. unfold f, T. 
destruct x. destruct y. simpl in *. induction p.  rewrite <- q. reflexivity.
Defined.



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

Since these are all the cases, we've proven the analogue to Theorem 2.6.5 for
coproducts (though it was stated rather implicitly).  I'll have to state it
more explicitly in Coq, though the proof is verbatim the same as the one by
hand.
*)

Definition code {A B : Type} (x : A + B) (y : A + B) :=
  match x with
  | inl a => match y with 
             | inl a' => (a = a')
             | inr b => Empty
             end
  | inr b => match y with
             | inl a => Empty
             | inr b' => (b = b')
             end
  end.
                     
Theorem ex2_8 : forall (A A' B B' : Type)
                       (g : A -> A') (h : B -> B')
                       (x y : A+B) (p : code x y),
  let f z := match z with
             | inl a => inl (g a)
             | inr b => inr (h b)
             end 
  in 
  ap f (path_sum x y p) = path_sum (f x) (f y) (
        (match x return code x y -> code (f x) (f y) with
         | inl a => match y return code (inl a) y -> code (inl (g a)) (f y) with
                    | inl a' => ap g
                    | inr b => idmap
                    end
         | inr b => match y return code (inr b) y -> code (inr (h b)) (f y) with
                    | inl a => idmap
                    | inr b' => ap h
                    end
         end) p).
Proof.
  intros. destruct x; destruct y; simpl in *; 
    try (path_induction; reflexivity);
    try (destruct p).
Qed.

     
(** %\exer{2.9}{104}% 
Prove that coproducts have the expected universal property,
%\[
  (A + B \to X) \eqvsym (A \to X) \times (B \to X).
\]%
Can you generalize this to an equivalence involving dependent functions?
*)

(** %\soln%
To define the forward map, let $h : A+B \to X$ and define $f : (A+B\to X) \to
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

Definition forward {A B X : Type} (h : (A+B -> X)) : (A->X) * (B->X) :=
  (h o inl, h o inr).

Definition backward {A B X : Type} (h : (A->X) * (B->X)) : A+B -> X :=
  fun x => match x with
             | inl a => (fst h) a
             | inr b => (snd h) b
           end.

Lemma alpha2_9 {A B X: Type} : forall (h : (A -> X) * (B -> X)), 
  forward (backward h) = h.
Proof.
  unfold forward, backward. destruct h as (x, y). reflexivity.
Qed.

Lemma beta2_9 `{Funext} {A B X: Type} : forall (h : A+B -> X), 
  backward (forward h) = h.
Proof.
  intros. apply H. unfold pointwise_paths. intros. destruct x; reflexivity.
Qed.

Theorem ex2_9 : forall A B X, IsEquiv(@forward A B X).
Proof.
  intros. apply (isequiv_adjointify forward backward alpha2_9 beta2_9).
Qed.
          
     
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

Definition ex2_10_f {A : Type} {B : A -> Type} {C : {x:A & B x} -> Type} : 
  {x:A & {y : B x & C (x; y)}} -> {p : {x:A & B x} & C p}.
  intro abc. destruct abc as [a [b c]]. apply ((a; b); c).
Defined.

Definition ex2_10_g {A : Type} {B : A -> Type} {C : {x:A & B x} -> Type} : 
  {p : {x:A & B x} & C p} -> {x:A & {y : B x & C (x; y)}}.
  intro abc. destruct abc as [[a b] c].
  exists a; exists b; apply c.
Defined.

Theorem ex2_10 : forall A B C, IsEquiv(@ex2_10_f A B C).
Proof.
  intros. 
  refine (isequiv_adjointify ex2_10_f ex2_10_g _ _);
  unfold ex2_10_f, ex2_10_g; intro abc; 
  [ destruct abc as [[a b] c] | destruct abc as [a [b c]]];
  reflexivity.
Qed.

(** %\exer{2.11}{104}% 
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
  (X \to P) \to (X \to A) \times_{(X \to C)} (X \to B)
\]%
is an equivalence.  Prove that the pullback $P \defeq A \times_{C} B$ defined
in 2.15.11 is the corner of a pullback square.
*)

(** %\soln%
To show that $P$ is the corner of a pullback square, we need to produce 
*)

(** %\exer{2.12}{104}% 
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
The good ol' pullback lemma.
*)

(** %\exer{2.13}{104}% 
Show that $(\bool \eqvsym \bool) \eqvsym \bool$.
*)

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

(** %\exer{2.15}{105}%
Show that Lemma 2.10.5 can be strengthened to
%\[
  \transfib{B}{p}{-} =_{B(x)\to B(y)} \idtoeqv(\mapfunc{B}(p))
\]%
without using function extensionality.
*)

(** %\exer{2.16}{105}%
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
    : \prd{x:A}B(x)$.  We need to construct a quasi-inverse for
the function
%\[
  \happly : (f = g) \to (f \sim g)
\]%
and this is given by $\funext$.  Suppose that $p : f = g$; then we can show
$\funext(\happly(p)) = p$.  By induction, we can assume that $p$ is $\refl{f}$.
Then by definition,
$\happly(\refl{f}) \equiv \lam{x}\refl{f(x)} : \prd{x:A} f(x) = f(x)$. 
*)

(** %\exer{2.17}{105}%
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
B'$, so again by univalence $(A \times B) \eqvsym (A' \times B')$. *)

Theorem ex2_17_i `{Univalence}: forall (A A' B B' : Type),
  A <~> A' -> B <~> B' -> (A * B) <~> (A' * B').
Proof.
  intros A A' B B' HA HB. 
  apply equiv_path_universe in HA.
  apply equiv_path_universe in HB.
  apply equiv_path_universe.
  rewrite HA, HB. reflexivity.
Defined.

(**
%\noindent%
(ii)  To prove this without univalence

%\noindent%
(iii)
*)

Theorem ex2_17_maps `{Univalence}: forall (A A' B B' : Type),
  A <~> A' -> B <~> B' -> (A -> B) <~> (A' -> B').
Proof.
  intros A A' B B' HA HB.
  apply equiv_path_universe in HA.
  apply equiv_path_universe in HB.
  apply equiv_path_universe.
  rewrite HA, HB. reflexivity.
Qed.

Theorem ex2_17_sum `{Univalence}: forall (A A' B B' : Type), 
  A <~> A' -> B <~> B' -> (A + B) <~> (A' + B').
Proof.
  intros A A' B B' HA HB.
  apply equiv_path_universe in HA.
  apply equiv_path_universe in HB.
  apply equiv_path_universe.
  rewrite HA, HB. reflexivity.
Qed.
