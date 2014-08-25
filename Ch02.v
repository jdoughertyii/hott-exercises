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
more explicitly in Coq, though the proof is the same as the one by
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

Definition ex2_9_f {A B X : Type} (h : (A + B -> X)) : (A->X) * (B->X) :=
  (h o inl, h o inr).

Definition ex2_9_g {A B X : Type} (h : (A->X) * (B->X)) : A + B -> X :=
  fun x => match x with
             | inl a => (fst h) a
             | inr b => (snd h) b
           end.

Lemma alpha2_9 {A B X: Type} : forall (h : (A -> X) * (B -> X)), 
  ex2_9_f (ex2_9_g h) = h.
Proof.
  unfold ex2_9_f, ex2_9_g. destruct h as (x, y). reflexivity.
Qed.

Lemma beta2_9 `{Funext} {A B X: Type} : forall (h : A + B -> X), 
  ex2_9_g (ex2_9_f h) = h.
Proof.
  intros. apply H. unfold pointwise_paths. intros. destruct x; reflexivity.
Qed.

Theorem ex2_9 : forall A B X, (A + B->X) <~> (A->X) * (B->X).
Proof.
  intros. apply (equiv_adjointify ex2_9_f ex2_9_g alpha2_9 beta2_9).
Qed.

(** All of this generalizes directly to the case of dependent functions. *)


Definition ex2_9_f' {A B : Type} {C: A + B -> Type} (h : forall (p:A + B), C p) 
  : (forall a:A, C(inl a)) * (forall b:B, C(inr b)) :=
(fun _ => h (inl _), fun _ => h (inr _)).

Definition ex2_9_g' {A B : Type} {C: A + B -> Type} 
           (h : (forall a:A, C(inl a)) * (forall b:B, C(inr b))) : 
  forall (p:A + B), C p :=
 fun _ => match _ as s return (C s) with
            | inl a => fst h a
            | inr b => snd h b
          end.

Theorem ex2_9' : forall A B C, 
  (forall (p:A + B), C(p)) <~> (forall a:A, C(inl a)) * (forall b:B, C(inr b)).
Proof.
  intros. 
  refine (equiv_adjointify ex2_9_f' ex2_9_g' _ _); unfold ex2_9_f', ex2_9_g'.
  intro. destruct x. apply path_prod; simpl;
  apply path_forall; unfold pointwise_paths; reflexivity.
  intro. apply path_forall; intro p. destruct p; reflexivity.
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

Section Exercise2_11.

Variables (A B C X : Type) (f: A -> C) (g: B -> C). 

Definition P := {a:A & {b:B & f a = g b}}.
Definition funpull := {h:X->A & {k:X->B & f o h = g o k}}.

Definition pi1 (p : P) : A := p.1.
Definition pi2 (p : P) : B := p.2.1.


Definition ex2_11_f `{Funext} : (X -> P) -> funpull.
  intro h.
  refine (pi1 o h; (pi2 o h; _)).
  apply path_forall; intro.
  exact (h x).2.2.
Defined.

Definition ex2_11_g : funpull -> (X -> P).
  intros h x.
  refine (h.1 x; (h.2.1 x; _)).
  exact (apD10 h.2.2 x).
Defined.

Theorem ex2_11 `{Funext} : (X -> P) <~> funpull.
  refine (equiv_adjointify ex2_11_f ex2_11_g _ _).

  (* alpha *)
  unfold Sect, ex2_11_g, ex2_11_f, path_forall; simpl. 
  destruct 0 as [f' [g' p]]; simpl. f_ap. f_ap.
  apply (ap apD10)^-1.
  apply eisretr.

  (* beta *)
  unfold Sect, ex2_11_g, ex2_11_f, path_forall; intro h; simpl.
  apply path_forall; intro x.
  repeat (apply path_sigma_uncurried; exists idpath; simpl).
  change (h x).2.2 with ((fun x' => (h x').2.2) x); f_ap. 
  apply eisretr.
Qed.

End Exercise2_11.

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
The good ol' pullback lemma---though since we've defined pullbacks in terms of
equalizers, it's not the usual proof.  Let the arrows in the diagram be labeled
$dc$, where $d$ is the domain and $c$ the codomain.  Since the diagram
commutes, we have the equalities $r : ef \circ ce = df \circ cd$, 
$\ell : cd \circ ac = bd \circ ab$, and $e : ef \circ ce \circ ac = df \circ bd
\circ ab$.  Since the right hand square is a pullback, we have the equivalence
%\[
  f : (X \to C) \eqvsym (X \to D) \times_{X \to F} (X \to E)
\]%
This equivalence allows us to express the universal property of the pulback in
a slightly more familiar way.  Suppose that $k : (X \to D) \times_{X \to F}
(X \to E)$.  Then we have
%\begin{align*}
  cd \circ f^{-1}(k) &= \proj{3}^{1}(f(f^{-1}(k))) = \proj{3}^{1}(k) \\
  ce \circ f^{-1}(k) &= \proj{3}^{2}(f(f^{-1}(k))) = \proj{3}^{2}(k)
\end{align*}%

Now for the pullback lemma, relating the obvious maps
%\begin{align*}
  g &: (X \to A) \to (X \to B) \times_{X \to D} (X \to C) \\
  h &: (X \to A) \to (X \to B) \times_{X \to F} (X \to E)
\end{align*}%
We want to show that $g$ is an equivalence iff $h$ is.

Suppose that $k : (X \to B) \times_{X \to D} (X \to C)$.  Since
$\proj{3}^{3}(k) : bd \circ \proj{3}^{1}(k) = cd \circ \proj{3}^{2}(k)$, we
have
%\[
  E(\proj{3}^{3}(k))
  :
  df \circ bd \circ \proj{3}^{1}(k) 
  = df \circ cd \circ \proj{3}^{2}(k)
  = ef \circ ce \circ \proj{3}^{2}(k)
\]%
where the first equality results from $\proj{3}^{3}(k)$ and the second from the
commutative diagram.  So define
%\[
  \phi : k \mapsto (\proj{3}^{1}(k), ce \circ \proj{3}^{2}(k),
  E(\proj{3}^{3}(k)))
\]%
We want to show that this is an equivalence.  For a quasi-inverse, consider
$k' : (X \to B) \times_{X \to F} (X \to E)$.  Then 
%\[
    \tilde{k}'
    \defeq
    (bd \circ \proj{3}^{1}(k'), \proj{3}^{2}(k'), \proj{3}^{3}(k'))
    :
    (X \to D) \times_{X \to F} (X \to E)
\]%
so $f^{-1}(\tilde{k}') : X \to C$.  Thus, if we can construct some
%\[
  q : bd \circ \proj{3}^{1}(k') = cd \circ f^{-1}(\tilde{k}')
\]%
then we will have a candidate for $\phi^{-1}$.  Using the universal property of
$f$, we have
%\[
  cd \circ f^{-1}(\tilde{k}')
  = \proj{3}^{1}(\tilde{k}')
  = bd \circ \proj{3}^{1}(k')
\]%
which is the required equality, meaning that we have our backward map,
%\[
  \phi^{-1} : k' \mapsto (\proj{3}^{1}(k'), f^{-1}(\tilde{k}'), E'(\proj{3}^{3}(k')))
\]%

Now to show that these are quasi-inverses.  Ignore the equality for now.
If $k : (X \to B) \times_{X\to D} (X \to C)$, then applying $\phi^{-1} \circ
\phi$ gives
%\[
  \left(
    \proj{3}^{1}(k),
    f^{-1}(bd \circ \proj{3}^{1}(k),
           ce \circ \proj{3}^{2}(k),
           E(\proj{3}^{3}(k))),
    E'(E(\proj{3}^{3}(k)))
  \right)
\]%
By function extensionality, this is equal to the identity if the second slot is
equal to $\proj{3}^{2}(k)$ and the third slot to $\proj{3}^{3}(k)$.  We have
%\[
  f(k) = (cd \circ \proj{3}^{1}(k), ce \circ \proj{3}^{2}(k), E(\proj{3}^{3}(k)))
\]%
by the definition of $f$, so the second slot agrees.

To go the other way, suppose that $k' : (X \to B) \times_{X\to F} (X \to E)$.
Then applying $\phi \circ \phi^{-1}$ gives
%\[
  \left(
    \proj{3}^{1}(k'),
    ce \circ f^{-1}(bd \circ \proj{3}^{1}(k'), \proj{3}^{2}(k'), \proj{3}^{3}(k)),
    E(E'(\proj{3}^{3}(k')))
  \right)
\]%
and the universal property of $f$ makes it obvious that the first two slots are
what we need by function extensionality.

I am too lazy to work out the equalities by hand right now.  Since $E$ and $E'$
are both constructed out of function applications and concatenations, and both
of these are functorial, induction on $\proj{3}^{3}(k)$ is going to make
everything reduce to reflexivities.

At this point we have shown that
%\[
  (X \to B) \times_{X \to D} (X \to C)
  \eqvsym
  (X \to B) \times_{X \to F} (X \to E)
\]%
Since equivalence is an equivalence relation, this means that $g$ is an
equivalence iff $h$ is an equivalence, which is what was to be proved.
*)

Section Exercise2_12.

Variables (A B C D E F X : Type) (ab:A->B) (ac:A->C) (bd:B->D)
          (cd:C->D) (ce:C->E) (df:D->F) (ef:E->F)
          (l: bd o ab = cd o ac) (r: df o cd = ef o ce).

Definition e : df o bd o ab = ef o ce o ac.
  transitivity (df o cd o ac).
  apply (ap (compose df) l).
  apply (ap (fun (f: C -> F) => f o ac) r).
Defined.

Definition f (k : X->C) : pullback (@compose X _ _ df) (@compose X _ _ ef) :=
  (cd o k; (ce o k; ap10 (ap compose r) k)).

Hypothesis right_pullback : IsEquiv(f).

Lemma comp_cd_is_pr1 : forall (k : pullback (@compose X _ _ df) 
                                              (@compose X _ _ ef)),
                           cd o f^-1 k = k.1.
Proof.
  intros.
  change (cd o f^-1 k) with (f (f^-1 k)).1.
  apply (ap pr1 (eisretr f k)).
Defined.

Lemma comp_ce_is_pr2 : forall (k : pullback (@compose X _ _ df) 
                                              (@compose X _ _ ef)),
                           ce o f^-1 k = k.2.1.
Proof.
  intros.
  change (ce o f^-1 k) with (f (f^-1 k)).2.1.
  apply (ap ((fun (k : pullback (@compose X _ _ df) (@compose X _ _ ef))
                   => k.2.1))
             (@eisretr (X -> C) 
                       (pullback (@compose X _ _ df) (@compose X _ _ ef))
                       f 
                       right_pullback
                       k)).
Defined.

Definition phi (k: pullback (@compose X _ _ bd) (@compose X _ _ cd))
: pullback (@compose X _ _ (df o bd)) (@compose X _ _ ef) :=
  (k.1; (ce o k.2.1; (ap (compose df) k.2.2) @ (ap10 (ap compose r) k.2.1))).

Definition phi_inv (k: pullback (@compose X _ _ (df o bd)) (@compose X _ _ ef))
: pullback (@compose X _ _ bd) (@compose X _ _ cd) :=
  (k.1; (f^-1 (bd o k.1; k.2); (base_path (eisretr f (bd o k.1; k.2)))^)).

Lemma ex2_12_alpha : forall k, phi (phi_inv k) = k.
Proof.
  unfold phi, phi_inv. intro k.
  apply path_sigma_uncurried. exists 1. simpl.
  apply path_sigma_uncurried. simpl. exists (comp_ce_is_pr2 (bd o k.1; k.2)).
  unfold comp_ce_is_pr2.
  rewrite trans_paths. rewrite ap_const. simpl. rewrite concat_1p.
  rewrite <- ap_apply_Fl.
Admitted.


Lemma ex2_12_beta : forall k, phi_inv (phi k) = k.
Proof.
  intro k. unfold phi_inv, phi. simpl.
  apply path_sigma_uncurried. exists 1. simpl.
  apply path_sigma_uncurried. simpl.
  assert (f^-1 (bd o k .1; 
                (ce o k.2.1; 
                 ap (compose df) k.2.2 @ ap10 (ap compose r) k.2.1)) 
          = k.2.1).
Admitted.
  
  
  
   

Theorem ex2_12_helper : 
  pullback (@compose X _ _ bd) (@compose X _ _ cd)
  <~> pullback (@compose X _ _ (df o bd)) (@compose X _ _ ef).
Proof.
  apply (equiv_adjointify phi phi_inv ex2_12_alpha ex2_12_beta).
Defined.
  
Theorem ex2_12 : 
  (X -> A) <~> pullback (@compose X _ _ bd) (@compose X _ _ cd)
  <->
  (X -> A) <~> pullback (@compose X _ _ (df o bd)) (@compose X _ _ ef).
Proof.
  split. 

  intros. 
  apply (@equiv_compose' _ (pullback (@compose X _ _ bd) (@compose X _ _ cd))).
  apply ex2_12_helper. apply X0.

  intros.
  apply (@equiv_compose' _ (pullback (@compose X _ _ (df o bd))
                                     (@compose X _ _ ef))).
  apply (equiv_inverse ex2_12_helper). apply X0.
Defined.
  

  
End Exercise2_12.


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

Lemma id_isequiv : Bool <~> Bool.
Proof.
  refine (equiv_adjointify idmap idmap (fun _ => 1) (fun _ => 1)).
Defined.

Lemma negb_isequiv : Bool <~> Bool.
Proof.
  refine (equiv_adjointify negb negb _ _);
  intro; destruct x; reflexivity.
Defined.

Definition ex2_13_f (x : Bool <~> Bool) : Bool := x false.

Definition ex2_13_g (b : Bool) : (Bool <~> Bool) :=
  if b
  then {| equiv_fun := negb |}
  else {| equiv_fun := idmap |}.
  

Lemma equiv_not_const (f : Bool -> Bool) `{IsEquiv Bool Bool f} : 
  f false = negb (f true).
Proof.
  pose proof (eissect f true) as H1.
  pose proof (eissect f false) as H2.
  destruct (f true), (f false);
  try (etransitivity; try (eassumption || (symmetry; eassumption)));
  try (simpl; reflexivity).
Defined.

Theorem negb_involutive : forall b, negb (negb b) = b.
Proof. destruct b; reflexivity. Qed.

Theorem ex2_13 `{Funext} : (Bool <~> Bool) <~> Bool.
Proof.
  refine (equiv_adjointify ex2_13_f ex2_13_g _ _);
  unfold Sect, ex2_13_f, ex2_13_g.

  (* alpha *)
  destruct x; reflexivity.
  
  (* beta *)
  destruct x. pose proof (equiv_not_const equiv_fun) as H1.
  apply path_equiv; apply path_forall; destruct x; simpl.
  destruct (equiv_fun false); simpl;
    repeat (transitivity (negb (negb (equiv_fun true)));
      [rewrite <- H1; reflexivity | apply negb_involutive]).
  destruct (equiv_fun false); reflexivity.
Qed.                                 
  
  
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
equivalence for all $g$, proving the result.  Fingers crossed that none of the
HoTT library lemmas I use depend on [Funext] or [Univalence].
*)

Section Exercise2_16.

Variable funext : forall (A : Type) (B : A -> Type) (f g : forall (x:A), B x),
                      (f == g) -> (f = g).

Definition funext' {A : Type} {B : A -> Type} (f g : forall (x:A), B x) : 
  (f==g) -> (f=g) :=
  (fun h : (f==g) => (funext A B f g h) @ (funext A B g g (fun _ => 1))^).

Lemma funext'_computes {A : Type} {B : A -> Type} (f : forall (x:A), B x) : 
  funext' f f (fun _ => 1) = 1.
Proof.
  unfold funext'. rewrite concat_pV. reflexivity.
Defined.

Definition isContr (X:Type) := {a : X & forall (x:X), a = x}.

Lemma Lemma3118 {C} : forall (c:C), isContr {x:C & c = x}.
Proof.
  intro c. exists (c; 1).
  intro x. destruct x as [x p]. path_induction. reflexivity.
Defined.

Lemma Lemma3116 A B f : isContr (forall x:A, {y : B x & f x = y}).
Proof.
  exists (fun x:A => (f x; 1)).
  intro k. apply (funext' (fun x => (f x; 1)) k); intro x.
  assert (isContr {y : B x & f x = y}). apply Lemma3118.
  destruct X. destruct x0. rewrite <- (p (k x)).
  apply path_sigma_uncurried. exists p0.
  induction p0. reflexivity.
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

Lemma contr_equiv_commute {A B} : A <~> B -> isContr A -> isContr B.
Proof.
  intros f k. unfold isContr in *.
  exists (f k.1). intro x. transitivity (f (f^-1 x)).
  apply (ap f). apply (k.2 (f^-1 x)).
  apply eisretr.
Defined.

Lemma reduce_to_refl {A B f} : isContr {g : forall x:A, B x & f == g}.
Proof.
  apply (@contr_equiv_commute (forall (x:A), {y : B x & f x = y})).
  refine (BuildEquiv _ _ choice Theorem2157).
  apply Lemma3116.
Defined.
  
Definition total_happly {A B f} : 
  {g : forall x:A, B x & f = g} -> {g : forall x:A, B x & f == g}.
  intros. destruct X. exists x. apply apD10. apply p.
Defined.

Definition total_happly_inv {A B f} : 
  {g : forall x:A, B x & f == g} -> {g : forall x:A, B x & f = g}.
  intros. destruct X. exists x. apply funext'. apply p.
Defined.

Lemma total_equivalence {A B f} : IsEquiv(@total_happly A B f).
Proof.
  refine (isequiv_adjointify total_happly total_happly_inv _ _); intro k.
  - assert (isContr {g : forall x:A, B x & f == g}). apply reduce_to_refl.
    destruct X. rewrite (p k)^. apply (p (total_happly (total_happly_inv x)))^.
  - assert (isContr {g : forall x:A, B x & f = g}). apply Lemma3118.
    destruct X. rewrite (p k)^. apply (p (total_happly_inv (total_happly x)))^.
Defined.

Definition total {A P Q} (f : forall (x:A), P x -> Q x) := fun w => (w.1; f w.1 w.2).

Lemma total_happly_is {A B f} : (@total_happly A B f) = total (@apD10 A B f).
Proof.
  unfold total_happly. 
  apply funext'; intro. 
  destruct x. 
  reflexivity.
Qed.

Definition fx_inv {A P Q} {f : forall x:A, P x -> Q x} {k : IsEquiv (total f)} 
           (x : A) (y : Q x) : P x. 
  destruct k.
  change x with (x; y).1.
  apply (transport _ (base_path (eisretr (x; y)))).
  apply (equiv_inv (x; y)).2.
Defined.

Lemma Theorem477 (A : Type) (P Q : A -> Type) (f : forall x:A, P x -> Q x) : 
  IsEquiv (total f) -> forall x:A, IsEquiv (f x).
Proof.
  intros.
  refine (isequiv_adjointify (f x) (fx_inv x) _ _); unfold fx_inv; intro y.
  - destruct X.
    rewrite ap_transport. simpl. unfold base_path. 
    apply (fiber_path (eisretr (x; y))).
  - destruct X. unfold base_path.
    change (x; f x y) with ((total f) (x; y)).
    rewrite eisadj. rewrite <- ap_compose.
    assert ((ap (pr1 o total f) (eissect (x; y))) = (base_path (eissect (x; y)))).
    unfold compose. unfold base_path. reflexivity.
    rewrite X. unfold base_path. simpl.
    transitivity (x; y).2.
    apply (fiber_path (eissect (x; y))).
    reflexivity.
Defined.
     
   

Theorem ex2_16 {A B} (f g : forall (x:A), B x) : IsEquiv(@apD10 A B f g).
Proof.
  apply Theorem477.
  rewrite <- total_happly_is.
  apply total_equivalence.
Qed.
  
End Exercise2_16.

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

Theorem ex2_17_i `{Univalence}: forall (A A' B B' : Type),
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

Theorem ex2_17_i' : forall (A A' B B' : Type),
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

Theorem equal_proofs `{Univalence} : ex2_17_i = ex2_17_i'.
Proof.
  unfold ex2_17_i, ex2_17_i'. simpl. unfold compose.
  apply path_forall; intro A.  apply path_forall; intro A'.
  apply path_forall; intro B.  apply path_forall; intro B'.
  apply path_forall; intro f.  apply path_forall; intro g.
  
  (* equiv_fun *)
  assert (transport idmap
                  (transport (fun x : Type => A * B = A' * x)
                     (path_universe_uncurried g)
                     (transport (fun x : Type => A * B = x * B)
                        (path_universe_uncurried f) 1))
          =
         fun z : A * B => (f (fst z), g (snd z))) as H1.
  apply path_forall; intro z. 
  repeat (rewrite trans_paths; hott_simpl).
  rewrite transport_pp. 
  rewrite <- transport_idmap_ap.
  rewrite <- (transport_idmap_ap Type (fun a:Type => a * B) A A' (path_universe_uncurried f) z).
  rewrite (@transport_prod Type idmap (fun x:Type => B)).
  rewrite transport_prod. simpl.
  destruct z; apply path_prod; simpl.
    rewrite transport_const.
    assert ((path_universe_uncurried f) = (path_universe (equiv_fun A A' f))).
    unfold path_universe. destruct f. reflexivity.
    rewrite X. apply transport_path_universe.
    rewrite transport_const.
    assert ((path_universe_uncurried g) = (path_universe (equiv_fun B B' g))).
    unfold path_universe. destruct g. reflexivity.
    rewrite X. apply transport_path_universe.

 unfold equiv_path, equiv_adjointify. 
 
 (* Lemma 3.5.1 *)
 apply path_equiv. apply H1.
Qed.
  
  

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

Theorem ex2_17_pi {A A' : Type} {B : A -> Type} {B' : A' -> Type}
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
