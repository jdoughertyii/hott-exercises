(** 
%\part{Foundations}%
%\section*{Introduction}%


The following are solutions to exercises from
_Homotopy Type Theory: Univalent Foundations of Mathematics_.  The Coq
code given alongside the by-hand solutions requires the HoTT version of Coq,
available %\href{https://github.com/HoTT}{at the HoTT github repository}%.  
*)


Require Export HoTT.


(**
%\tableofcontents%


* Type Theory *)


(** %\exerdone{1.1}{56}%  
Given functions $f:A\to B$ and $g:B\to C$, define their composite $g
\circ f : A \to C$.  Show that we have $h \circ (g \circ f) \equiv (h
    \circ g) \circ f$.


%\soln%
Define $g \circ f \defeq \lam{x:A}g(f(x))$.  Then if $h:C \to D$, we
have
%\[
h \circ (g \circ f) 
\equiv \lam{x:A}h((g \circ f)x)
\equiv \lam{x:A}h((\lam{y:A}g(fy))x)
\equiv \lam{x:A}h(g(fx))
\]%
and
%\[
(h \circ g) \circ f 
\equiv \lam{x:A}(h \circ g)(fx)
\equiv \lam{x:A}(\lam{y:B}h(gy))(fx)
\equiv \lam{x:A}h(g(fx))
\]%
So $h \circ (g \circ f) \equiv (h \circ g) \circ f$.  In Coq, we have *)


Module Ex1.

Definition compose {A B C : Type} (g : B -> C) (f : A -> B) := fun x => g (f x).

Lemma compose_assoc (A B C D : Type) (f : A -> B) (g : B-> C) (h : C -> D)
  : compose h (compose g f) = compose (compose h g) f.
Proof.
  reflexivity.
Defined.
  
End Ex1.

(** %\exerdone{1.2}{56}%  
Derive the recursion principle for products $\rec{A \times B}$ using only the
    projections, and verify that the definitional equalities are valid.  Do the
    same for $\Sigma$-types.  *)


(** %\soln% 
The recursion principle states that we can define a function $f : A \times B
\to C$ by giving its value on pairs.  Suppose that we have projection functions
$\fst : A \times B \to A$ and $\snd : A \times B \to B$.  Then we can define a
function of type
%\[
  \rec{A\times B}' : \prd{C : \UU} (A \to B \to C) \to A \times B \to C
\]%
in terms of these projections as follows
%\[
  \rec{A \times B}'(C, g, p) \defeq g(\fst p)(\snd p)
\]%
or, in Coq,
*)

Module Ex2.

Section Ex2a.
Context (A B : Type).

Definition prod_rect (C : Type) (g : A -> B -> C) (p : A * B) 
  := g (fst p) (snd p).

(** We must then show that
%\begin{align*}
    \rec{A\times B}'(C, g, (a, b)) 
    \equiv g(\fst (a, b))(\snd (a, b))
    \equiv g(a)(b)
\end{align*}%
which in Coq amounts to showing that these this equality is a reflexivity.
*)


Theorem prod_rect_correct : forall (C : Type) (g : A -> B -> C) (a : A) (b : B), 
    prod_rect C g (a, b) = g a b. 
Proof.
  reflexivity.
Defined.

End Ex2a.

(** Now for the $\Sigma$-types.  Here we have a projection
%\[
  \fst : \left(\sm{x : A} B(x) \right) \to A
\]%
and another
%\[
  \snd : \prd{p : \sm{x : A} B(x)} B(\fst (p))
\]%
Define a function of type 
%\[
  \rec{\sm{x:A}B(x)}' : \prd{C:\UU} \left(\tprd{x:A} B(x) \to C \right) \to
    \left(\tsm{x:A}B(x) \right) \to C
\]%
by
%\[
  \rec{\sm{x:A}B(x)}'(C, g, p) \defeq g(\fst p)(\snd p)
\]% 
*)

Section Ex2b.

Context (A : Type).
Context (B : A -> Type).


Definition sigma_rect (C : Type) (g : forall (x : A), B x -> C) (p : {x:A & B x}) 
  := g (p.1) (p.2).

(** %\noindent%
We then verify that
%\begin{align*}
  \rec{\sm{x:A}B(x)}(C, g, (a, b))
  \equiv g(\fst (a, b))(\snd (a, b))
  \equiv g(a)(b)
\end{align*}%
*)

Theorem sigma_rect_correct : forall (C:Type) (g : forall x, B x -> C) (a:A) (b:B a), 
  sigma_rect C g (a; b) = g a b. 
Proof.
  reflexivity.
Defined.

End Ex2b.

End Ex2.

(** %\exerdone{1.3}{56}% 
Derive the induction principle for products $\ind{A \times B}$ using only the
projections and the propositional uniqueness principle $\uppt$.
Verify that the definitional equalities are valid.  Generalize $\uppt$
to $\Sigma$-types, and do the same for $\Sigma$-types. *)

(** %\soln% 
The induction principle has type
%\[
  \ind{A\times B} : \prd{C: A\times B \to \UU}\left(\prd{x:A}\prd{y:B}C((x,
    y))\right) \to \prd{z:A\times B}C(z)
\]%
For a first pass, we can define our new inductor as
%\[
  \lam{C}{g}{z}g(\fst z)(\snd z)
\]%
However, we have $g(\fst x)(\snd x) : C((\fst x, \snd x))$, so the type of this
$\ind{A \times B}'$ is
%\[
  \prd{C: A\times B \to \UU}\left(\prd{x:A}\prd{y:B}C((x,
    y))\right) \to \prd{z:A\times B}C((\fst z, \snd z))
    \]%
To define $\ind{A \times B}'$ with the correct type, we need the
$\mathsf{transport}$ operation from the next chapter.  The uniqueness principle
for product types is
%\[
  \uppt : \prd{x : A \times B} \big((\fst x, \snd x) =_{A \times B} x\big)
\]%
By the transport principle, there is a function
%\[
  (\uppt\, x)_{*} : C((\fst x, \snd x)) \to C(x)
\]%
so
%\[
  \ind{A \times B}(C, g, z)
  \defeq
  (\uppt\, z)_{*}(g(\fst z)(\snd z))
\]%
has the right type.  In Coq we use [eta_prod], which is the name for
$\uppt$, then use it with transport to give our $\ind{A\times B}'$.  *)

Module Ex3.
Section Ex3a.
Context (A B : Type).


Definition prod_rect (C : A * B -> Type) (g : forall (x:A) (y:B), C (x, y)) (z : A * B) 
  := (eta_prod z) # (g (fst z) (snd z)).

(** 
We now have to show that
%\[
  \ind{A \times B}(C, g, (a, b)) \equiv g(a)(b)
\]%
Unfolding the left gives
%\begin{align*}
  \ind{A \times B}(C, g, (a, b)) 
  &\equiv
  (\uppt\, (a, b))_{*}(g(\fst (a, b))(\snd (a, b)))
  \\&\equiv
  \ind{=_{A \times B}}(D, d, (a, b), (a, b), \uppt((a, b)))(g(a)(b))
  \\&\equiv
  \ind{=_{A \times B}}(D, d, (a, b), (a, b), \refl{(a, b)})
  (g(a)(b))
  \\&\equiv
  \mathsf{id}_{C((a, b))}(g(a)(b))
  \\&\equiv
  g(a)(b)
\end{align*}%
which was to be proved. *)

Theorem prod_rect_correct : 
  forall (C : A * B -> Type) (g : forall (x:A) (y:B), C (x, y)) (a:A) (b:B), 
    prod_rect C g (a, b) = g a b. 
Proof.
  reflexivity.
Defined.

End Ex3a.


(** For $\Sigma$-types, we define
%\[
  \ind{\tsm{x:A}B(x)}' : \prd{C:(\tsm{x:A}B(x)) \to \UU}
  \left(\tprd{a:A}\tprd{b:B(a)}C((a, b))\right) \to \prd{p: \tsm{x:A}B(x)}C(p)
\]%
at first pass by
%\[
  \lam{C}{g}{p}g(\fst p)(\snd p)
\]%
We encounter a similar problem as in the product case: this gives an output in
$C((\fst p, \snd p))$, rather than $C(p)$.  So we need a uniqueness
principle for $\Sigma$-types, which would be a function
%\[
  \upst : \prd{p : \sm{x:A}B(x)} \big( (\fst p, \snd p) =_{\sm{x:A}B(x)} p \big)
\]%
As for product types, we can define
%\[
  \upst((a, b)) \defeq \refl{(a, b)}
\]%
which is well-typed, since $\fst(a, b) \equiv a$ and $\snd(a, b) \equiv b$.
Thus, we can write
%\[
  \ind{\sm{x:A}B(x)}'(C, g, p) \defeq (\upst\, p)_{*}(g(\fst p)(\snd p)).
\]%
and in Coq, *)

Section Ex3b.
Context (A : Type).
Context (B : A -> Type).


Definition sigma_rect (C : {x:A & B x} -> Type) 
           (g : forall (a:A) (b:B a), C (a; b)) (p : {x:A & B x}) 
  := (eta_sigma p) # (g (p.1) (p.2)).

(** 
Now we must verify that
%\[
  \ind{\sm{x:A}B(x)}'(C, g, (a, b)) \equiv g(a)(b)
\]%
We have
%\begin{align*}
  \ind{\sm{x:A}B(x)}'(C, g, (a, b))
  &\equiv
  (\uppt\, (a, b))_{*}(g(\fst(a, b))(\snd(a, b)))
  \\&\equiv
  \ind{=_{\sm{x:A}B(x)}}'(D, d, (a, b), (a, b), \uppt\, (a, b))
  (g(a)(b))
  \\&\equiv
  \ind{=_{\sm{x:A}B(x)}}'(D, d, (a, b), (a, b), \refl{(a, b)})
  (g(a)(b))
  \\&\equiv
  \mathsf{id}_{C((a, b))}
  (g(a)(b))
  \\&\equiv
  g(a)(b)
\end{align*}% *)


Theorem sigma_rect_correct : 
      forall (C : {x:A & B x} -> Type) 
             (g : forall (a:A) (b:B a), C (a; b)) (a : A) (b : B a), 
        sigma_rect C g (a; b) = g a b. 
Proof.
  reflexivity.
Defined.

End Ex3b.

End Ex3.

(** %\exerdone{1.4}{56}%  
Assuming as given only the _iterator_ for natural numbers
%\[
\ite : 
\prd{C:\UU} C \to (C \to C) \to \mathbb{N} \to C
\]%
with the defining equations
%\begin{align*}
\ite(C, c_{0}, c_{s}, 0) &\defeq c_{0}, \\
\ite(C, c_{0}, c_{s}, \suc(n)) &\defeq c_{s}(\ite(C, c_{0}, c_{s}, n)),
\end{align*}%
derive a function having the type of the recursor $\rec{\mathbb{N}}$.  Show
that the defining equations of the recursor hold propositionally for this
function, using the induction principle for $\mathbb{N}$. *)

Section Ex4.

Variable C : Type.
Variable c0 : C.
Variable cs : nat -> C -> C.

(** %\soln%  
Fix some $C : \UU$, $c_{0} : C$, and $c_{s} : \mathbb{N} \to C \to C$.
$\ite(C)$ allows for the $n$-fold application of a single function to a single
input from $C$, whereas $\rec{\mathbb{N}}$ allows each application to depend on
$n$, as well.  Since $n$ just tracks how many applications we've done, we can
construct $n$ on the fly, iterating over elements of $\mathbb{N} \times C$.  So
we will use the iterator
%\[
\ite_{\mathbb{N} \times C} : \mathbb{N} \times C \to (\mathbb{N} \times C
\to \mathbb{N} \times C) \to \mathbb{N} \to \mathbb{N} \times C
\]%
to derive a function
%\[
\Phi : \prd{C : \UU} C \to (\mathbb{N} \to C \to C) \to
\mathbb{N} \to C
\]%
which has the same type as $\rec{\mathbb{N}}$.  


The first argument of $\ite_{\mathbb{N} \times C}$ is the starting point,
which we'll make $(0, c_{0})$.  The second input takes an element of
$\mathbb{N} \times C$ as an argument and uses $c_{s}$ to construct a new
element of $\mathbb{N} \times C$.  We can use the first and second elements of
the pair as arguments for $c_{s}$, and we'll use $\suc$ to advance the first
argument, representing the number of steps taken.  This gives the function
%\[
\lam{x}(\suc(\fst x), c_{s}(\fst x, \snd x)) 
: \mathbb{N} \times C \to \mathbb{N} \times C
\]%
for the second input to $\ite_{\mathbb{N} \times C}$.  The third input is just
$n$, which we can pass through.  Plugging these in gives
%\[
\ite_{\mathbb{N} \times C}\big(
(0, c_{0}),
\lam{x}(\suc(\fst x), c_{s}(\fst x, \snd x)),
n
\big)
: \mathbb{N} \times C
\]%
from which we need to extract an element of $C$.  This is easily done with the
projection operator, so we have
%\[
\Phi(C, c_{0}, c_{s}, n) \defeq
\snd\bigg(
\ite_{\mathbb{N} \times C}\big(
(0, c_{0}),
\lam{x}(\suc(\fst x), c_{s}(\fst x, \snd x)),
n
\big)
\bigg)
\]%
which has the same type as $\rec{\mathbb{N}}$.  In Coq we first define the
iterator and then our alternative recursor: *)



Fixpoint iter (C : Type) (c0 : C) (cs : C -> C) (n : nat) : C :=
  match n with 
    | O => c0
    | S n' => cs(iter C c0 cs n')
  end.


Definition Phi (C : Type) (c0 : C) (cs: nat -> C -> C) (n : nat) :=
  snd (iter (nat * C)
            (O, c0)
            (fun x => (S (fst x), cs (fst x) (snd x)))
            n).

(** 
  Now to show that the defining equations hold propositionally for $\Phi$.
  For clarity of notation, define
  %\[
  \Phi'(n) = 
  \ite_{\mathbb{N} \times C}\big(
  (0, c_{0}),
  \lam{x}(\suc(\fst x), c_{s}(\fst x, \snd x)),
  n
  \big)
  \]% *)

Definition Phi' (n : nat) := 
  iter (nat * C) (O, c0) (fun x => (S (fst x), cs (fst x) (snd x))) n.

(** %\noindent%
So the propositional equalities can be written
%\begin{align*}
\snd \Phi'(0) &=_{C} c_{0}  \\
\prd{n:\mathbb{N}} \snd \Phi'(\suc(n)) &=_{C} c_{s}(n, \snd \Phi'(n)).
\end{align*}%
The first is straightforward:
%\[
\snd \Phi'(0)
\equiv
\snd\ite_{\mathbb{N} \times C}\big(
(0, c_{0}),
\lam{x}(\suc(\fst x), c_{s}(\fst x, \snd x)),
0
\big)
\equiv
\snd(0, c_{0})
\equiv
c_{0}
\]%
so $\refl{c_{0}} : \snd\Phi'(0) =_{C} c_{0}$.  To establish the second, we use
induction on a strengthened hypothesis involving $\Phi'$.  We will establish
that for all $n : \mathbb{N}$,
%\[
P(n) \defeq 
\Phi'(\suc(n)) =_{C} (\suc(n), c_{s}(n, \snd\Phi'(n)))
\]%
is inhabited.
For the base case, we have
%\begin{align*}
\Phi'(\suc(0)) &\equiv 
\ite_{\mathbb{N} \times C}\big(
(0, c_{0}),
\lam{x}(\suc(\fst x), c_{s}(\fst x, \snd x)),
\suc(0)
\big)
\\&\equiv
\Big(\lam{x}(\suc(\fst x), c_{s}(\fst x, \snd x))\Big)
\ite_{\mathbb{N} \times C}\big(
(0, c_{0}),
\lam{x}(\suc(\fst x), c_{s}(\fst x, \snd x)),
0
\big)
\\&\equiv
\Big(\lam{x}(\suc(\fst x), c_{s}(\fst x, \snd x))\Big)
(0, c_{0})
\\&\equiv
(\suc(0), c_{s}(0, c_{0}))
\\&\equiv
(\suc(0), c_{s}(0, \snd\Phi'(0)))
\end{align*}%
using the derivation of the first propositional equality.  So $P(0)$ is
inhabited, or $p_{0} : P(0)$.  For the induction
hypothesis, suppose that $n : \mathbb{N}$ and that $p_{n} : P(n)$.  A little
massaging gives
%\begin{align*}
\Phi'(\suc(\suc(n)))
&\equiv
\ite_{\mathbb{N} \times C}\big(
(0, c_{0}),
\lam{x}(\suc(\fst x), c_{s}(\fst x, \snd x)),
\suc(\suc(n))
\big)
\\&\equiv
\Big(\lam{x}(\suc(\fst x), c_{s}(\fst x, \snd x))\Big) \Phi'(\suc(n))
\\&\equiv
(\suc(\fst \Phi'(\suc(n))), c_{s}(\fst \Phi'(\suc(n)), \snd \Phi'(\suc(n)))) 
\end{align*}%
We now apply based path induction using $p_{n}$.  Consider the family
%\[
D : \prd{z:\mathbb{N} \times C}(\Phi'(\suc(n)) = x) \to \UU
\]%
given by
%\[
D(z) \defeq 
\Big(\suc(\fst \Phi'(\suc(n))), c_{s}(\fst \Phi'(\suc(n)), \snd
\Phi'(\suc(n)))\Big) 
=
(\suc(\fst z), c_{s}(\fst z, \snd \Phi'(\suc(n)))) 
\]%
Clearly, we have
%\[
\refl{\Phi'(\suc(\suc(n)))} : D(\Phi'(\suc(n)), \refl{\Phi'(\suc(n))})
\]%
so by based path induction, there is an element
%\begin{align*}
f((\suc(n), c_{s}(n, \snd\Phi'(n))), p_{n}) &:
\Big(\suc(\fst \Phi'(\suc(n))), c_{s}(\fst \Phi'(\suc(n)), \snd
\Phi'(\suc(n)))\Big) 
\\&=
(\suc(\fst (\suc(n), c_{s}(n, \snd\Phi'(n)))),
\\&\phantom{---}
c_{s}(\fst (\suc(n), c_{s}(n,
\snd\Phi'(n))), \snd\Phi'(\suc(n)))) 
\end{align*}%
Let $p_{n+1} \defeq f((\suc(n), c_{s}(n, \snd \Phi'(n))))$.
Our first bit of massaging allows us to replace the left hand side of this by
$\Phi'(\suc(\suc(n))$.  As for the right, applying the projections gives
%\begin{align*}
p_{n+1} &: \Phi'(\suc(\suc(n))) 
=
(\suc(\suc(n)), c_{s}(\suc(n), \snd\Phi'(\suc(n)))) 
\equiv P(\suc(n))
\end{align*}%
Plugging all this into our induction principle for $\mathbb{N}$, we can
discharge the assumption that $p_{n} : P(n)$ to obtain
%\[
q \defeq \ind{\mathbb{N}}(P, p_{0}, \lam{n}{p_{n}}p_{n+1}, n) : P(n)
\]%
The propositional equality we're after is a consequence of this, which we again
obtain by based path induction.  Consider the family
%\[
E : \prd{z:\mathbb{N} \times C}(\Phi'(n) = z) \to \UU
\]%
given by
%\[
E(z, p) \defeq 
\snd\Phi'(\suc(n)) = \snd z
\]%
Again, it's clear that
%\[
\refl{\snd\Phi'(\suc(n))} : E(\Phi'(\suc(n)), \refl{\Phi'(\suc(n))}
\]%
So based path induction gives us a function
%\[
g((\suc(n), c_{s}(n, \snd\Phi'(n))), q) : 
\snd\Phi'(\suc(n)) = \snd (\suc(n), c_{s}(n, \snd\Phi'(n)))
\]%
and by applying the projection function on the right and discharging the
assumption of $n$, we have shown that
%\[
\prd{n:\mathbb{N}}\snd\Phi'(\suc(n)) = c_{s}(n, \snd\Phi'(n))
\]%
is inhabited.  Next chapter we'll prove that functions are functors, and we
won't have to do this based path induction every single time.  It'll be great.
Repeating it all in Coq, we have*)

Theorem Phi'_correct1 : snd (Phi' 0) = c0. 
Proof.
  reflexivity.
Defined.

Theorem Phi'_correct2 : forall n, Phi'(S n) = (S n, cs n (snd (Phi' n))).
Proof.
  intros. induction n. reflexivity.
  transitivity ((S (fst (Phi' (S n))), cs (fst (Phi' (S n))) (snd (Phi' (S n))))).
  reflexivity.
  rewrite IHn. reflexivity.
Defined.
  
End Ex4.

(** %\exerdone{1.5}{56}%  
Show that if we define $A + B \defeq \sm{x:\bool} \rec{\bool}(\UU, A,
B, x)$, then we can give a definition of $\ind{A+B}$ for which the
definitional equalities stated in %\S1.7% hold.


%\soln%  
Define $A+B$ as stated.  We need to define a function of type
%\[
\ind{A+B}' : \prd{C : (A + B) \to \UU}
\left( \tprd{a:A} C(\inl(a))\right)
\to
\left( \tprd{b:B} C(\inr(b))\right)
\to
\tprd{x : A + B} C(x)
\]%
which means that we also need to define $\inl' : A \to A + B$ and $\inr' B \to
A + B$; these are
%\begin{align*}
\inl'(a) \defeq (0_{\bool}, a)
\qquad\qquad
\inr'(b) \defeq (1_{\bool}, b)
\end{align*}%
In Coq, we can use [sigT] to define [coprd] as a
$\Sigma$-type: *)

Module Ex5.
Section Ex5.

Context (A B : Type).


Definition sum := {x:Bool & if x then B else A}.
Definition inl (a : A) := existT (fun x:Bool => if x then B else A) false a.
Definition inr (b : B) := existT (fun x:Bool => if x then B else A) true b.

(** 
Suppose that $C : A + B \to \UU$, $g_{0} : \prd{a:A} C(\inl'(a))$, $g_{1} :
\prd{b:B} C(\inr'(b))$, and $x : A+B$; we're looking to define
%\[
\ind{A+B}'(C, g_{0}, g_{1}, x)
\]%
We will use $\ind{\sm{x:\bool}\rec{\bool}(\UU, A, B, x)}$, and for notational
convenience will write $\Phi \defeq \sm{x:\bool}\rec{\bool}(\UU, A, B, x)$.
$\ind{\Phi}$ has signature
%\[
\ind{\Phi} :
\prd{C : \Phi \to \UU}
\left(\tprd{x:\bool}\tprd{y:\rec{\bool}(\UU, A, B, x)}C((x, y))\right)
\to
\tprd{p:\Phi} C(p)
\]%
So
%\[
\ind{\Phi}(C) : 
\left(\tprd{x:\bool}\tprd{y:\rec{\bool}(\UU, A, B, x)}C((x, y))\right)
\to
\tprd{p:\Phi} C(p)
\]%
To obtain something of type $\tprd{x:\bool}\tprd{y:\rec{\bool}(\UU, A, B,
x)}C((x, y))$ we'll have to use $\ind{\bool}$.  In particular, for $B(x)
\defeq\prd{y:\rec{\bool}(\UU, A, B, x)}C((x, y))$ we have
%\[
\ind{\bool}(B)
:
B(0_{\bool})
\to
B(1_{\bool})
\to
\prd{x:\bool}
B(x)
\]%
along with
%\[
g_{0} :
\prd{a:A} C(\inl'(a))
\equiv
\prd{a:\rec{\bool}(\UU, A, B, 0_{\bool})} C((0_{\bool}, a))
\equiv
B(0_{\bool})
\]%
and similarly for $g_{1}$.  So
%\[
\ind{\bool}(B, g_{0}, g_{1}) : \prd{x:\bool}\prd{y:\rec{\bool}(\UU, A, B, x)}
C((x, y))
\]%
which is just what we needed for $\ind{\Phi}$.  So we define
%\[
\ind{A+B}'(C, g_{0}, g_{1}, x)
\defeq
\ind{\sm{x:\bool}\rec{\bool}(\UU, A, B, x)}\left(
C,
\ind{\bool}\left(
\prd{y:\rec{\bool}(\UU, A, B, x)} C((x, y)),
g_{0},
g_{1}
\right),
x
\right)
\]%
and, in Coq, we use sigT_rect, which is the built-in
$\ind{\sm{x:A}B(x)}$: *)


Definition sum_rect (C : sum -> Type) 
           (g0 : forall a : A, C (inl a)) 
           (g1 : forall b : B, C (inr b)) 
           (x : sum) 
  := 
  sigT_rect C 
            (Bool_ind (fun x:Bool => forall (y : if x then B else A), C (x; y))
                      g1 
                      g0) 
            x.

(** 
Now we must show that the definitional equalities
%\begin{align*}
\ind{A+B}'(C, g_{0}, g_{1}, \inl'(a)) \equiv g_{0}(a) \\
\ind{A+B}'(C, g_{0}, g_{1}, \inr'(b)) \equiv g_{1}(b)
\end{align*}%
hold.  For the first, we have
%\begin{align*}
\ind{A+B}'(C, g_{0}, g_{1}, \inl'(a)) 
&\equiv
\ind{A+B}'(C, g_{0}, g_{1}, (0_{\bool}, a)) 
\\&\equiv
\ind{\sm{x:\bool}\rec{\bool}(\UU, A, B, x)}\left(
C,
\ind{\bool}\left(
\prd{y:\rec{\bool}(\UU, A, B, x)} C((x, y)),
g_{0},
g_{1}
\right),
(0_{\bool}, a)
\right)
\\&\equiv
\ind{\bool}\left(
\prd{y:\rec{\bool}(\UU, A, B, x)} C((x, y)),
g_{0},
g_{1},
0_{\bool}
\right)(a)
\\&\equiv
g_{0}(a)
\end{align*}%
and for the second,
%\begin{align*}
\ind{A+B}'(C, g_{0}, g_{1}, \inr'(b)) 
&\equiv
\ind{A+B}'(C, g_{0}, g_{1}, (1_{\bool}, b)) 
\\&\equiv
\ind{\sm{x:\bool}\rec{\bool}(\UU, A, B, x)}\left(
C,
\ind{\bool}\left(
\prd{y:\rec{\bool}(\UU, A, B, x)} C((x, y)),
g_{0},
g_{1}
\right),
(1_{\bool}, b)
\right)
\\&\equiv
\ind{\bool}\left(
\prd{y:\rec{\bool}(\UU, A, B, x)} C((x, y)),
g_{0},
g_{1},
1_{\bool}
\right)(b)
\\&\equiv
g_{1}(b)
\end{align*}% *)


Theorem sum_rect_correct1 : 
  forall C g0 g1 a, sum_rect C g0 g1 (inl a) = g0 a. 
Proof.
  reflexivity.
Qed.

Theorem sum_rect_correct2 : 
  forall C g0 g1 a, sum_rect C g0 g1 (inr a) = g1 a. 
Proof.
  reflexivity.
Qed.

End Ex5.
End Ex5.

(** %\exerdone{1.6}{56}%
Show that if we define $A \times B \defeq \prd{x : \bool}
    \rec{\bool}(\UU, A, B, x)$, then we can give a definition of $\ind{A \times
    B}$ for which the definitional equalities stated in %\S1.5% hold
    propositionally (i.e.%~%using equality types). *)

(** %\soln% 
Define
%\[
  A \times B \defeq \prd{x : \bool} \rec{\bool}(\UU, A, B, x)
\]%
Supposing that $a : A$ and $b : B$, we have an element $(a, b) : A \times B$
given by
%\[
  (a, b) \defeq \ind{\bool}(\rec{\bool}(\UU, A, B), a, b)
\]%
Defining this type and constructor in Coq, we have *)

Module Ex6.
Section Ex6.
Context (A B : Type).


Definition prod := forall x : Bool, if x then B else A.

Definition pair (a : A) (b : B) 
  := Bool_ind (fun x : Bool => if x then B else A) b a.

(** 
An induction principle for $A \times B$ will, given a family $C : A \times B
\to \UU$ and a function 
%\[
g : \prd{x:A}\prd{y:B} C((x, y)),
\]% 
give a function $f : \prd{x : A \times B}C(x)$ defined by
%\[
f((x, y)) \defeq g(x)(y)
\]%
So suppose that we have such a $C$ and $g$.  Writing things out in terms of the
definitions, we have
%\begin{align*}
C &: \left(\prd{x:\bool}\rec{\bool}(\UU, A, B, x)\right) \to \UU \\
g &: \prd{x:A}\prd{y:B} C(\ind{\bool}(\rec{\bool}(\UU, A, B), x, y))
\end{align*}%  
We can define projections by
%\[
\fst p \defeq p(0_{\bool}) \qquad\qquad \snd p \defeq p(1_{\bool})
\]%
Since $p$ is an element of a dependent type, we have
%\begin{align*}
p(0_{\bool}) &: \rec{\bool}(\UU, A, B, 0_{\bool}) \equiv A\\
p(1_{\bool}) &: \rec{\bool}(\UU, A, B, 1_{\bool}) \equiv B
\end{align*}% *)

Definition fst (p : prod) := p false.
Definition snd (p : prod) := p true.

(** 
Then we have
%\begin{align*}
g(\fst p)(\snd p) 
&: C(\ind{\bool}(\rec{\bool}(\UU, A, B), (\fst p), (\snd p)))
\equiv 
C((p(0_{\bool}), p(1_{\bool})))
\end{align*}%
So we have defined a function
%\[
f' : \prd{p : A \times B} C((p(0_{\bool}), p(1_{\bool})))
\]%
But we need one of the type
%\[
f : \prd{p : A \times B} C(p)
\]%
To solve this problem, we need to appeal to function extensionality from %\S2.9%.
This implies that there is a function
%\[
\funext : 
\left(\prd{x:\bool} ((\fst p, \snd p)(x) =_{\rec{\bool}(\UU, A, B, x)} p(x))\right)
\to 
((\fst p, \snd p) =_{A \times B} p)
\]%
We just need to show that the antecedent is inhabited, which we can do with
$\ind{\bool}$.  So consider the family
%\begin{align*}
E &\defeq 
\lam{x : \bool} 
((p(0_{\bool}), p(1_{\bool}))(x) =_{\rec{\bool}(\UU, A, B, x)}  p(x)))
\\&\phantom{:}\equiv
\lam{x : \bool} 
(\ind{\bool}(\rec{\bool}(\UU, A, B), p(0_{\bool}), p(1_{\bool}), x)
=_{\rec{\bool}(\UU, A, B, x)} p(x))
\end{align*}%
We have
%\begin{align*}
E(0_{\bool})
&\equiv
(\ind{\bool}(\rec{\bool}(\UU, A, B),
p(0_{\bool}), p(1_{\bool}), 0_{\bool}) =_{\rec{\bool}(\UU, A, B, 0_{\bool})}
p(0_{\bool}))
\\&\equiv
(p(0_{\bool}) =_{\rec{\bool}(\UU, A, B, 0_{\bool})} p(0_{\bool}))
\end{align*}%
Thus $\refl{p(0_{\bool})} : E(0_{\bool})$.  The same argument goes through to
show that $\refl{p(1_{\bool})} : E(1_{\bool})$.  This means that
%\[
h \defeq
\ind{\bool}(E, \refl{p(0_{\bool})}, \refl{p(1_{\bool})})
:
\prd{x : \bool} ((\fst p, \snd p)(x) =_{\rec{\bool}(\UU, A, B, x)} p(x))
\]%
and thus
%\[
\funext(h) 
: 
(p(0_{\bool}), p(1_{\bool}))
=_{A \times B} 
p 
\]%
This allows us to define the uniqueness principle for products:
%\[
  \uppt \defeq \lam{p}\funext(h)  
  : \prd{p:A \times B} 
  (\fst p, \snd p)
  =_{A \times B} 
  p 
\]%
Now we can define $\ind{A\times B}$ as
%\[
  \ind{A\times B}(C, g, p) \defeq (\uppt\, p)_{*}(g(\fst p)(\snd p))
\]%
In Coq we can repeat this construction using [Funext]. *)

Definition eta_prod `{Funext} (p : prod) : pair (fst p) (snd p) = p.
  apply path_forall.
  unfold pointwise_paths; apply Bool_ind; reflexivity.
Defined.

Definition prod_rect `{Funext} (C : prod -> Type) 
           (g : forall (x:A) (y:B), C (pair x y)) (z : prod) 
  := (eta_prod z) # (g (fst z) (snd z)).

(** 
Now, we must show that the definitional equality holds propositionally.  That
is, we must show that the type
%\[
\ind{A \times B}(C, g, (a, b)) =_{C((a, b))} g(a)(b)
\]%
is inhabited.  Unfolding the left gives
%\begin{align*}
\ind{A \times B}(C, g, (a, b))
&\equiv
(\uppt\, (a, b))_{*}(g(\fst (a, b))(\snd (a, b)))
\\&\equiv
\ind{=_{C((a, b))}}(D, d, (a, b), (a, b), \uppt\, (a, b))(g(a)(b))
\end{align*}%
where $D : \prd{x, y : A \times B} (x = y) \to \UU$ is given by $D(x, y, p)
\defeq C(x) \to C(y)$ and
%\[
d \defeq \lam{x}\idfunc{C(x)} : \prd{x:A\times B} D(x, x, \refl{x})
\]%
Now,
%\[
\uppt\, (a, b) \equiv \funext(h) : (a, b) =_{A \times B} (a, b)
\]%
and, in particular, we have $h : x \mapsto \refl{(a, b)(x)}$, so $\funext(h) =
\refl{(a, b)}$.  Plugging this into $\ind{=_{C((a, b))}}$ and applying its
defining equality gives
%\begin{align*}
\ind{A \times B}(C, g, (a, b))
&=
\ind{=_{C((a, b))}}(D, d, (a, b), (a, b), \refl{(a, b)})(g(a)(b))
\\&=
d((a, b))(g(a)(b))
\\&=
\idfunc{C((a, b))}(g(a)(b))
\\&=
g(a)(b)
\end{align*}%
Verifying that the definitional equality holds propositionally.  The reason we
can only get propositional equality, not judgemental equality, is that
$\funext(h) = \refl{(a, b)}$ is just a propositional equality.  Understanding
this better requires stuff from next chapter. 
*)

Lemma prod_rect_correct `{Funext} C g a b
  : prod_rect C g (pair a b) = g a b.
Proof.
  unfold prod_rect.
  path_via (transport C 1 (g (fst (pair a b)) (snd (pair a b)))). f_ap.
  unfold eta_prod.
  path_via (path_forall (pair (fst (pair a b)) (snd (pair a b))) (pair a b) 
                        (fun _ => idpath)).
  f_ap. apply path_forall; intro x. destruct x; reflexivity.
  apply path_forall_1.
Defined.
  
End Ex6.
End Ex6.


(** %\exerdone{1.7}{56}%             
Give an alternative derivation of $\ind{=_{A}}'$ from $\ind{=_{A}}$ which
avoids the use of universes. *)

(** %\soln%
To avoid universes, we follow the plan from %p.~53% of the text: show that
$\ind{=_{A}}$ entails Lemmas 2.3.1 and 3.11.8, and that these two principles
imply $\ind{=_{A}}'$ directly.  

First we have Lemma 2.3.1, which states that for any type family $P$ over $A$
and $p : x =_{A} y$, there is a function $p_{*} : P(x) \to P(y)$.  The proof
for this can be taken directly from the text.  Consider the type family
%\[
D : \prd{x, y : A}(x = y) \to \UU,
\qquad\qquad
D(x, y, p) \defeq P(x) \to P(y)
\]%
which exists, since $P(x) : \UU$ for all $x : A$ and these can be used to form
function types.  We also have
%\[
d \defeq \lam{x}\idfunc{P(x)} 
: \prd{x:A}D(x, x, \refl{x})
\equiv \prd{x:A} P(x) \to P(x)
\]%
We now apply $\ind{=_{A}}$ to obtain
%\[
p_{*} \defeq \ind{=_{A}}(D, d, x, y, p) : P(x) \to P(y)
\]%
establishing the Lemma.

Next we have Lemma 3.11.8, which states that for any $A$ and any $a : A$, the
    type $\sm{x:A} (a = x)$ is contractible;  that is, there is some $w :
    \sm{x:A}(a=x)$ such that $w = w'$ for all $w' : \sm{x:A}(a=x)$.  Consider the
    point $(a, \refl{a}) : \sm{a:A}(a=x)$ and the family $C: \prd{x,y:A}(x=y) \to \UU$ given
    by
    %\[
    C(x, y, p) \defeq 
    ((x, \refl{x}) =_{\sm{z:A}(x=z)} (y, p))
    \]%
    Take also the function
    %\[
    \refl{(x, \refl{x})} : \prd{x:A} ((x, \refl{x}) =_{\sm{x:A}(x=z)} (x, \refl{x}))
    \]%
    By path induction, then, we have a function
    %\[
    g : \prd{x, y:A}\prd{p:x =_{A} y} 
    ((x, \refl{x}) =_{\sm{z:A}(x=z)} (y, p))
    \]%
    such that $g(x, x, \refl{x}) \defeq \refl{(x, \refl{x})}$.  
    This allows us to construct
    %\[
    \lam{p}g(a, \fst p, \snd p) : 
    \prd{p:\sm{x:A}(a=x)}
    (a, \refl{a}) =_{\sm{z:A}(a=z)} (\fst p, \snd p)
    \]%
    And $\upst$ lets us transport this, using the first lemma, to the statement
    that $\sm{x:A}(a=x)$ is contractible:
    %\[
    \contr \defeq \lam{p}\Big(
    (\upst\,p)_{*}g(a, \fst p, \snd p)
    \Big)
    :
    \prd{p:\sm{x:A}(a=x)}
    (a, \refl{a}) =_{\sm{z:A}(a=z)} p
    \]%

    With these two lemmas we can derive based path induction.  Fix some $a:A$ and
    suppose we have a family
    %\[
    C : \prd{x:A} (a=x) \to \UU
    \]%
    and an element
    %\[
    c : C(a, \refl{a}).
\]%
Suppose we have $x:A$ and $p:a=x$.  Then we have $(x,p) : \sm{x:A}(a=x)$, and
because this type is contractible, an element $\contr_{(x,p)}: (a,\refl{a}) =
(x,p)$.  So for any type family $P$ over $\sm{x:A}(a=x)$, we have the function
$(\contr_{(x,p)})_{*} : P((a, \refl{a})) \to P((x,p))$.  In particular, we have
the type family
%\[
\tilde{C} \defeq \lam{p} C(\fst p, \snd p)
\]%
so
%\[
(\contr_{(x,p)})_{*} : \tilde{C}((a,\refl{a})) \to \tilde{C}((x,p)) \equiv  C(a, \refl{a}) \to C(x, p).
\]%
thus
%\[
(\contr_{(x,p)})_{*}(c) : C(x,p)
\]%
or, abstracting out the $x$ and $p$,
%\[
f \defeq \lam{x}{p}(\contr_{(x,p)})_{*}(c) : \prd{x:A}\prd{p:x=y}C(x,p).
\]%
We also have
%\begin{align*}
f(a, \refl{a}) 
& \equiv 
(\contr_{(a, \refl{a})})_{*}(c)
\\&\equiv
((\upst\, (a, \refl{a}))_{*}g(a, a, \refl{a}))_{*}(c)
\\&\equiv
((\upst\, (a, \refl{a}))_{*}\refl{(a, \refl{a})})_{*}(c)
\\&\equiv
(\ind{=}(\lam{x}((a, \refl{a}) = x), \lam{x}\idfunc{(a, \refl{a})=x}, (a,\refl{a}), (a,\refl{a}),
\refl{(a,\refl{a})})\refl{(a, \refl{a})})_{*}(c)
\\&\equiv
(\idfunc{(a, \refl{a})=(a,\refl{a})}\refl{(a, \refl{a})})_{*}(c)
\\&\equiv
(\refl{(a, \refl{a})})_{*}(c)
\\&\equiv
\ind{=}(\tilde{C}, \lam{x}\idfunc{\tilde{C}(x)}, (a, \refl{a}), (a, \refl{a}), \refl{(a, \refl{a})})(c)
\\&\equiv
\idfunc{\tilde{C}((a, \refl{a}))}(c)
\\&\equiv
\idfunc{C(a, \refl{a})}(c)
\\&\equiv
c
\end{align*}%
So we have derived based path induction.
 *)

Module Ex7.

Section ex7.

Definition ind (A : Type) : forall (C : forall (x y : A), x = y -> Type),
                              (forall (x:A), C x x idpath) -> 
                              forall (x y : A) (p : x = y), C x y p.
Proof.
  path_induction. apply X.
Defined.

Definition Lemma231 {A} (P : A -> Type) (x y : A) (p : x = y) : P(x) -> P(y).
Proof.
  intro. rewrite <- p. apply X.
Defined.

Definition Lemma3118 : forall (A : Type) (a:A), Contr {x:A & a=x}.
Proof.
  intros A a. exists (a; idpath).
  intro x. destruct x as [x p]. path_induction. reflexivity.
Defined.

Definition ind' (A : Type) : forall (a : A) (C : forall (x:A), a = x -> Type),
                               C a idpath -> forall (x:A) (p:a=x), C x p.
Proof.
  intros.
  assert (H : (Contr {x:A & a=x})). apply Lemma3118.
  change (C x p) with ((fun c => C c.1 c.2) (x; p)).
  apply (Lemma231 _ (a; idpath) (x; p)).
  transitivity (center {x : A & a = x}). destruct H as [[a' p'] z]. simpl. 
  rewrite <- p'. reflexivity.
  destruct H as [[a' p'] z]. simpl. rewrite <- p'. rewrite <- p. reflexivity.
  apply X.
Defined.


End ex7.
End Ex7.

(** %\exerdone{1.8}{56}%  
Define multiplication and exponentiation using
$\rec{\mathbb{N}}$.  Verify that $(\mathbb{N}, +, 0, \times, 1)$ is a semiring
using only $\ind{\mathbb{N}}$. *)

Local Open Scope nat_scope.

(** %\soln% 
For multiplication, we need to construct a function $\mult : \mathbb{N}
\to \mathbb{N} \to \mathbb{N}$.  Defined with pattern-matching, we would have
%\begin{align*}
\mult(0, m) &\defeq 0 \\
\mult(\suc(n), m) &\defeq m + \mult(n, m)
\end{align*}%
so in terms of $\rec{\mathbb{N}}$ we have
%\[
\mult \defeq 
\rec{\mathbb{N}}(
\mathbb{N} \to \mathbb{N},
\lam{n}0,
\lam{n}{g}{m}\add(m, g(m))
)
\]%
For exponentiation, we have the function $\expf: \mathbb{N} \to \mathbb{N} \to
\mathbb{N}$, with the intention that $\expf(e, b) = b^{e}$.  In terms of pattern
matching,
%\begin{align*}
\expf(0, b) &\defeq 1 \\
\expf(\suc(e), b) &\defeq \mult(b, \expf(e, b))
\end{align*}%
or, in terms of $\rec{\mathbb{N}}$,
%\[
\expf \defeq \rec{\mathbb{N}}(
\mathbb{N} \to \mathbb{N},
\lam{n}1,
\lam{n}{g}{m}\mult(m, g(m))
)
\]%
In Coq, we can define these by *)

Fixpoint plus (n m : nat) : nat :=
  match n with
    | 0 => m
    | S p => S (p + m)
  end

    where "n + m" := (plus n m) : nat_scope.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | 0 => 0
    | S p => m + (p * m)
  end

    where "n * m" := (mult n m) : nat_scope.

Fixpoint myexp (e b : nat) :=
  match e with
    | 0 => S 0
    | S e' => b * (myexp e' b)
  end.

(** 
To verify that $(\mathbb{N}, +, 0, \times, 1)$ is a semiring, we need stuff
from Chapter 2.  In particular, we need the following properties of the
identity.  First, for all types $A$ and $x, y : A$, we have the inversion
mapping, with type
%\[
p \mapsto p^{-1} : 
(x = y) \to (y = x)
\]%
and such that $\refl{x}^{-1} \equiv \refl{x}$ for each $x : A$.  Second, for
$x, y, z : A$ we have concatenation:
%\[
p \mapsto q \mapsto p \ct q
: (x = y) \to (y = z) \to (x = z)
\]%
such that $\refl{x} \ct \refl{x} \equiv \refl{x}$ for any $x : A$.  To show
that $(\mathbb{N}, +, 0, \times, 1)$ is a semiring, we need to verify that for
all $n, m, k: \mathbb{N}$,
%\begin{enumerate}
\item $\prd{n:\mathbb{N}}0 + n = n = n + 0$
\item $\prd{n:\mathbb{N}}0 \times n = 0 = n \times 0$.
\item $\prd{n:\mathbb{N}}1 \times n = n = n \times 1$
\item $\prd{n,m:\mathbb{N}}n + m = m + n$
\item $\prd{n, m, k:\mathbb{N}}(n+m)+k = n+(m+k)$
\item $\prd{n,m,k:\mathbb{N}}(n \times m) \times k = n \times (m \times k)$
\item $\prd{n,m,k:\mathbb{N}}n \times (m + k) = (n \times m) + (n \times k)$
\item $\prd{n,m,k:\mathbb{N}}(n + m) \times k = (n \times k) + (m \times k)$
\end{enumerate}%
For (i)--(iii), we show each equality separately and then use concatenation to
show the implicit third equality.  We dream of next chapter, where we obtain
the function $\mathsf{ap}$.
%\begin{enumerate}
\item For all $n : \mathbb{N}$, we have
\begin{align*}
0 + n \equiv \add(0, n) \equiv n
\end{align*}
so $\refl{}:\prd{n:\mathbb{N}}0+n = n$.  For the other equality
we'll need induction on $n$.  For the base case, we have
\begin{align*}
0 + 0 \equiv \add(0, 0) \equiv 0.
\end{align*}
so $\refl{0} : 0 = 0 + 0$.
Fix $n$ and suppose for the induction step that $p_{n} : n = n+0$.  Then we have
\begin{align*}
\suc(n) + 0 \equiv \add(\suc(n), 0) \equiv \suc(\add(n, 0))  
\end{align*}
so we turn again to based path induction, with the family
\[
C : \prd{m:\mathbb{N}}(n = m) \to \UU
\qquad\qquad
C(m, p) \defeq (\suc(n) = \suc(m))
\]
and the element $\refl{\suc(n)} : C(n, \refl{n})$.  So we have
\[
\ind{=}'(n, C, \refl{\suc(n)}, \refl{n}, \add(n, 0), p_{n}) 
: 
\suc(n) = \suc(\add(n, 0))
\]
and discharging our induction step gives
\[
q \defeq \ind{\mathbb{N}}(\lam{n}(n = n+0), \refl{0}, 
\lam{n}\ind{=}'(n, C, \refl{\suc(n)}, \refl{n}, \add(n, 0))
)
:
\prd{n:\mathbb{N}} (n = n+0)
\]
For the final equality, we use concatenation.  From $\refl{n} : 0 + n = n$ and
$q_{n} : n = n + 0$, we have $\refl{n} \ct q_{n} : 0 + n = n + 0$.

\item For all $n : \mathbb{N}$,
\[
0 \times n \equiv \mult(0, n) \equiv 0
\]
so $\lam{n}\refl{0} : \prd{n:\mathbb{N}}0 \times n = 0$.  For the other
direction, induction on $n$.  The base case is
\[
0 \times 0 = \mult(0, 0) = 0
\]
so $\refl{0} : 0 = 0 \times 0$.  Fixing $n$ and supposing for the induction step that $p_{n} :
0 = n \times 0$, we have
\[
\mult(\suc(n), 0) \equiv 0 + \mult(n, 0) \equiv \add(0, \mult(n, 0)) \equiv
\mult(n, 0)
\]
so $p_{n} : 0 = \suc(n) \times 0$.  Thus
\[
q 
\defeq \ind{\mathbb{N}}(\lam{n}(0 = n \times 0), \refl{0}, \lam{n}\idfunc{n = n \times 0}) 
: \prd{n : \mathbb{N}} (n = n \times 0).
\]
And again, $\refl{0} \ct q_{n} : 0 \times n = n \times 0$ gives us the last
equality.

\item For all $n : \mathbb{N}$,
\[
1 \times n \equiv \suc(0) \times n 
\equiv n + (0 \times n) \equiv n + 0
\]
so, recalling $q_{n}$ from (i), we have $\refl{1 \times n} \ct q^{-1}_{n} : 1
\times n = n$.  For the other direction, we proceed by induction on $n$.  For
the base case we have
\[
0 \times 1 \equiv \mult(0, 1) \equiv 0
\]
so $\refl{0} : 0 = 0 \times 1$.  Fixing $n$ and supposing for induction that $p_{n} : n = n
\times 1$, we have
\[
\mult(\suc(n), 1) 
\equiv 1 + \mult(n, 1) 
\equiv \suc(0) + \mult(n, 1)
\equiv \suc(n \times 1)
\]
So we turn to based path induction again.  Let $C(m) = \suc(n) = \suc(m)$; then
    \[
    \ind{=}'(n, C, \refl{\suc(n)}, n \times 1, p_{n})
    : \suc(n) = \suc(n \times 1)
    \]
    and
    \[
    r \defeq \ind{\mathbb{N}}(\lam{n}(n = n \times 1), \refl{0}, 
    \lam{n}\ind{=}'(n, C, \refl{\suc(n)}, n \times 1))
    : \prd{n:\mathbb{N}}(n = n \times 1)
    \]
    For the third equality, finally, $\refl{1 \times n} \ct q_{n}^{-1} \ct r_{n} : 1
    \times n = n \times 1$.

\item We first prove an auxiliary lemma by induction: $\prd{n,
m:\mathbb{N}} \suc(n+m) = n + \suc(m)$.  For the base case, we have $\suc(0+m)
\equiv \suc(m) \equiv 0 + \suc(m)$, so $\refl{\suc(m)} : \suc(0+m) = 0 +
\suc(m)$.  Fix $n : \mathbb{N}$, and suppose for induction that $p_{n} : \suc(n
+ m) = n + \suc(m)$.  Then
\[
\suc(\suc(n) + m) \equiv \suc(\suc(n+m))
\]
and based path induction on $C(m) \defeq \suc(\suc(n + m)) = \suc(m)$ gives
\[
\ind{=}'(\suc(n+m), C, \refl{\suc(\suc(n+m))}, n + \suc(m), p_{n})
: \suc(\suc(n+m)) = \suc(n + \suc(m))
\]
so letting $D(n) \defeq \prd{m : \mathbb{N}}(\suc(n+m) = n + \suc(m))$,
\[
r \defeq \ind{\mathbb{N}}(D, \refl{\suc(m)}, 
\lam{n}\ind{=}'(\suc(n+m), C, \refl{\suc(\suc(n+m))}, n + \suc(m))
)
: \prd{n:\mathbb{N}} D(n)
\]

We now proceed by induction on $n$ to show (iv).  For the base case, recalling
$q_{n}$ from (i), we have $\refl{m} \ct q_{m} : 0 + m = m + 0$.  Fixing $n$ and
supposing for induction that $p_{n} : n + m = m + n$, we have
\[
\suc(n) + m \equiv \suc(n + m)
\]
We then apply based path induction on $E(k) \defeq \suc(n+m) = \suc(k)$ to
obtain
\begin{align*}
\ind{=}'(n+m, E, \refl{\suc(n+m)}, m+n, p_{n}) &: \suc(n)+m = \suc(m+n) \\
\ind{=}'(n+m, E, \refl{\suc(n+m)}, m+n, p_{n}) \ct r_{m,n} &: \suc(n)+m = m +
\suc(n)
\end{align*}
and, finally, for the family $F(n) = n+m = m + n$,
\[
\ind{\mathbb{N}}(F, \refl{m} \ct q_{m}, 
\lam{n}{p}(
\ind{=}'(n+m, E, \refl{\suc(n+m)}, m+n, p) \ct r_{m,n}
)
) : \prd{n:\mathbb{M}}n+m = m+m
\]
Abstracting out the $m$ gives us (iv).

\item Fix $m$ and $k$.  We proceed by induction on $n$.  For the base case,
\[
(0 + m) + k \equiv m + k \equiv 0 + (m + k)
\]
By the definition of $\add$.  Fix $n$, and suppose that $p_{n} : (n + m) + k =
n + (m + k)$.  We have
\[
(\suc(n) + m) + k
\equiv \suc(n + m) + k
\equiv \suc((n+m)+k)
\]
So based path induction on $C(\ell) = \suc((n+m)+k) = \suc(\ell)$ gives
\[
\ind{=}'((n+m)+k, C, \refl{\suc((n+m)+k)}, n+(m+k), p_{n})
:
\suc((n+m)+k) = \suc(n+(m+k))
\]
which is equivalently the type $(\suc(n)+m)+k = \suc(n) + (m + k)$.  So
induction over $D(n) = (n+m)+k = n+(m+k)$ gives
\[
\ind{\mathbb{N}}(D, \refl{(0+m)+k}, 
\lam{n}{p}
\ind{=}'((n+m)+k, C, \refl{\suc((n+m)+k)}, n+(m+k), p)
)
:
\prd{n:\mathbb{N}}D(n)
\]
and abstracting out the $m$ and $k$ gives us (v).

\item Fix $m$ and $k$.  First an auxiliary lemma; we show that $(n+m) \times k
= (n \times k) + (m \times k)$ by induction on $n$.  For the base case,
\[
(0+m) \times k \equiv m \times k \equiv 0 + (m \times k) \equiv (0 \times k)
+ (m \times k)
\]
Now fix $n$ and suppose that $p_{n} : (n+m) \times k = n \times k + m \times
k$.
\[
(\suc(n) + m) \times k
\equiv \suc(n + m) \times k
\equiv k + (n + m) \times k
\]
and
\[
\suc(n) \times k + m \times k
\equiv 
(k + n \times k) + m \times k
\]
Using based path induction over $C(\ell) \defeq k + (n + m) \times k = k +
\ell$, we get
\[
\ind{=}'((n+m)\times k, C, \refl{k+(n+m)\times k}, n \times k + m \times
k, p_{n})
:
k + (n+m) \times k = k + (n \times k + m \times k)
\]
We established in (v) that addition is associative, so we have some
\[
r_{k, n \times k, m \times k}^{-1} 
: k + (n \times k + m \times k) = (k + n
\times k) + m \times k
\]
and concatenating this with the result of the based path induction gives
something of type
\[
k + (n + m) \times k = (k + n \times k) + m \times k
\]
Our two strings of judgemental equalities mean that this is the same as the
type
\[
(\suc(n) + m) \times k = \suc(n) \times k + m \times k.
\]
So we can now perform the induction over $D(\ell) = (n + m) \times k = n \times
k + m \times k$ to obtain
\[
\ind{\mathbb{N}}(D, \refl{(0+m) \times k}, 
\lam{n}{p}(
\ind{=}'((n+m)\times k, C, \refl{k+(n+m)\times k}, n \times k + m \times
k, p_{n})
\ct
r_{k, n \times k, m \times k}^{-1})
)
\]
which is of type
\[
\prd{n : \mathbb{N}} (n+m) \times k = n \times k + m \times k
\]
abstracting out the $m$ and $k$ give the final result (i.e., that
multiplication on the right distributes over addition).

Now, for (vi).  As always, it's induction on $n$.  For the base case
\[
(0 \times m) \times k
\equiv 0 \times k
\equiv 0
\equiv 0 \times (m \times k)
\]
Now fix $n$ and assume that $p_{n} : (n \times m) \times k = n \times (m \times
k)$.  We have
\[
(\suc(n) \times m) \times k
\equiv (m + n \times m) \times k
\]
and
\[
\suc(n) \times (m \times k)
\equiv
m \times k + n \times (m \times k)
\]
From our lemma, then, there is a function
\[
q : \prd{n:\mathbb{N}} (\suc(n) \times m) \times k = m \times k + (n \times
m) \times k
\]
we use based path induction over $E(\ell) \defeq m \times k + \ell$ to obtain
\[
\ind{=}'((n\times m)\times k, E, \refl{m\times k + (n \times m) \times k}, n
\times (m \times k), p_{n})
:
m \times k + (n \times m) \times k = m \times k + n \times (m \times k)
\]
which, concatenated with $q_{n}$ and altered by the second judgemental
equality, gives something of type
\[
(\suc(n) \times m) \times k = \suc(n) \times (m \times k)
\]
So our induction principle over $F(\ell) \defeq (n \times m) \times k = n
\times (m \times k)$ gives
\[
\ind{\mathbb{N}}(F,\refl{(0 \times m) \times k},
\lam{n}{p}(
q_{n} \ct \ind{=}'((n\times m)\times k, E, \refl{m\times k + (n \times m) \times k}, n
\times (m \times k), p_{n}) )
)
\]
of type
\[
\prd{n:\mathbb{N}} (n \times m) \times k = n \times (m \times k)
\]
and abstracting out the $m$ and $k$ gives (vi).

\item Fix $m$ and $k$.  We proceed by induction on $n$.  For the base case we
have
\[
0 \times (m + k)
\equiv 0
\equiv 0 + 0
\equiv (0 \times m) + (0 \times k)
\]
So fix $n : \mathbb{N}$ and suppose that $p_{n} : n \times (m + k) = (n \times
m) + (n \times k)$.  We have
\[
\suc(n) \times (m + k)
\equiv
(m+k) + n \times (m + k)
\]
and
\[
(\suc(n) \times m) + (\suc(n) \times k)
\equiv
(m + n \times m) + (k + n \times k)
\]
Now by (iv) and (v) we have the following two functions
\begin{align*}
q : \prd{n, m:\mathbb{N}} n + m = m + n
\qquad\qquad
r : \prd{n, m, k:\mathbb{N}} (n + m) + k = n + (m + k)
\end{align*}
A long chain of based path inductions allows us to construct an object of type
\[
(\suc(n) \times m) + (\suc(n) \times k) = (m+k) + (n \times m + n \times k)
\]
In the interest of masochism, I'll do them explicitly.  We start with
\[
r_{1} \defeq r_{m, n \times m, k+n\times k} 
: (m + n \times m) + (k + n \times k)
= m + (n \times m + (k + n \times k))
\]
Based path induction over $C_{1}(\ell) \defeq m + (n \times m + (k + n \times
k)) = m + \ell$ and using
\[
r_{2} \defeq r_{n \times m, k, n \times k}
: n \times m + (k + n \times k)
= (n \times m + k) + n \times k
\]
gives
\[
\langle r_{2} \rangle \defeq 
\ind{=}'(n\times m + (k + n \times k), C_{1}, \refl{m+(n\times m + (k + n
\times k))}, (n \times m + k) + n \times k, r_{2}
)
\]
which results in
\[
r_{1} 
\ct
\langle r_{2} \rangle
:
(m + n \times m) + (k + n \times k)
=
m + ((n \times m + k) + n \times k)
\]
Next consider
\[
q_{1} \defeq q_{n\times m, k} : n \times m + k = k + n \times m
\]
which is passed through a based path induction on $C_{2}(\ell) \defeq m + ((n
\times m + k) + n \times k) =  m + (\ell
+ n \times k)$ to get
\[
\langle q_{1} \rangle
\defeq
\ind{=}'(n \times m + k, C_{2}, \refl{m + ((n \times m + k) + n \times k)}, k + n
\times m, q_{1})
\]
which adds to our chain, giving
\[
r_{1} \ct \langle r_{2} \rangle \ct \langle q_{1} \rangle
:
(m + n \times m) + (k + n \times k)
=
m + ((k + n \times m) + n \times k)
\]
Now just two applications of associativity are left.  We have
\[
r_{3} \defeq r_{k, n \times m, n \times k}
:
(k + n \times m) + n \times k
=
k + (n \times m + n \times k)
\]
so for $C_{3}(\ell) \defeq m + ((k + n \times m) + n \times k) = m + \ell$, we have
\[
\langle r_{3} \rangle \defeq
\ind{=}'((k + n \times m) + n \times k, C_{3}, \refl{m + ((k + n \times m) + n
\times k)}, k + (n \times m + n \times k), r_{3})
\]
making our chain of type
\[
r_{1} \ct \langle r_{2} \rangle \ct \langle q_{1} \rangle \ct \langle r_{3}
\rangle
:
(m + n \times m) + (k + n \times k)
=
m + (k + (n \times m + n \times k))
\]
Finally, take
\[
r_{4} \defeq r^{-1}_{m, k, n \times m + n \times k}
:
m + (k + (n \times m + n \times k))
=
(m + k) + (n \times m + n \times k)
\]
so after applying the last judgemental equality above, we have
\[
f \defeq
r_{1} \ct \langle r_{2} \rangle \ct \langle q_{1} \rangle \ct \langle r_{3}
\rangle \ct r_{4}
:
(\suc(n) \times m) + (\suc(n) \times k)
=
(m + k) + (n \times m + n \times k)
\]
Now, consider the family $D(\ell) \defeq (m+k) + n \times (m+k) = (m+k) +
\ell$.  Based path induction once more gives us
\[
\ind{=}'(n \times (m + k), D, \refl{(m+k)+n\times(m+k)}, n \times m + n
\times k, p_{n}) \ct f^{-1}
\]
which, after application of our judgemental equalities, is of type
\[
\suc(n) \times (m + k) = (\suc(n) \times m) + (\suc(n) \times k)
\]
So we can at last apply induction over $\mathbb{N}$, using the family $E(n) : n
\times (m + k) = (n \times m) + (n \times k)$, giving
\[
\ind{\mathbb{N}}(E, \refl{0 \times (m + k)}, 
\lam{n}{p}(
\ind{=}'(n \times (m + k), D, \refl{(m+k)+n\times(m+k)}, n \times m + n
\times k, p) \ct f^{-1}
))
\]
which is of type
\[
\prd{n:\mathbb{N}} n \times (m + k) = (n \times m) + (n \times k)
\]
and $m$ and $k$ may be abstracted out to give (vii). 

\item This was shown as a lemma in proving (vi).

\end{enumerate}%

In Coq we'll do things a touch out of order, so as to appeal to (viii) in the
proof of (vi). *)

Theorem plus_O_r : forall (n : nat), n = plus n 0.
Proof.
  induction n. reflexivity. apply (ap S IHn).
Defined.

Theorem ex1_8_i : forall (n : nat), 
                    (0 + n = n) /\ (n = n + 0) /\ (0 + n = n + 0).
Proof.
  split; [| split; rewrite <- plus_O_r]; reflexivity.
Qed.

Theorem mult_0_r : forall (n : nat), 0 = n * 0.
Proof.
  induction n; [| simpl; rewrite <- IHn]; reflexivity.
Qed. 

Theorem ex1_8_ii : forall (n : nat),
                     (0 * n = 0) /\ (0 = n * 0) /\ (0 * n = n * 0).
Proof.
  split; [| split; rewrite <- mult_0_r]; reflexivity.
Qed.

Theorem mult_1_r : forall (n : nat), n = n * 1.
Proof.
  induction n; [| simpl; rewrite <- IHn]; reflexivity.
Qed.

Theorem mult_1_l : forall (n : nat), 1 * n = n.
Proof.
  simpl; intro n; rewrite <- plus_O_r; reflexivity.
Qed.

Theorem ex1_8_iii : forall (n : nat),
                      (1 * n = n) /\ (n = n * 1) /\ (1 * n = n * 1).
Proof.
  split; [rewrite mult_1_l
         | split; rewrite <- mult_1_r; 
           [| rewrite mult_1_l]];
  reflexivity.
Qed.

Theorem plus_n_Sm : forall (n m : nat), S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n. reflexivity.
  simpl. apply (ap S). apply IHn.
Defined.

Theorem plus_comm : forall (n m : nat), n + m = m + n.
Proof.
  intros n m.
  induction n. apply plus_O_r.
  refine (_ @ (plus_n_Sm _ _)). apply (ap S IHn).
Defined.
  

Theorem plus_assoc : forall (n m k : nat),
                    (n + m) + k = n + (m + k).
Proof.
  intros n m k.
  induction n; [| simpl; rewrite IHn]; reflexivity.
Qed.

Theorem ex1_8_viii : forall (n m k : nat),
                       (n + m) * k = (n * k) + (m * k).
Proof.
  intros n m k.
  induction n. reflexivity. simpl. 
  refine (_ @ (plus_assoc _ _ _)^).
  apply (ap (plus k) IHn).
Defined.

Theorem ex1_8_vi : forall (n m k : nat),
                     (n * m) * k = n * (m * k).
Proof.
  intros n m k.
  induction n; [| simpl; rewrite <- IHn; rewrite <- ex1_8_viii]; reflexivity.
Qed.

Theorem ex1_8_vii : forall (n m k : nat),
                      n * (m + k) = (n * m) + (n * k).
Proof.
  intros n m k.
  induction n. reflexivity.
  simpl.
  refine (_ @ (plus_assoc _ _ _)^).
  refine ((plus_assoc _ _ _) @ _). apply (ap (plus m)).
  refine (_ @ (plus_comm _ _)).
  refine (_ @ (plus_assoc _ _ _)^).
  apply (ap (plus k)). refine (IHn @ _). apply plus_comm.
Defined.

Local Close Scope nat_scope.

(** %\exerdone{1.9}{56}%  
Define the type family $\Fin : \mathbb{N} \to \UU$ mentioned at the end of
%\S1.3%, and the dependent function $\fmax : \prd{n : \mathbb{N}} \Fin(n + 1)$
mentioned in %\S1.4%. *)


(** %\soln%  
$\Fin(n)$ is a type with exactly $n$ elements.  Consider $\Fin(n)$ from the
types-as-propositions point of view: $\Fin(n)$ is a predicate that applies to
exactly $n$ elements.  Recalling that $\sm{m:\mathbb{N}}(m < n)$ may be
regarded as ``the type of all elements $m : \mathbb{N}$ such that $(m < n)$'',
we note that there are $n$ such elements, and define
%\[
  \Fin(n) 
  \defeq \sum_{m:\mathbb{N}} (m < n)
  \equiv \sum_{m:\mathbb{N}} \sm{k:\mathbb{N}}(m+ \suc(k) = n)
\]%
And in Coq, *)

Local Open Scope nat_scope.

Definition le (n m : nat) : Type := {k:nat & n + k = m}.
Notation "n <= m" := (le n m)%nat (at level 70) : nat_scope.

Definition lt (n m : nat) : Type := {k : nat & n + S k = m}.
Notation "n < m" := (lt n m)%nat (at level 70) : nat_scope.

Definition Fin (n:nat) : Type := {m:nat & m < n}.

(** %\noindent%
To define $\fmax$, note that one can think of an element of $\Fin(n)$ as a
tuple $(m, (k, p))$, where $p : m + \suc(k) = n$.  The maximum element of
$\Fin(n+1)$ will have the greatest value in the first slot, so
%\[
  \fmax(n) \defeq n_{n+1} \defeq (n, (0, \refl{n+1}))
  : \sm{m:\mathbb{N}}\sm{k:\mathbb{N}} (m+\suc(k) = n+1)
  \equiv \Fin(n+1)
\]% *)


Definition fmax (n:nat) : Fin(n+1) := (n; (0; idpath)).

(** %\noindent%
To verify that this definition is correct, we need to show that
%\[
  \prd{n:\mathbb{N}}\prd{m_{n+1}:\Fin(n+1)} (\fst(m_{n+1}) \leq \fst(\fmax(n)))
\]%
is inhabited.  Unfolding this a bit, we get
%\[
  \prd{n:\mathbb{N}}\prd{m_{n+1}:\Fin(n+1)} (m \leq n)
  \equiv
  \prd{n:\mathbb{N}}\prd{m_{n+1}:\Fin(n+1)}\sm{k:\mathbb{N}} (m + k = n)
\]%
Fix some such $n$ and $m_{n+1}$.  By the induction principle for
$\Sigma$-types, we can write $m_{n+1} = (m^{1}, (m^{2}, m^{3}))$, where $m^{3}
: m^{1} + \suc(m^{2}) = n + 1$.  Using the results of the previous exercise, we
can obtain from $m^{3}$ a proof $p : m^{1} + m^{2} = n$.  So $(m^{2}, p)$ is a
witness to our result.  *)


Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Theorem S_inj : forall (n m : nat), S n = S m -> n = m.
Proof.
  intros n m H.
  change n with (pred (S n)). change m with (pred (S m)).
  apply (ap pred). apply H.
Defined.

Theorem plus_1_r : forall n, S n = n + 1.
Proof.
  intros. rewrite plus_comm. reflexivity.
Qed.

Theorem fmax_correct : forall (n:nat) (m:Fin(n+1)),
                         m .1 <= (fmax n) .1.
Proof.
  unfold Fin, lt, le. intros. simpl.
  exists m.2.1.
  apply S_inj. rewrite plus_n_Sm.
  rewrite m.2.2.
  symmetry.
  apply plus_1_r.
Qed.

Local Close Scope nat_scope.

(** 
    %\exerdone{1.10}{56}%  
    Show that the Ackermann function $\ack : \mathbb{N} \to
        \mathbb{N} \to \mathbb{N}$,
        satisfying the following equations
        %\begin{align*}
        \ack(0, n) &\equiv \suc(n), \\
        \ack(\suc(m), 0) &\equiv \ack(m, 1), \\
        \ack(\suc(m), \suc(n)) &\equiv \ack(m, \ack(\suc(m), n)),
        \end{align*}%
        is definable using only $\rec{\mathbb{N}}$.


    %\soln% 
    $\ack$ must be of the form
    %\[
    \ack \defeq 
    \rec{\mathbb{N}}(\mathbb{N} \to \mathbb{N}, \Phi, \Psi)
    \]%
    with
        %\[
        \Phi : \mathbb{N} \to \mathbb{N}
        \qquad\qquad
        \Psi : \mathbb{N} \to (\mathbb{N} \to \mathbb{N}) \to (\mathbb{N} \to
        \mathbb{N})
        \]%
        which we can determine by their intended behaviour.  We have
        %\[
        \ack(0, n)
        \equiv
        \rec{\mathbb{N}}(\mathbb{N} \to \mathbb{N}, \Phi, \Psi, 0)(n)
        \equiv
        \Phi(n)
        \]%
        So we must have $\Phi \defeq \suc$, which is of the correct type.  The next
        equation gives us
        %\begin{align*}
        \ack(\suc(m), 0)
        &\equiv
        \rec{\mathbb{N}}(\mathbb{N} \to \mathbb{N}, \suc, \Psi, \suc(m))(0)
        \\&\equiv
        \Psi(m, \rec{\mathbb{N}}(\mathbb{N} \to \mathbb{N}, \suc, \Psi, m))(0)
        \\&\equiv
        \Psi(m, \ack(m, -), 0)
        \end{align*}%
    Suppose that $\Psi$ is also defined in terms of $\rec{\mathbb{N}}$.  We know
    its signature, giving the first arg, and this second equation gives its
    behavior on $0$, the second arg.  So it must be of the form
    %\[
    \Psi = 
    \lam{m}{r} \rec{\mathbb{N}}(\mathbb{N}, r(1), \Theta(m, r))
    \qquad
    \Theta : \mathbb{N} \to (\mathbb{N} \to \mathbb{N}) \to \mathbb{N} \to \mathbb{N} \to \mathbb{N}
    \]%
    The final equation fixes $\Theta$:
    %\begin{align*}
    &\phantom{\equiv} \ack(\suc(m), \suc(n))
    \\&\equiv
    \rec{\mathbb{N}}(\mathbb{N} \to \mathbb{N}, \suc, 
    \lam{m}{r} \rec{\mathbb{N}}(\mathbb{N}, r(1), \Theta(m, r)),
    \suc(m))(\suc(n))
    \\&\equiv
    \rec{\mathbb{N}}(\mathbb{N}, \ack(m, 1), \Theta(m, \ack(m, -)), \suc(n))
    \\&\equiv
    \Theta(m, \ack(m, -), n, 
    \rec{\mathbb{N}}(\mathbb{N}, \ack(m, 1), \Theta(m, \ack(m, -)), n)
    )
    \\&\equiv
    \Theta(m, \ack(m, -), n, 
    \Psi(m, \ack(m, -), n)
    )
    \end{align*}%
    Looking at the second equation again suggests that the final argument to
    $\Theta$ is really $\ack(\suc(m), n)$.  Supposing this is true,
    %\[
    \Theta \defeq \lam{m}{r}{n}{s}r(s)
    \]%
    should work.  Putting it all together, we have
    %\[
    \ack \defeq 
    \rec{\mathbb{N}}(\mathbb{N} \to \mathbb{N}, 
    \suc,
    \lam{m}{r}\rec{\mathbb{N}}(\mathbb{N}, 
    r(1), 
    \lam{n}{s}r(s))
    )
    \]%
In Coq, we define *)

Definition ack : nat -> nat -> nat :=
  nat_rect (fun _ => nat -> nat)
           S
           (fun m r => nat_rect (fun _ => nat)
                                (r (S 0))
                                (fun n s => (r s))).


(** Now, to show that the three equations hold, we just calculate
%\begin{align*}
\ack(0, n)
&\equiv 
\rec{\mathbb{N}}(\mathbb{N} \to \mathbb{N}, 
\suc,
\lam{m}{r}\rec{\mathbb{N}}(\mathbb{N}, 
r(1), 
\lam{n}{s}r(s)),
0
)
(n)
\equiv
\suc(n)
\end{align*}%
for the first,
%\begin{align*}
\ack(\suc(m), 0)
&\equiv 
\rec{\mathbb{N}}(\mathbb{N} \to \mathbb{N}, 
\suc,
\lam{m}{r}\rec{\mathbb{N}}(\mathbb{N}, 
r(1), 
\lam{n}{s}r(s)),
\suc(m)
)
(0)
\\&\equiv
\rec{\mathbb{N}}(\mathbb{N}, \ack(m, 1), \lam{n}{s}\ack(m, s), 0)
\\&\equiv
\ack(m, 1)
\end{align*}%
for the second, and finally
%\begin{align*}
\ack(\suc(m), \suc(n))
&\equiv 
\rec{\mathbb{N}}(\mathbb{N} \to \mathbb{N}, 
\suc,
\lam{m}{r}\rec{\mathbb{N}}(\mathbb{N}, 
r(1), 
\lam{n}{s}r(s)),
\suc(m)
)
(\suc(n))
\\&\equiv
\rec{\mathbb{N}}(\mathbb{N}, \ack(m, 1), \lam{n}{s}\ack(m, s), \suc(n))
\\&\equiv
\ack(m, \rec{\mathbb{N}}(\mathbb{N}, \ack(m, 1), \lam{n}{s}\ack(m, s), n))
\end{align*}%
Focus on the second argument of the outer $\ack$.  We have
    %\begin{align*}
    \ack(\suc(m), n) 
    &\equiv
    \rec{\mathbb{N}}(\mathbb{N} \to \mathbb{N}, 
    \suc,
    \lam{m}{r}\rec{\mathbb{N}}(\mathbb{N}, 
    r(1), 
    \lam{n}{s}r(s)),
    \suc(m)
    )
    (n)
    \\&\equiv
    \rec{\mathbb{N}}(\mathbb{N}, \ack(m, 1), \lam{n}{s}\ack(m,s), n)
    \end{align*}%
    and so we may substitute it back in to get
    %\[
    \ack(\suc(m), \suc(n))
    \equiv
    \ack(m, \ack(\suc(m), n))
    \]%
    which is the third equality.  In Coq,
 *)

Goal forall n, ack 0 n = S n. auto. Qed.
Goal forall m, ack (S m) 0 = ack m (S 0). auto. Qed.
Goal forall m n, ack (S m) (S n) = ack m (ack (S m) n). auto. Qed.

Close Scope nat_scope.

(** %\exerdone{1.11}{56}%  
Show that for any type $A$, we have $\lnot\lnot\lnot A \to
    \lnot A$.


%\soln% 
Suppose that $\lnot\lnot\lnot A$ and $A$.  Supposing further that $\lnot
A$, we get a contradiction with the second assumption, so $\lnot \lnot A$.  But
this contradicts the first assumption that $\lnot\lnot\lnot A$, so $\lnot A$.
Discharging the first assumption gives $\lnot\lnot\lnot A \to \lnot A$.


In type-theoretic terms, the first assumption is $x : ((A \to \emptyt) \to
\emptyt) \to \emptyt$, and the second is $a : A$.  If we further assume that
$h : A \to \emptyt$, then $h(a) : \emptyt$, so discharging the $h$ gives
%\[
\lam{h:A \to \emptyt}h(a) : (A \to \emptyt) \to \emptyt
\]%
But then we have
%\[
x(\lam{h : A \to \emptyt}h(a)) : \emptyt
\]%
so discharging the $a$ gives
%\[
\lam{a:A}x(\lam{h : A \to \emptyt}h(a)) : A \to \emptyt
\]%
And discharging the first assumption gives
%\[
\lam{x:((A\to\emptyt)\to\emptyt)\to\emptyt}{a:A}x(\lam{h : A \to
\emptyt}h(a)) :
(((A \to \emptyt) \to \emptyt) \to \emptyt) \to (A \to \emptyt)
\]% *)


Goal forall A, ~ ~ ~ A -> ~A. auto. Qed.

(** 
%\noindent% 
We can get a proof out of Coq by printing this [Goal].  It returns
    [[
    fun (A : Type) (X : ~ ~ ~ A) (X0 : A) => X (fun X1 : A -> Empty => X1 X0) 
    : forall A : Type, ~ ~ ~ A -> ~ A
    ]]
    %\noindent%
    which is just the function obtained by hand. *)

(** %\exerdone{1.12}{56}%  
    Using the propositions as types interpretation, derive the
    following tautologies.
%\begin{enumerate}
\item If $A$, then (if $B$ then $A$).
\item If $A$, then not (not $A$).
\item If (not $A$ or not $B$), then not ($A$ and $B$).
\end{enumerate}% *)

Section Ex12.
  Context (A B : Type).

  (** 
%\soln% 
(i)  Suppose that $A$ and $B$; then $A$.  Discharging the
assumptions, $A \to B \to A$.  That is, we
have 
%\[
\lam{a:A}{b:B}a : A \to B \to A
\]%
and in Coq, *)


  Goal A -> B -> A. trivial. Qed.

  (** 
(ii)  Suppose that $A$.  Supposing further that $\lnot A$ gives a
contradiction, so $\lnot\lnot A$.  That is,
%\[
\lam{a:A}{f:A \to \emptyt}f(a) : A \to (A \to \emptyt) \to \emptyt
\]% *)
  Goal A -> ~ ~ A. auto. Qed.

  (** 
(iii)
Finally, suppose $\lnot A \lor \lnot B$.  Supposing further that $A \land B$
means that $A$ and that $B$.  There are two cases.  If $\lnot A$, then we have
a contradiction; but also if $\lnot B$ we have a contradiction.  Thus $\lnot (A
\land B)$.


Type-theoretically, we assume that $x : (A \to\emptyt) + (B \to\emptyt)$ and $z
: A \times B$.  Conjunction elimination gives $\fst z : A$ and $\snd z : B$.
We can now perform a case analysis.  Suppose that $x_{A} : A \to \emptyt$; then
$x_{A}(\fst z) : \emptyt$, a contradicton; if instead $x_{B} : B \to \emptyt$,
then $x_{B}(\snd z) : \emptyt$.  By the recursion principle for the coproduct,
then,
%\[
f(z) \defeq \rec{(A\to\emptyt)+(B\to\emptyt)}(
\emptyt,
\lam{x}x(\fst z),
\lam{x}x(\snd z)
)
:
(A \to \emptyt) + (B \to \emptyt) \to \emptyt
\]%
Discharging the assumption that $A \times B$ is inhabited, we have
%\[
f : 
A \times B \to (A \to \emptyt) + (B \to \emptyt) \to \emptyt
\]%
So
%\[
\mathsf{swap}(A\times B, (A\to\emptyt)+(B\to\emptyt), \emptyt, f)
:
(A \to \emptyt) + (B \to \emptyt) 
\to 
A \times B 
\to \emptyt
\]% *)
  Goal (~ A + ~ B) -> ~ (A * B).
  Proof.
    unfold not.
    intros H x.
    apply H.
    destruct x.
    constructor.
    exact fst.
  Qed.

End Ex12.

(**
%\exerdone{1.13}{57}%
Using propositions-as-types, derive the double negation of the
principle of excluded middle, %i.e.~prove% 
%\emph{not (not ($P$ or not $P$))}%. *)

Section Ex13.
  Context (P : Type).

  (** 
%\soln%  
Suppose that $\lnot(P \lor \lnot P)$.  Then, assuming $P$, we have
$P \lor \lnot P$ by disjunction introduction, a contradiction.  Hence
$\lnot P$.  But disjunction introduction on this again gives $P \lor \lnot P$,
a contradiction.  So we must reject the remaining assumption, giving
$\lnot\lnot(P \lor \lnot P)$.


In type-theoretic terms, the initial assumption is that $g : P + (P \to
\emptyt) \to \emptyt$.  Assuming $p : P$, disjunction introduction results in
$\inl(p) : P + (P \to \emptyt)$.  But then $g(\inl(p)) : \emptyt$, so we
discharge the assumption of $p : P$ to get
%\[
\lam{p:P}g(\inl(p)) : P \to \emptyt
\]%
Applying disjunction introduction again leads to contradiction, as
%\[
g(\inr(\lam{p:P}g(\inl(p)))) : \emptyt
\]%
So we must reject the assumption of $\lnot( P \lor \lnot P)$, giving the
result:
%\[
\lam{g:P + (P \to \emptyt) \to \emptyt}g(\inr(\lam{p:P}g(\inl(p)))) 
: 
(P + (P \to \emptyt) \to \emptyt) \to \emptyt
\]%
Finally, in Coq, *)


  Goal ~ ~ (P + ~P).
  Proof.
    unfold not.
    intro H.
    apply H.
    right.
    intro p.
    apply H.
    left.
    apply p.
  Qed.

End Ex13.

(** 
%\exerdone{1.14}{57}%  
Why do the induction principles for identity types not allow
us to construct a function $f : \prd{x:A}\prd{p:x=x}(p = \refl{x})$ with the
defining equation
%\[
f(x, \refl{x}) \defeq \refl{\refl{x}}\qquad?
\]% *)

(** %\soln%
To attempt to define this function by path induction, we'd need a
family
%\[
  C \defeq \lam{x}{y}{p}(p = \refl{\refl{x}})
\]%
and a function
%\[
 c : \prd{x:A}(p = \refl{\refl{x}})
\]%
But there is not always such a function $c$, since it is not always the case
that there is only one path in $x = x$.
Because of the possiblity of nontrivial homotopies, one might fail to have $(p = p) = (p = \refl{x})$.

Attempting this proof in Coq would go as
[[
Definition f : forall (A : Type) (x : A) (p : x = x), p = 1.
intros. path_induction.
exact 1.
]]
%\noindent%
which returns the error message
[[
The term "1" has type "p = p" while it is expected to have type "p = 1".
]]
%\noindent%
*)


(** %\exerdone{1.15}{57}% 
Show that indiscernability of identicals follows from path induction.*)

(** %\soln%
    Consider some family $C : A \to \UU$, and define
    %\[
    D : \prd{x, y : A} (x =_{A} y) \to \UU,
    \qquad\qquad
    D(x, y, p) \defeq C(x) \to C(y)
    \]%
    Note that we have the function
    %\[
    \lam{x}\idfunc{C(x)} : 
    \prd{x:A} C(x) \to C(x)
    \equiv
    \prd{x:A} D(x, x, \refl{x}) 
    \]%
    So by path induction there is a function
    %\[
    f : 
    \prd{x, y : A} \prd{p : x =_{A} y} D(x, y, p)
    \equiv
    \prd{x, y : A} \prd{p : x =_{A} y} C(x) \to C(y)
    \]%
    such that
    %\[
    f(x, x, \refl{x}) \defeq \idfunc{C(x)}
    \]%
    But this is just the statement of the indiscernability of identicals: for every
    such family $C$, there is such an $f$.
 *)
