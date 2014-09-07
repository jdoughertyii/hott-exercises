(* begin hide *)
Require Export HoTT Ch04.
(* end hide *)
(** printing <~> %\ensuremath{\eqvsym}% **)
(** printing == %\ensuremath{\sim}% **)
(** printing ^-1 %\ensuremath{^{-1}}% **)
(** * Induction *)

(** %\exerdone{5.1}{175}%
Derive the induction principle for the type $\lst{A}$ of lists from its
definition as an inductive type in %\S5.1%.
*)

(** %\soln%
The induction principle constructs an element $f : \prd{\ell:\lst{A}} P(\ell)$
for some family $P : \lst{A} \to \UU$.  The constructors for $\lst{A}$ are
$\nil : \lst{A}$ and $\cons : A \to \lst{A} \to \lst{A}$, so the hypothesis for
the induction principle is given by
%\[
  d : P(\nil) 
      \to \left(\prd{h:A} \prd{t:\lst{A}}P(t) \to P(\cons(h, t))\right)
      \to \prd{\ell:\lst{A}}P(\ell)
\]%
So, given a $p_{n} : P(\nil)$ and a function $p_{c} : \prd{h:A} \prd{t:\lst{A}}
P(t) \to P(\cons(h, t))$, we obtain a function $f : \prd{\ell:\lst{A}}P(\ell)$
with the following computation rules:
%\begin{align*}
  f(\nil) &\defeq p_{n} \\
  f(\cons(h, t)) &\defeq p_{c}(h, t, f(t))
\end{align*}%
In Coq we can just use the pattern-matching syntax.
*)

Module Ex1.

  Section Ex1. 
    Variable A : Type.
    Variable P : list A -> Type.
    Hypothesis d : P nil 
                   -> (forall h t, P t -> P (cons h t))
                   -> forall l, P l.
    Variable p_n : P nil.
    Variable p_c : forall h t, P t -> P (cons h t).

    Fixpoint f (l : list A) : P l :=
      match l with
        | nil => p_n
        | cons h t => p_c h t (f t)
      end.
    End Ex1.
End Ex1.

(** %\exerdone{5.2}{175}% 
Construct two functions on natural numbers which satisfy the same recurrence
$(e_{z}, e_{s})$ but are not definitionally equal.
*)

(** %\soln%
Let $C$ be any type, with $c : C$ some element.  The constant function
$f' \defeq \lam{n}c$ is not definitionally equal to the function
defined recursively by
%\begin{align*}
  f(0) &\defeq c \\
  f(\suc(n)) &\defeq f(n)
\end{align*}%
However, they both satisfy the same recurrence; namely, $e_{z} \defeq c$ and
$e_{s} \defeq \lam{n}\idfunc{C}$.
*)

Module Ex2.
Section Ex2.
  Variables (C : Type) (c : C).

  Definition f (n : nat) := c.
  Fixpoint f' (n : nat) :=
    match n with
      | O => c
      | S n' => f' n'
    end.

  Theorem ex5_2_O : f O = f' O.
  Proof.
    reflexivity.
  Qed.
  
  Theorem ex5_2_S : forall n, f (S n) = f' (S n).
  Proof.
    intros. unfold f, f'.
    induction n. reflexivity. apply IHn.
  Qed.
End Ex2.
End Ex2.

(** %\exerdone{5.3}{175}% 
Construct two different recurrences $(e_{z}, e_{s})$ on the same type $E$ which
are both satisfied by the same function $f : \N \to E$.
*)

(** %\soln%
From the previous exercise we have the recurrences
%\[
  e_{z} \defeq c
  \qquad\qquad
  e_{s} \defeq \lam{n}\idfunc{C}
\]%
which give rise to the same function as the recurrences
%\[
  e'_{z} \defeq c
  \qquad\qquad
  e'_{s} \defeq \lam{n}\lam{x}c
\]%
Clearly $f \defeq \lam{n}c$ satisfies both of these recurrences.
However, suppose that $c, c' : C$ are such that $c \neq c'$.  Then
$\lam{n}\lam{x} \neq \lam{n}\idfunc{C}$, so $e_{s} \neq e'_{s}$, so
the recurrences are not equal.
*)

Module Ex3.
Section Ex3.
  Variables (C : Type) (c c' : C) (p : ~ (c = c')).
  
  Definition ez := c.
  Definition es (n : nat) (x : C) := x.
  Definition ez' := c.
  Definition es' (n : nat) := fun (x : C) => c.
  
  Theorem f_O : Ex2.f C c O = ez.
  Proof.
    reflexivity.
  Defined.
  Theorem f_S : forall n, Ex2.f C c (S n) = es n (Ex2.f C c n).
  Proof.
    reflexivity.
  Defined.
    
  Theorem f_O' : Ex2.f C c O = ez'.
  Proof.
    reflexivity.
  Defined.
  Theorem f_S' : forall n, Ex2.f C c (S n) = es' n (Ex2.f C c n).
  Proof.
    reflexivity.
  Defined.

  Theorem ex5_3 : ~ ((ez, es) = (ez', es')).
  Proof.
    intro q. apply (ap snd) in q. simpl in q. unfold es, es' in q.
    assert (idmap = fun x:C => c) as r.
    apply (apD10 q O).
    assert (c' = c) as s.
    apply (apD10 r). 
    symmetry in s.
    contradiction p.
  Defined.

End Ex3.
End Ex3.


(** %\exerdone{5.4}{175}% 
Show that for any type family $E : \bool \to \UU$, the induction operator
%\[
  \ind{\bool}(E) : 
  (E(0_{\bool}) \times E(1_{\bool}))
  \to
  \prd{b : \bool} E(b)
\]%
is an equivalence.
*)

(** %\soln%
For a quasi-inverse, suppose that $f : \prd{b:\bool} E(b)$.  To provide an
element of $E(0_{\bool}) \times E(1_{\bool})$, we take the pair $(f(0_{\bool}),
f(1_{\bool}))$.  For one direction around the loop, consider an element
$(e_{0}, e_{1})$ of the domain.  We then have
%\[
  \left(
    \ind{\bool}(E, e_{0}, e_{1}, 0_{\bool}),
    \ind{\bool}(E, e_{0}, e_{1}, 1_{\bool})
  \right)
  \equiv
  ( e_{0}, e_{1} )
\]%
by the computation rule for $\ind{\bool}$.  For the other direction, suppose
that $f : \prd{b:\bool} E(b)$, so that once around the loop gives
$\ind{\bool}(E, f(0_{\bool}), f(1_{\bool}))$.  Suppose that $b : \bool$.  Then
there are two cases:
 - $b \equiv 0_{\bool}$ gives $\ind{\bool}(E, f(0_{\bool}), f(1_{\bool}),
   0_{\bool}) \equiv f(0_{\bool})$
 - $b \equiv 1_{\bool}$ gives $\ind{\bool}(E, f(0_{\bool}), f(1_{\bool}),
   1_{\bool}) \equiv f(1_{\bool})$
by the computational rule for $\ind{\bool}$.  By function extensionality, then,
the result is equal to $f$.
*)

Definition Bool_rect_uncurried (E : Bool -> Type) : 
  (E false) * (E true) -> (forall b, E b).
  intros p b. destruct b; [apply (snd p) | apply (fst p)].
Defined.

Definition Bool_rect_uncurried_inv (E : Bool -> Type) : 
  (forall b, E b) -> (E false) * (E true).
  intro f. split; [apply (f false) | apply (f true)].
Defined.

Theorem ex5_4 (E : Bool -> Type) : IsEquiv (Bool_rect_uncurried E).
Proof.
  refine (isequiv_adjointify _ (Bool_rect_uncurried_inv E) _ _);
    unfold Bool_rect_uncurried, Bool_rect_uncurried_inv.
  intro f. apply path_forall; intro b. destruct b; reflexivity.
  intro p. apply eta_prod.
Qed.

(** %\exerdone{5.5}{175}% 
Show that the analogous statement to Exercise 5.4 for $\N$ fails.
*)

(** %\soln%
The analogous statement is that
%\[
  \ind{\N}(E) : \left(E(0) \times \prd{n:\N}E(n) \to E(\suc(n))\right)
  \to
  \prd{n:\N}E(n)
\]%
is an equivalence.  To show that it fails, note that an element of the domain
is a recurrence $(e_{z}, e_{s})$.  Recalling the solution to Exercise 5.3, we
have recurrences $(e_{z}, e_{s})$ and $(e'_{z}, e'_{s})$ such that $(e_{z},
e_{s}) \neq (e'_{z}, e'_{s})$, but such that $\ind{\N}(E, e_{z}, e_{s}) =
\ind{\N}(E, e'_{z}, e'_{s})$.  Suppose for contradiction that
$\ind{\N}(E)$ has a quasi-inverse $\ind{\N}^{-1}(E)$.  Then 
%\[
  (e_{z}, e_{s}) 
  =
  \ind{\N}^{-1}(E, \ind{\N}(E, e_{z}, e_{s}))
  =
  \ind{\N}^{-1}(E, \ind{\N}(E, e'_{z}, e'_{s}))
  =
  (e'_{z}, e'_{s}) 
\]%
The first and third equality are from the fact that a quasi-inverse is a left
inverse.  The second comes from the fact that $\ind{\N}(E)$ sends the two
recurrences to the same function.  So we have derived a contradiction.
*)

Definition nat_rect_uncurried (E : nat -> Type) :
  (E O) * (forall n, E n -> E (S n)) -> forall n, E n.
  intros p n. induction n. apply (fst p). apply (snd p). apply IHn.
Defined.

Theorem ex5_5 : ~ IsEquiv (nat_rect_uncurried (fun _ => Bool)).
Proof.
  intro e. destruct e.
  set (ez := (Ex3.ez Bool true)).
  set (es := (Ex3.es Bool)).
  set (ez' := (Ex3.ez' Bool true)).
  set (es' := (Ex3.es' Bool true)).
  assert ((ez, es) = (ez', es')) as H.
  transitivity (equiv_inv (nat_rect_uncurried (fun _ => Bool) (ez, es))).
  symmetry. apply eissect.
  transitivity (equiv_inv (nat_rect_uncurried (fun _ => Bool) (ez', es'))).
  apply (ap equiv_inv). apply path_forall; intro n. induction n.
    reflexivity.
    simpl. rewrite IHn. unfold Ex3.es, Ex3.es'. induction n; reflexivity.
  apply eissect.
  assert (~ ((ez, es) = (ez', es'))) as nH.
    apply (Ex3.ex5_3 Bool true false). apply true_ne_false.
    contradiction nH.
Qed.
                                  

(** %\exer{5.6}{175}% 
Show that if we assume simple instead of dependent elimination for $\w$-types,
the uniqueness property fails to hold.  That is, exhibit a type satisfying the
recursion principle of a $\w$-type, but for which functions are not determined
uniquely by their recurrence.
*)

(** %\exer{5.7}{175}% 
Suppose that in the ``inductive definition'' of the type $C$ at the beginning
of %\S5.6%, we replace the type $\N$ by $\emptyt$.  Analogously to
5.6.1, we might consider a recursion principle for this type with hypothesis
%\[
  h : (C \to \emptyt) \to (P \to \emptyt) \to P.
\]%
Show that even without a computation rule, this recursion principle is
inconsistent, %i.e.~it% allows us to construct an element of $\emptyt$.
*)

(** %\soln%
The associated recursion principle is
%\[
  \rec{C} : \prd{P:\UU} ((C \to \emptyt) \to (P \to \emptyt) \to P) \to C \to P
\]%
*)


(** %\exer{5.8}{175}% 
Consider now an ``inductive type'' $D$ with one constructor $\mathsf{scott} :
(D \to D) \to D$.  The second recursor for $C$ suggested in %\S5.6% leads to
the following recursor for $D$:
%\[
  \rec{D} : \prd{P:\UU} ((D \to D) \to (D \to P) \to P) \to D \to P
\]%
with computation rule $\rec{D}(P, h, \mathsf{scott}(\alpha)) \equiv h(\alpha,
(\lam{d}\rec{D}(P, h, \alpha(d))))$. Show that this also leads to a
contradiction.
*)

(** %\exerdone{5.9}{176}% 
Let $A$ be an arbitrary type and consider generally an ``inductive definition''
of a type $L_{A}$ with constructor $\mathsf{lawvere}:(L_{A} \to A) \to L_{A}$.
The second recursor for $C$ suggested in %\S5.6% leads to the following
recursor for $L_{A}$:
%\[
  \rec{L_{A}} : \prd{P:\UU} ((L_{A} \to A) \to P) \to L_{A} \to P
\]%
with computation rule $\rec{L_{A}}(P, h, \mathsf{lawvere}(\alpha)) \equiv
h(\alpha)$.  Using this, show that $A$ has a _fixed-point property_, %i.e.~for%
every function $f : A \to A$ there exists an $a : A$ such that $f(a) = a$.  In
particular, $L_{A}$ is inconsistent if $A$ is a type without the fixed-point
property, such as $\emptyt$, $\bool$, $\N$.
*)

(** %\soln%
This is an instance of Lawvere's fixed-point theorem, which says that in a
cartesian closed category, if there is a point-surjective map $T \to A^{T}$,
then every endomorphism $f : A \to A$ has a fixed point.  Working at an
intuitive level, the recursion principle ensures that we have the required
properties of a point-surjective map in a CCC.  In particular, we have the map
$\phi : (L_{A} \to A) \to A^{L_{A} \to A}$ given by
%\[
  \phi \defeq 
  \lam{f : L_{A} \to A}{\alpha : L_{A} \to A}f(\mathsf{lawvere}(\alpha))
\]%
and for any $h : A^{L_{A} \to A}$, we have
%\[
  \phi(\rec{L_{A}}(A, h))
  \equiv
  \lam{\alpha : L_{A} \to A}\rec{L_{A}}(A, h, \mathsf{lawvere}(\alpha))
  \equiv                 
  \lam{\alpha : L_{A} \to A}h(\alpha)
  =
  h
\]%
So we can recap the proof of Lawvere's fixed-point theorem with this $\phi$.
Suppose that $f : A \to A$, and define
%\begin{align*}
  q &\defeq \lam{\alpha:L_{A} \to A}f(\phi(\alpha, \alpha)) 
     : (L_{A} \to A) \to A \\
  p &\defeq \rec{L_{A}}(A, q) 
     : L_{A} \to A
\end{align*}%
so that $p$ lifts $q$:
%\[
  \phi(p)
  \equiv
  \lam{\alpha : L_{A} \to A}\rec{L_{A}}(A, q, \mathsf{lawvere}(\alpha))
  \equiv
  \lam{\alpha : L_{A} \to A}q(\alpha)
  =
  q
\]%
This make $\phi(p, p)$ a fixed point of $f$:
%\[
  f(\phi(p, p))
  = (\lam{\alpha : L_{A} \to A}f(\phi(\alpha, \alpha)))(p) 
  = q(p) 
  = \phi(p, p) 
\]%
*)

Definition onto {X Y} (f : X -> Y) := forall y : Y, {x : X & f x = y}.

Lemma LawvereFP {X Y} (phi : X -> (X -> Y)) : 
  onto phi -> forall (f : Y -> Y), {y : Y & f y = y}.
Proof.
  intros Hphi f.
  set (q := fun x => f (phi x x)).
  set (p := Hphi q). destruct p as [p Hp].
  exists (phi p p).
  change (f (phi p p)) with ((fun x => f (phi x x)) p).
  change (fun x => f (phi x x)) with q.
  symmetry. apply (apD10 Hp).
Defined.

Module Ex9.
Section Ex9.

Variable (L A : Type).
Variable lawvere : (L -> A) -> L.
Variable rec : forall P, ((L -> A) -> P) -> L -> P.
Hypothesis rec_comp : forall P h alpha, rec P h (lawvere alpha) = h alpha.

Definition phi : (L -> A) -> ((L -> A) -> A) :=
  fun f alpha => f (lawvere alpha).

Theorem ex5_9 : forall (f : A -> A), {a : A & f a = a}.
Proof.
  intro f. apply (LawvereFP phi).
  intro q. exists (rec A q). unfold phi.
  change q with (fun alpha => q alpha).
  apply path_forall; intro alpha. apply rec_comp.
Defined.

End Ex9.
End Ex9.

(** %\exerdone{5.10}{176}% 
Continuing from Exercise 5.9, consider $L_{\unit}$, which is not obviously
inconsistent since $\unit$ does have the fixed-point property.  Formulate an
induction principle for $L_{\unit}$ and its computation rule, analogously to
its recursor, and using this, prove that it is contractible.
*)

(** %\soln%
The induction principle for $L_{\unit}$ is
%\[
  \ind{L_{\unit}} 
  : \prd{P : L_{\unit} \to \UU} 
    \left(\prd{\alpha : L_{\unit} \to \unit} P(\mathsf{lawvere}(\alpha))\right)
    \to \prd{\ell : L_{\unit}}P(\ell)
\]%
and it has the computation rule
%\[
  \ind{L_{\unit}}(P, f, \mathsf{lawvere}(\alpha)) \equiv f(\alpha)
\]%
for all $f : \prd{\alpha : L_{\unit} \to \unit} P(\mathsf{lawvere}(\alpha))$
and $\alpha : L_{\unit} \to \unit$.

Let ${!} : L_{\unit} \to \unit$ be the unique terminal arrow.  I claim that
$L_{\unit}$ is contractible with center $\mathsf{lawvere}({!})$.  By
$\ind{L_{\unit}}$, it suffices to show that $\mathsf{lawvere}({!}) =
\mathsf{lawvere}(\alpha)$ for any $\alpha : L_{\unit} \to \unit$.  And by the
universal property of the terminal object, $\alpha = {!}$, so we're done.
*)

Module Ex10.
Section Ex10.

Variable L : Type.
Variable lawvere : (L -> Unit) -> L.

Variable indL : forall P, (forall alpha, P (lawvere alpha)) -> forall l, P l.
Hypothesis ind_comp : forall P f alpha, indL P f (lawvere alpha) = f alpha.

Theorem ex5_10 : Contr L.
Proof.
  apply (BuildContr L (lawvere (fun _ => tt))).
  apply indL; intro alpha.
  apply (ap lawvere).
  apply allpath_hprop.
Defined.

End Ex10.
End Ex10.

(** %\exerdone{5.11}{176}% 
In %\S5.1% we defined the type $\lst{A}$ of finite lists of elements of some
type $A$.  Consider a similiar inductive definition of a type $\lost{A}$, whose
only constructor is
%\[
  \cons : A \to \lost{A} \to \lost{A}.
\]%
Show that $\lost{A}$ is equivalent to $\emptyt$.
*)

(** %\soln%
Consider the recursor for $\lost{A}$, given by
%\[
  \rec{\lost{A}} : \prd{P : \UU} (A \to \lost{A} \to P \to P) \to \lost{A} \to P
\]%
with computation rule
%\[
  \rec{\lost{A}}(P, f, \cons(h, t)) \equiv f(h, \rec{\lost{A}}(P, f, t))
\]%
Now $\rec{\lost{A}}(\emptyt, \lam{a}{\ell}\idfunc{\emptyt}) : \lost{A} \to
\emptyt$, so $\lnot \lost{A}$ is inhabited, thus $\lost{A} \eqvsym \emptyt$.
*)

Theorem not_equiv_empty (A : Type) : ~ A -> (A <~> Empty).
Proof.
  intro nA. refine (equiv_adjointify nA (Empty_rect (fun _ => A)) _ _);
  intro; contradiction.
Defined.

Module Ex11.

Inductive lost (A : Type) := cons : A -> lost A -> lost A.

Theorem ex5_11 (A : Type) : lost A <~> Empty.
Proof.
  apply not_equiv_empty.
  intro l.
  apply (lost_rect A). auto. apply l.
Defined.

End Ex11.

