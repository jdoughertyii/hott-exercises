(* begin hide *)
Require Export HoTT Ch02.
(* end hide *)
(** printing <~> %\ensuremath{\eqvsym}% **)
(** printing == %\ensuremath{\sim}% **)
(** printing ^-1 %\ensuremath{^{-1}}% **)
(** * Sets and logic *)

Notation Brck Q := (merely Q).

(** %\exerdone{3.1}{127}%  
Prove that if $A \eqvsym B$ and $A$ is a set, then so is $B$.
*)

(** %\soln%
Suppose that $A \eqvsym B$ and that $A$ is a set.  Since $A$ is a set, $x =_{A}
y$ is a mere proposition.  And since $A \eqvsym B$, this means that $x =_{B} y$
is a mere proposition, hence that $B$ is a set.

Alternatively, we can unravel some definitions.  By assumption we have $f : A
\eqvsym B$ and
%\[
  g : \isset(A) \equiv \prd{x, y:A}\prd{p,q : x=y} (p = q)
\]%
Now suppose that $x, y : B$ and $p, q : x = y$.  Then $f^{-1}(x),
f^{-1}(y) : A$ and $f^{-1}(p), f^{-1}(q) : f^{-1}(x) =
f^{-1}(y)$, so
%\[
  f\!\left(g(f^{-1}(x), f^{-1}(y), f^{-1}(p), f^{-1}(q))\right) 
  : 
    f(f^{-1}(p)) = f(f^{-1}(q))
\]%
Since $f^{-1}$ is a quasi-inverse of $f$, we have the homotopy $\alpha :
\prd{a:A} (f(f^{-1}(a)) = a)$, thus
%\[
  \alpha_{x}^{-1} \ct 
  f\!\left(g(f^{-1}(x), f^{-1}(y), f^{-1}(p), f^{-1}(q))\right) 
  \ct \alpha_{y}
  :
  p = q
\]%
So we've constructed an element of
%\[
  \isset(B) : \prd{x, y : B} \prd{p, q : x = y} (p = q)
\]%
*)

Theorem ex3_1 (A B : Type) `{Univalence} : A <~> B -> IsHSet A -> IsHSet B.
Proof.
  intros f g.
  apply equiv_path_universe in f.
  rewrite <- f.
  apply g.
Defined.

Theorem ex3_1' (A B : Type) : A <~> B -> IsHSet A -> IsHSet B.
Proof.
  intros f g x y.
  apply hprop_allpath. intros p q.
  assert (ap f^-1 p = ap f^-1 q). apply g.
  apply ((ap (ap f^-1))^-1 X).
Defined.


(** %\exerdone{3.2}{127}%
Prove that if $A$ and $B$ are sets, then so is $A + B$.
*)

(** %\soln%
Suppose that $A$ and $B$ are sets.  Then for all $a, a' : A$ and $b, b': B$, $a
= a'$ and $b = b'$ are contractible.  Given the characterization of the path
space of $A+B$ in \S2.12, it must also be contractible.  Hence $A + B$ is a
set.

More explicitly, suppose that $z, z' : A + B$ and $p, q : z = z'$.  By
induction, there are four cases.
 - $z \equiv \inl(a)$ and $z' \equiv \inl(a')$.  Then $(z = z') \eqvsym (a = a')$, and since $A$ is a set, $a = a'$ is contractible, so $(z = z')$ is as well.
 - $z \equiv \inl(a)$ and $z' \equiv \inr(b)$.  Then $(z = z') \eqvsym \emptyt$, so $p$ is a contradiction.
 - $z \equiv \inr(b)$ and $z' \equiv \inl(a)$.  Then $(z = z') \eqvsym \emptyt$, so $p$ is a contradiction.
 - $z \equiv \inr(b)$ and $z' \equiv \inr(b')$.  Then $(z = z') \eqvsym (b = b')$, and since $B$ is a set, this type is contractible.
So $z = z'$ is contractible, making $A + B$ a set.
*)
  
Theorem ex3_2 (A B : Type) : IsHSet A -> IsHSet B -> IsHSet (A + B).
Proof.
  intros f g.
  intros z z'. apply hprop_allpath. intros p q.
  assert ((path_sum z z')^-1 p = (path_sum z z')^-1 q).
  pose proof ((path_sum z z')^-1 p).
  destruct z as [a | b], z' as [a' | b']. 
  apply f. contradiction. contradiction. apply g.
  apply ((ap (path_sum z z')^-1)^-1 X).
Defined.

(** %\exerdone{3.3}{127}%
Prove that if $A$ is a set and $B : A \to \UU$ is a type family such that
$B(x)$ is a set for all $x:A$, then $\sm{x:A}B(x)$ is a set.
*)

(** %\soln%
At this point the pattern in these proofs is relatively obvious: show
that the path space of the combined types is determined by the path
spaces of the base types, and then apply the fact that the base types
are sets.  So here we suppose that $w w' : \sm{x:A} B(x)$, and that $p
q : (w = w')$.  Now
%\[
  (w = w') \eqvsym \sm{p : \fst(w) = \fst(w')} p_{*}(\snd(w)) = \snd(w')
\]%
by Theorem 2.7.2. Since $A$ is a set, $\fst(w) = \fst(w')$ is
contractible, so $(w = w') \eqvsym ((\refl{\fst(w)})_{*}(\snd(w)) =
\snd(w')) \equiv (\snd(w) = \snd(w'))$ by Lemma 3.11.9.  And since $B$
is a set, this too is contractible, making $w = w'$ contractible and
$\sm{x:A} B(x)$ a set.
*)

Theorem ex3_3 (A : Type) (B : A -> Type) : 
  IsHSet A -> (forall x:A, IsHSet (B x)) -> IsHSet {x : A & B x}.
Proof.
  intros f g. 
  intros w w'. apply hprop_allpath. intros p q.
  assert ((path_sigma_uncurried B w w')^-1 p = (path_sigma_uncurried B w w')^-1 q).
  apply path_sigma_uncurried. simpl.
  assert (p..1 = q..1). apply f. exists X. apply (g w'.1).
  apply ((ap (path_sigma_uncurried B w w')^-1)^-1 X).
Defined.
  

(** %\exerdone{3.4}{127}%
Show that $A$ is a mere proposition if and only if $A \to A$ is contractible.
*)

(** %\soln% 
For the forward direction, suppose that $A$ is a mere proposition.  Then by
Example 3.6.2, $A \to A$ is a mere proposition.  We also have $\idfunc{A} : A
\to A$ when $A$ is inhabited and $! : A \to A$ when it's not, so $A \to A$ is
contractible.

For the other direction, suppose that $A \to A$ is contractible and that $x y :
A$.  We have the functions $z \mapsto x$ and $z \mapsto y$, and since $A \to A$
is contractible these functions are equal.  $\happly$ then gives $x = y$, so
$A$ is a mere proposition.
*)

Theorem ex3_4 `{Funext} (A : Type) : IsHProp A <-> Contr (A -> A).
Proof.
  split; intro H'.

  (* forward *)
  exists idmap; intro f.
  apply path_forall; intro x. apply H'.

  (* backward *)
  apply hprop_allpath; intros x y.
  assert ((fun z:A => x) = (fun z:A => y)).
  destruct H'. transitivity center. 
  apply (contr (fun _ => x))^. apply (contr (fun _ : A => y)).
  apply (apD10 X x).
Defined.

(** %\exerdone{3.5}{127}%
Show that $\isprop(A) \eqvsym (A \to \iscontr(A))$.
*)

(** %\soln%
Lemma 3.3.3 gives us maps $\isprop(A) \to (A \to \iscontr(A))$ and $(A
\to \iscontr(A)) \to \isprop(A)$.  Note that $\iscontr(A)$ is a mere
proposition, so $A \to \iscontr(A)$ is as well.  $\isprop(A)$ is
always a mere proposition, so by Lemma 3.3.3 we have the equivalence.
*)

Module Ex5.

Theorem equiv_hprop_inhabited_contr `{Funext} (A : Type) 
  : IsHProp A <~> (A -> Contr A).
Proof.
  apply equiv_iff_hprop.
  apply contr_inhabited_hprop.
  apply hprop_inhabited_contr.
Defined.

End Ex5.

(** %\exerdone{3.6}{127}%
Show that if $A$ is a mere proposition, then so is $A + (\lnot A)$.
*)

(** %\soln%
Suppose that $A$ is a mere proposition, and that $x, y : A + (\lnot A)$.  By a
case analysis, we have
 - $x = \inl(a)$ and $y = \inl(a')$.  Then $(x = y) \eqvsym (a = a')$, and $A$ is a mere proposition, so this holds.
 - $x = \inl(a)$ and $y = \inr(f)$.  Then $f(a) : \emptyt$, a contradiction.
 - $x = \inr(f)$ and $y = \inl(a)$.  Then $f(a) : \emptyt$, a contradiction.
 - $x = \inr(f)$ and $y = \inr(f')$.  Then $(x = y) \eqvsym (f = f')$, and $\lnot A$ is a mere proposition, so this holds.
*)


Theorem ex3_6 `{Funext} {A} : IsHProp A -> IsHProp (A + ~A).
Proof.
  intro H'. 
  assert (IsHProp (~A)) as H''. 
  apply hprop_allpath. intros f f'. apply path_forall; intro x. contradiction.
  apply hprop_allpath. intros x y.
  destruct x as [a | f], y as [a' | f'].
  apply (ap inl). apply H'.
  contradiction.
  contradiction.
  apply (ap inr). apply H''.
Defined.

(** %\exerdone{3.7}{127}%
More generally, show that if $A$ and $B$ are mere propositions and $\lnot (A
\times B)$, then $A + B$ is also a mere proposition.
*)

(** %\soln%
Suppose that $A$ and $B$ are mere propositions with $f : \lnot (A \times B)$,
and let $x, y : A + B$.  Then we have cases:
 - $x = \inl(a)$ and $y = \inl(a')$.  Then $(x = y) \eqvsym (a = a')$, and $A$ is a mere proposition, so this holds.
 - $x = \inl(a)$ and $y = \inr(b)$.  Then $f(a, b) : \emptyt$, a contradiction.
 - $x = \inr(b)$ and $y = \inl(a)$.  Then $f(a, b) : \emptyt$, a contradiction.
 - $x = \inr(b)$ and $y = \inr(b')$.  Then $(x = y) \eqvsym (b = b')$, and $B$ is a mere proposition, so this holds.
*)

Theorem ex3_7 {A B} : IsHProp A -> IsHProp B -> ~(A * B) -> IsHProp (A+B).
Proof.
  intros HA HB f.
  apply hprop_allpath; intros x y.
  destruct x as [a | b], y as [a' | b'].
  apply (ap inl). apply HA.
  assert Empty. apply (f (a, b')). contradiction.
  assert Empty. apply (f (a', b)). contradiction.
  apply (ap inr). apply HB.
Defined.

(** %\exerdone{3.8}{127}%
Assuming that some type $\isequiv(f)$ satisfies
%\begin{itemize}
  \item[(i)] For each $f : A \to B$, there is a function $\qinv(f) \to \isequiv(f)$;
  \item[(ii)] For each $f$ we have $\isequiv(f) \to \qinv(f)$;
  \item[(iii)] For any two $e_{1}, e_{2} : \isequiv(f)$ we have $e_{1} = e_{2}$,
\end{itemize}%
show that the type $\brck{\qinv(f)}$ satisfies the same conditions and is
equivalent to $\isequiv(f)$.
*)

(** %\soln%
Suppose that $f : A \to B$.  There is a function $\qinv(f) \to \brck{\qinv(f)}$
by definition.  Since $\isequiv(f)$ is a mere proposition (by iii), the
recursion principle for $\brck{\qinv(f)}$ gives a map $\brck{\qinv(f)} \to
\isequiv(f)$, which we compose with the map from (ii) to give a map
$\brck{\qinv(f)} \to \qinv(f)$.  Finally, $\brck{\qinv(f)}$ is a mere
proposition by construction.  Since $\brck{\qinv(f)}$ and $\isequiv(f)$ are
both mere propositions and logically equivalent, $\brck{\qinv(f)} \eqvsym
\isequiv(f)$ by Lemma 3.3.3.
*)

Section Exercise3_8.

Variables (E Q : Type).
Hypothesis H1 : Q -> E.
Hypothesis H2 : E -> Q.
Hypothesis H3 : forall e e' : E, e = e'.

Definition ex3_8_i : Q -> (Brck Q) := tr.

Definition ex3_8_ii : (Brck Q) -> Q.
  intro q. apply H2. apply (@Trunc_rect -1 Q).
  intro q'. apply hprop_allpath. apply H3.
  apply H1. apply q.
Defined.

Theorem ex3_8_iii : forall q q' : Brck Q, q = q'.
  apply allpath_hprop.
Defined.

Theorem ex3_8_iv : (Brck Q) <~> E.
  apply @equiv_iff_hprop.
  apply hprop_allpath. apply ex3_8_iii.
  apply hprop_allpath. apply H3.
  apply (H1 o ex3_8_ii).
  apply (ex3_8_i o H2).
Defined.


  
End Exercise3_8. 

(** %\exerdone{3.9}{127}%
Show that if $\LEM{}$ holds, then the type $\prop \defeq \sm{A:\UU}\isprop(A)$
is equivalent to $\bool$.
*)

(** %\soln%
Suppose that 
%\[
  f : \prd{A:\UU}\left(\isprop(A) \to (A + \lnot A)\right)
\]%
To construct a map $\prop \to \bool$, it suffices to consider an element of the
form $(A, g)$, where $g : \isprop(A)$.  Then $f(g) : A + \lnot A$, so we have
two cases:
  - $f(g) \equiv \inl(a)$, in which case we send it to $1_{\bool}$, or
  - $f(g) \equiv \inr(a)$, in which case we send it to $0_{\bool}$.
To go the other way, note that $\LEM{}$ splits $\prop$ into two equivalence
classes (basically, the true and false propositions), and $\unit$ and $\emptyt$
are in different classes.  Univalence quotients out these classes, leaving us
with two elements.  We'll use $\unit$ and $\emptyt$ as representatives, so we
send $0_{\bool}$ to $\emptyt$ and $1_{\bool}$ to $\unit$.

Coq has some trouble with the universes here, so we have to specify that we want [(Unit : Type)] and [(Empty : Type)]; otherwise we get the [Type0] versions.
*)

Section Exercise3_9.

Hypothesis LEM : forall (A : Type), IsHProp A -> (A + ~A).

Definition ex3_9_f (P : {A:Type & IsHProp A}) : Bool :=
  match (LEM P.1 P.2) with
    | inl a => true
    | inr a' => false
  end.

Lemma hprop_Unit : IsHProp (Unit : Type).
  apply hprop_inhabited_contr. intro u. apply contr_unit.
Defined.

Definition ex3_9_inv (b : Bool) : {A : Type & IsHProp A} :=
  match b with
    | true => @existT Type IsHProp (Unit : Type) hprop_Unit
    | false => @existT Type IsHProp (Empty : Type) hprop_Empty
  end.

Theorem ex3_9 `{Univalence} : {A : Type & IsHProp A} <~> Bool.
Proof.
  refine (equiv_adjointify ex3_9_f ex3_9_inv _ _).
  intro b. unfold ex3_9_f, ex3_9_inv.
  destruct b. 
    simpl. destruct (LEM (Unit:Type) hprop_Unit). 
      reflexivity.
      contradiction n. exact tt.
    simpl. destruct (LEM (Empty:Type) hprop_Empty).
      contradiction. reflexivity.
  intro w. destruct w as [A  p]. unfold ex3_9_f, ex3_9_inv.
    simpl. destruct (LEM A p) as [x | x]. 
    apply path_sigma_uncurried. simpl.
    assert ((Unit:Type) = A).
      assert (Contr A). apply contr_inhabited_hprop. apply p. apply x.
      apply equiv_path_universe. apply equiv_inverse. apply equiv_contr_unit.
    exists X. induction X. simpl. 
    assert (IsHProp (IsHProp (Unit:Type))). apply HProp_HProp. apply X.
    apply path_sigma_uncurried. simpl.
    assert ((Empty:Type) = A).
      apply equiv_path_universe. apply equiv_iff_hprop.
        intro z. contradiction.
        intro a. contradiction.
    exists X. induction X. simpl.
    assert (IsHProp (IsHProp (Empty:Type))). apply HProp_HProp. apply X.
Qed.

End Exercise3_9.

(** %\exerdone{3.10}{127}%
Show that if $\UU_{i+1}$ satisfies $\LEM{}$, then the canonical inclusion
$\prop_{\UU_{i}} \to \prop_{\UU_{i+1}}$ is an equivalence.
*)

(** %\soln%
If $\LEM{i+1}$ holds, then $\LEM{i}$ holds as well.  For suppose that
$A : \UU_{i}$ and $p : \isprop(A)$.  Then we also have $A :
\UU_{i+1}$, so $\LEM{i+1}(A, p) : A + \lnot A$, establishing
$\LEM{i}$.  By the previous exercise, then, $\prop_{\UU_{i}} \eqvsym
\bool \eqvsym \prop_{\UU_{i+1}}$.

Since Coq doesn't let the user access the [Type]${}_{i}$ hierarchy,
there's not much to do here.  This is really more of a ``proof by
contemplation'' anyway.
*)


(** %\exerdone{3.11}{127}%
Show that it is not the case that for all $A : \UU$ we have $\brck{A} \to A$.
*)

(** %\soln%
We can essentially just copy Theorem 3.2.2.  Suppose given a function $f :
\prd{A:\UU} \brck{A} \to A$, and recall the equivalence $e : \bool \eqvsym
\bool$ from Exercise 2.13 given by $e(1_{\bool}) \defeq 0_{\bool}$ and
$e(0_{\bool}) = 1_{\bool}$.  Then $\ua(e) : \bool = \bool$, $f(\bool)
: \brck{\bool} \to \bool$, and
%\[
  \mapdepfunc{f}(\ua(e)) : 
  \transfib{A \mapsto (\brck{A} \to A)}{\ua(e)}{f(\bool)} = f(\bool)
\]%
So for $u : \brck{\bool}$,
%\[
  \happly(\mapdepfunc{f}(\ua(e)), u) : 
  \transfib{A \mapsto (\brck{A} \to A)}{\ua(e)}{f(\bool)}(u) = f(\bool)(u)
\]%
and by 2.9.4, we have
%\[
  \transfib{A \mapsto (\brck{A} \to A)}{\ua(e)}{f(\bool)}(u) 
  =
  \transfib{A \mapsto A}{\ua(e)}{f(\bool)(\transfib{\lvert \blank
  \rvert}{\ua(e)^{-1}}{u}})
\]%
But, any two $u, v : \brck{A}$ are equal, since $\brck{A}$ is contractible.  So
$\transfib{\lvert\blank\rvert}{\ua(e)^{-1}}{u} = u$, and so
%\[
  \happly(\mapdepfunc{f}(\ua(e)), u) : 
  \transfib{A \mapsto A}{\ua(e)}{f(\bool)(u)}
  = f(\bool)(u)
\]%
and the propositional computation rule for $\ua$ gives
%\[
  \happly(\mapdepfunc{f}(\ua(e)), u) : 
  e(f(\bool)(u)) = f(\bool)(u)
\]%
But $e$ has no fixed points, so we have a contradiction.
*)

Lemma negb_no_fixpoint : forall b, ~ (negb b = b).
Proof.
  intros b H. destruct b; simpl in H.
    apply (false_ne_true H).
    apply (true_ne_false H).
Defined.

(*
Theorem ex3_11 `{Univalence} : ~ (forall A, Brck A -> A).
Proof.
  intro f.
  assert (forall b, negb (f Bool b) = f Bool b). intro b.
  assert (transport (fun A => Brck A -> A) (path_universe negb) (f Bool) b
          =
          f Bool b).
  apply (apD10 (apD f (path_universe negb)) b).
  assert (transport (fun A => Brck A -> A) (path_universe negb) (f Bool) b
          =
          transport idmap (path_universe negb) 
                    (f Bool (transport (fun A => Brck A) 
                                       (path_universe negb)^
                                       b))).
  apply (@transport_arrow Type0 (fun A => Brck A) idmap).
  rewrite X in X0.
  assert (b = (transport (fun A : Type => Brck A) (path_universe negb) ^ b)).
  apply allpath_hprop. rewrite <- X1 in X0. symmetry in X0.
  assert (transport idmap (path_universe negb) (f Bool b) = negb (f Bool b)).
  apply transport_path_universe. rewrite X2 in X0. apply X0.
  apply (@negb_no_fixpoint (f Bool (min1 true))). 
  apply (X (min1 true)).
Qed.
*)
  
 
(** %\exerdone{3.12}{127}%
Show that if $\LEM{}$ holds, then for all $A : \UU$ we have $\bbrck{\brck{A}
\to A}$.
*)

(** %\soln%
Suppose that $\LEM{}$ holds, and that $A : \UU$.  By $\LEM{}$, either $\brck{A}$
or $\lnot\brck{A}$.   If the
former, then we can use the recursion principle for $\brck{A}$ to construct a
map to $\bbrck{\brck{A} \to A}$, then apply it to the element of $\brck{A}$.
So we need a map $A \to \bbrck{\brck{A} \to A}$, which is not hard to get:
%\[
  \lam{a:A}\left\lvert\lam{a':\brck{A}}a\right\rvert : A \to \bbrck{\brck{A} \to A}
\]%
If the latter, then we have the canonical map out of the empty type $\brck{A}
\to A$, hence we have $\bbrck{\brck{A} \to A}$.  
*)

Section Exercise3_12.

Hypothesis LEM : forall A, IsHProp A -> (A + ~A).

Theorem ex3_12 : forall A, Brck (Brck A -> A).
Proof.
  intro A.
  destruct (LEM (Brck A) _).
  strip_truncations. apply tr. intro a. apply t.
  apply tr. intro a. contradiction (n a).
Defined.

End Exercise3_12.



(** %\exerdone{3.13}{127}%
Show that the axiom
%\[
    \LEM{}': \prd{A:\UU} (A + \lnot A)
\]%
implies that for $X : \UU$, $A : X \to \UU$, and $P : \prd{x:X} A(x) \to \UU$,
if $X$ is a set, $A(x)$ is a set for all $x:X$, and $P(x, a)$ is a mere
proposition for all $x:X$ and $a:A(x)$, 
%\[
  \left(\prd{x:X}\left\lVert\sm{a:A(x)}P(x, a)\right\rVert\right)
  \to
  \left\lVert \sm{g:\prd{x:X}A(x)}\prd{x:X}P(x, g(x))\right\rVert.
\]%
*)

(** %\soln%
By Lemma 3.8.2, it suffices to show that for any set $X$ and any $Y : X \to
\UU$ such that $Y(x)$ is a set, we have
%\[
  \left(\prd{x:X}\brck{Y(x)}\right) \to \left\lVert\prd{x:X}Y(x)\right\rVert
\]%
Suppose that $f : \prd{x:X}\brck{Y(x)}$.  By $\LEM{}'$, either $Y(x)$ is
inhabited or it's not.  If it is, then $\LEM{}'(Y(x)) \equiv y : Y(x)$, and we
have
%\[
  \left\lvert\lam{x:X}y\right\rvert : \left\lVert \prd{x:X} Y(x) \right\rVert
\]%
Suppose instead that $\lnot Y(x)$ and that $x:X$.  Then $f(x) : \brck{Y(x)}$.
Since we're trying to derive a mere proposition, we can ignore this truncation
and suppose that $f(x) : Y(x)$, in which case we have a contradiction, and
we're done.

The reason we can ignore the truncation (and apply [strip_truncations] in Coq)
in hypotheses is given by the reasoning in the previous Exercise.  If the
conclusion is a mere proposition, then the recursion principle for
$\brck{Y(x)}$ allows us to construct an arrow out of $\brck{Y(x)}$ if we have
one from $Y(x)$.
*)
  
Definition AC := forall X A P,
  IsHSet X -> (forall x, IsHSet (A x)) -> (forall x a, IsHProp (P x a))
  -> ((forall x:X, Brck {a:A x & P x a}) 
      -> Brck {g : forall x, A x & forall x, P x (g x)}).

Definition AC_prod := forall (X : hSet) (Y : X -> Type),
  (forall x, IsHSet (Y x)) -> 
  ((forall x, Brck (Y x)) -> Brck (forall x, Y x)).

Lemma hprop_is_hset (A : Type) : IsHProp A -> IsHSet A.
Proof.
  typeclasses eauto.
Defined.

  
Lemma AC_equiv_AC_prod `{Funext} : AC <~> AC_prod.
Proof.
  apply equiv_iff_hprop; unfold AC, AC_prod.

  (* forward *)
  intros AC HX Y HY f.
  
  transparent assert (He : (
    Brck ({g : forall x, Y x & forall x, (fun x a => Unit) x (g x)})
    <~> 
    Brck (forall x, Y x)
  )).
  apply equiv_iff_hprop. 
  intro w. strip_truncations. apply tr. apply w.1.
  intro g. strip_truncations. apply tr. exists g. intro x. apply tt.

  apply He. clear He. apply (AC _ Y (fun x a => Unit)). apply HX. apply HY.
  intros. apply hprop_Unit. intros. 
  assert (y : Brck (Y x)) by apply f. strip_truncations.
  apply tr. exists y. apply tt.

  (* back *)
  intros AC_prod X A P HX HA HP f.

  transparent assert (He: (
    Brck (forall x, {a : A x & P x a}) 
    <~> 
    Brck {g : forall x, A x & forall x, P x (g x)}
  )).
  apply equiv_iff_hprop.
  intros. strip_truncations. apply tr. exists (fun x => (X0 x).1).
  intro x. apply (X0 x).2.
  intros. strip_truncations. apply tr. intro x. apply (X0.1 x; X0.2 x). 

  apply He. clear He. 
  apply (AC_prod (default_HSet X HX) (fun x => {a : A x & P x a})).
  intros. apply ex3_3. apply (HA x). intro a.
  apply hprop_is_hset. apply (HP x a).
  intro x. apply (f x).
Defined.

Section Exercise3_13.

Hypothesis LEM' : forall A, A + ~A.

Theorem ex3_13 `{Funext} : AC.
Proof.
  apply AC_equiv_AC_prod. intros X Y HX HY.
  apply tr. intros. 
  destruct (LEM' (Y x)). apply y.
  assert (Brck (Y x)) as y'. apply HY.
  assert (~ Brck (Y x)) as nn. intro p. strip_truncations. contradiction.
  contradiction nn.
Defined.

End Exercise3_13.

(** %\exerdone{3.14}{127}%
Show that assuming $\LEM{}$, the double negation $\lnot\lnot A$ has the same
universal property as the propositional truncation $\brck{A}$, and is therefore
equivalent to it.  
*)

(** %\soln%
Suppose that $a : \lnot\lnot A$ and that we have some function $g : A \to B$,
where $B$ is a mere proposition, so $p : \isprop(B)$.  We can construct a
function $\lnot \lnot A \to \lnot \lnot B$ by using contraposition twice,
producing $g'': \lnot \lnot A \to \lnot \lnot B$
%\[
    g''(h) \defeq 
    \lam{f : \lnot B}h(\lam{a:A}f(g(a))) 
\]%
$\LEM{}$ then allows us to use double negation elimination to produce a map
$\lnot \lnot B \to B$.  Suppose that $f : \lnot \lnot B$.  Then we have
$\LEM{}(B, p) : B + \lnot B$, and in the left case we can produce the witness,
and in the right case we use $f$ to derive a contradiction.  Explicitly, we
have $\ell : \lnot \lnot B \to B$ given by
%\[
  \ell(f) \defeq 
  \rec{B + \lnot\lnot B}(B, \idfunc{B}, f, \LEM{}(B, p))
\]%
The computation rule does not hold judgementally for $g'' \circ \ell$.  I don't
see that it can, given the use of $\LEM{}$.  Clearly it does hold
propositionally, if one takes $\lvert a \rvert' \defeq \lam{f}f(a)$ to be the
analogue of the constructor for $\brck{A}$; for any $a : A$, we have $g(a) :
B$, and the fact that $B$ is a mere proposition ensures that $(g'' \circ
\ell)(\lvert a \rvert') = g(a)$.
*)

Section Exercise3_14.

Hypothesis LEM : forall A, IsHProp A -> (A + ~A).

Definition Brck' (A : Type) := ~ ~ A.
Definition min1' {A : Type} (a : A) : Brck' A := fun f => f a.

Definition contrapositive {A B : Type} : (A -> B) -> (~ B -> ~ A).
  intros. intro a. apply X0. apply X. apply a.
Defined.

Definition DNE {B : Type} `{IsHProp B} : ~ ~ B -> B.
  intros. destruct (LEM B IsHProp0). apply b. contradiction X.
Defined.

Definition trunc_rect' {A B : Type} (g : A -> B) : IsHProp B -> Brck' A -> B.
  intros HB a. apply DNE. apply (contrapositive (contrapositive g)). apply a.
Defined.

End Exercise3_14.

(** %\exerdone{3.15}{128}%
Show that if we assume propositional resizing, then the type
%\[
  \prd{P:\prop}\left((A \to P) \to P\right)
\]%
has the same universal property as $\brck{A}$.
*)

(** %\soln%
Let $A:\UU_{i}$, so that for $\brck{A}'' \defeq \prd{P:\prop_{\UU_{i}}} ((A \to
P) \to P)$ we have $\brck{A}'' : \UU_{i+1}$.  By propositional resizing,
however, we have a corresponding $\brck{A}'' : \UU_{i}$.  To construct an arrow
$\brck{A}'' \to B$, suppose that $f : \brck{A}''$ and $g : A \to B$.  Then
$f(B, g) : B$.  So $\lam{f}\tilde{f}(B, g) : \brck{A}'' \to B$, where
$\tilde{f}$ is the image of $f$ under the inverse of the canonical inclusion
$\prop_{\UU_{i}} \to \prop_{\UU_{i+1}}$.

To show that the computation rule holds, let
%\[
  \lvert a \rvert'' \defeq \lam{P}{f}f(a) : \prd{P:\prop}\left((A \to P) \to P
  \right)
\]%
We need to show that $(\lam{f}\tilde{f}(B, g))(\lvert a \rvert'') \equiv g(a)$.
Assuming that propositional resizing gives a judgemental equality, we have
%\begin{align*}
  (\lam{f}\tilde{f}(B, g))(\lvert a \rvert '')
  &\equiv
  (\lam{f}\tilde{f}(B, g))(\lam{P}{f}f(a))
  \\&\equiv
  (\lam{P}{f}f(a))(B, g)
  \\&\equiv
  g(a)
\end{align*}%
*)

Definition Brck'' (A : Type) := forall (P : hProp), ((A -> P) -> P).
Definition min1'' {A : Type} (a : A) := fun (P : hProp) (f : A -> P) => f a.

Definition trunc_rect'' {A B : Type} (g : A -> B) : IsHProp B -> Brck'' A -> B.
  intros p f.
  apply (f (hp B p)). apply g.
Defined.



(** %\exerdone{3.16}{128}%
Assuming $\LEM{}$, show that double negation commutes with universal
quantification of mere propositions over sets.  That is, show that if $X$ is a
set and each $Y(x)$ is a mere proposition, then $\LEM{}$ implies
%\[
  \left(\prd{x:X}\lnot\lnot Y(x)\right) 
  \eqvsym
  \left(\lnot\lnot\prd{x:X} Y(x)\right).
\]%
*)

(** %\soln%
Each side is a mere proposition, since one side is a dependent function into a
mere proposition and the other is a negation.  So we just need to show that
each implies the other.  From left to right we use the fact that $\LEM{}$
is equivalent to double negation to obtain $\prd{x:X}Y(x)$, and double negation
introduction is always allowed, giving the right side.  For the other direction
we do the same.
*)

Section Exercise3_16.

Hypothesis LEM : forall A, IsHProp A -> (A + ~ A).

Theorem ex3_16 `{Funext} (X : hSet) (Y : X -> Type) :
  (forall x, IsHProp (Y x)) -> 
  (forall x, ~ ~ Y x) <~> ~ ~ (forall x, Y x).
Proof.
  intro HY. apply equiv_iff_hprop; intro H'.
  
  intro f. apply f. intro x. 
  destruct (LEM (Y x)). 
    apply HY. apply y.
    contradiction (H' x).
  
  intro x. 
  destruct (LEM (Y x)). 
    apply HY. intro f. contradiction.
    assert (~ (forall x, Y x)). intro f. contradiction (f x).
    contradiction H'.
Qed.
   
End Exercise3_16.
  

(** %\exerdone{3.17}{128}%
Show that the rules for the propositional truncation given in %\S3.7% are
sufficient to imply the following induction principle: for any type family $B :
\brck{A} \to \UU$ such that each $B(x)$ is a mere proposition, if for every
$a:A$ we have $B(\lvert a \rvert)$, then for every $x : \brck{A}$ we have
$B(x)$.
*)

(** %\soln%
Suppose that $B : \brck{A} \to \UU$, $B(x)$ is a mere proposition for all $x :
\brck{A}$ and that $f : \prd{a:A} B(\lvert a \rvert)$. Suppose that $x
: \brck{A}$; we need to construct an element of $B(x)$.  By the
induction principle for $\brck{A}$, it suffices to exhibit a map $A
\to B(x)$.  So suppose that $a:A$, and we'll construct an element of
$B(x)$.  Since $\brck{A}$ is contractible, we have $p : \lvert a
\rvert = x$, and $p_{*}(f(a)) : B(x)$.
*)

Theorem ex3_17 (A : Type) (B : Brck A -> Type) :
  (forall x, IsHProp (B x)) -> (forall a, B (tr a)) -> (forall x, B x).
Proof.
  intros HB f. intro x.
  apply Trunc_rect. apply HB.
  intro a. apply (f a).
Defined.
  
  

(** %\exerdone{3.18}{128}%
Show that the law of excluded middle
%\[
  \LEM{} : \prd{A:\UU} \left( \isprop(A) \to (A + \lnot A)\right)
\]%
and the law of double negation
%\[
  \DN : \prd{A:\UU} \left( \isprop(A) \to (\lnot\lnot A \to A)\right)
\]%
are logically equivalent.
*)

(** %\soln%
For the forward direction, suppose that $\LEM{}$ holds, that $A : \UU$,
that $H : \isprop(A)$, and that $f : \lnot\lnot A$.  We then need to produce an
element of $A$.  We have $z \defeq \LEM{}(A, H) : A + \lnot A$, so we can
consider cases:
 - $z \equiv \inl(a)$, in which case we can produce $a$.
 - $z \equiv \inr(x)$, in which case we have $f(x) : \emptyt$, a contradiction.
giving the forward direction.

Suppose instead that $\DN$ holds, and we have $A : \UU$ and $H : \isprop(A)$.
We need to provide an element of $A + \lnot A$.  By Exercise 3.6, $A + \lnot A$
is a mere proposition, so by $\DN$, if we can give an element of $\lnot\lnot(A
+ \lnot A)$, then we'll get one of $A + \lnot A$.  In Exercise 1.13 we
constructed such an element, so producing that gives one of $A + \lnot A$, and
we're done.
*)

Theorem ex3_18 `{Funext} : 
  (forall A, IsHProp A -> (A + ~A)) <-> (forall A, IsHProp A -> (~ ~A -> A)).
Proof.
  split.
  intros LEM A H' f. destruct (LEM A H'). apply a. contradiction.
  intros DN A H'. apply (DN (A + ~A) (ex3_6 H')).
  exact (fun g : ~ (A + ~ A) => g (inr (fun a:A => g (inl a)))).
Qed.
  
  

(** %\exerdone{3.19}{128}%
Suppose $P : \mathbb{N} \to \UU$ is a decidable family of mere propositions.
Prove that
%\[
  \left\lVert \sm{n:\mathbb{N}} P(n) \right\rVert
  \to
  \sm{n:\mathbb{N}} P(n).
\]%
*)

(** %\soln%
Since $P : \mathbb{N} \to \UU$ is decidable, we have $f : \prd{n:\mathbb{N}}
(P(n) + \lnot P(n))$.  So if $\bbrck{\sm{n:\mathbb{N}}
P(n)}$ is inhabited, then there is some smallest $n$ such that $P(n)$.
It would be nice if we could define a function to return the
smallest $n$ such that $P(n)$.  But unbounded minimization isn't a
total function, so that won't obviously work.  Following the
discussion of Corollary 3.9.2, what we can do instead is to define some
%\[
  Q : \left(\sm{n:\mathbb{N}} P(n)\right) \to \UU
\]%
such that $\sm{w:\sm{n:\mathbb{N}} P(n)} Q(w)$ is a mere proposition.  Then
we can project out an element of $\sm{n:\mathbb{N}} P(n)$.

$Q(w)$ will be the proposition that $w$ is the smallest member of
$\sm{n\mathbb{N}}P(n)$.  Explicitly,
%\[
  Q(w) \defeq 
  \prd{w' : \sm{n:\mathbb{N}}P(n)} \fst(w) \leq \fst(w')
\]%
Then we have
%\[
  \sm{w : \sm{n : \mathbb{N}} P(n)} Q(w)
  \equiv
  \sm{w : \sm{n : \mathbb{N}} P(n)}
  \prd{w' : \sm{n:\mathbb{N}}P(n)} \fst(w) \leq \fst(w')
\]%
which we must show to be a mere proposition.  Suppose that $w$ and $w'$ are two
elements of this type.  By $\snd(w)$ and $\snd(w')$, we have $\fst(\fst(w)) \leq
\fst(\fst(w'))$ and $\fst(\fst(w')) \leq \fst(\fst(w))$, so $\fst(\fst(w)) = \fst(\fst(w'))$.  Since
$\mathbb{N}$ has decidable equality, $\fst(w) \leq \snd(w')$ is a mere
proposition for all $w$ and $w'$, meaning that $Q(w)$ is a mere proposition.
So $w = w'$, meaning that our type is contractible.

Now we can use the universal property of $\bbrck{\sm{n:\mathbb{N}}P(n)}$ to
construct an arrow into $\sm{w : \sm{n:\mathbb{N}} P(n)} Q(w)$ by way of a
function $\big(\sm{n:\mathbb{N}} P(n)\big) \to \sm{w : \sm{n:\mathbb{N}} P(n)}
Q(w)$.  So suppose that we have some element $w : \sm{n:\mathbb{N}} P(n)$.
Using bounded minimization, we can obtain the smallest element of $\sm{n:
\mathbb{N}} P(n)$ that's less than or equal to $w$, and this will in fact be
the smallest element _tout court_.  This means that it's a member of our
constructed type, so we've constructed a map
%\[
  \left\lVert \sm{n:\mathbb{N}} P(n) \right\rVert
  \to
  \sm{w:\sm{n:\mathbb{N}}P(n)}Q(w)
\]%
and projecting out gives the function in the statement.

*)

Local Open Scope nat_scope.

Fixpoint nat_code (n m : nat) :=
  match n, m with
    | O, O => Unit
    | S n', O => Empty
    | O, S m' => Empty
    | S n', S m' => nat_code n' m'
  end.

Fixpoint nat_r (n : nat) : nat_code n n :=
  match n with
    | O => tt
    | S n' => nat_r n'
  end.

Definition nat_encode (n m : nat) (p : n = m) : (nat_code n m)
  := transport (nat_code n) p (nat_r n).

Definition nat_decode : forall (n m : nat), (nat_code n m) -> (n = m).
Proof.
  induction n, m; intro.
  reflexivity. contradiction. contradiction.
  apply (ap S). apply IHn. apply X.
Defined.

Theorem equiv_path_nat : forall n m, (nat_code n m) <~> (n = m).
Proof.
  intros.
  refine (equiv_adjointify (nat_decode n m) (nat_encode n m) _ _).
  
  intro p. induction p. simpl.
  induction n. reflexivity. simpl.
  apply (ap (ap S) IHn).

  generalize dependent m.
  induction n. induction m.
  intro c. apply eta_unit.
  intro c. contradiction.
  induction m.
  intro c. contradiction.
  intro c. simpl. unfold nat_encode.
  refine ((transport_compose _ S _ _)^ @ _).
  simpl. apply IHn.
Defined.

Lemma Sn_neq_O : forall n, S n <> O.
Proof.
  intros n H. apply nat_encode in H. contradiction.
Defined.

Lemma plus_eq_O (n m : nat) : n + m = O -> (n = O) /\ (m = O).
Proof.
  destruct n.
  intro H. split. reflexivity. apply H.
  intro H. simpl in H. apply nat_encode in H. contradiction.
Defined.
  
Lemma le_trans : forall n m k, (n <= m) -> (m <= k) -> (n <= k).
Proof.
  intros n m k Hnm Hmk.
  destruct Hnm as [l p].
  destruct Hmk as [l' p'].
  exists (l + l').
  refine ((plus_assoc _ _ _)^ @ _).
  refine (_ @ p'). f_ap.
Defined.  

Lemma le_Sn_le (n m : nat) : S n <= m -> n <= m.
Proof.
  intro H. apply (le_trans n (S n) m). exists 1. apply (plus_1_r _)^. apply H.
Defined.
  
Lemma plus_cancelL : forall n m k, n + m = n + k -> m = k.
Proof.
  intro n. induction n. trivial.
  intros m k H.
  apply S_inj in H. apply IHn. apply H.
Defined.

Lemma le_antisymmetric (n m : nat) : (n <= m) -> (m <= n) -> (n = m).
Proof.
  intro H. destruct H as [k p].
  intro H. destruct H as [k' p'].
  transparent assert (q : (n + (k + k') = n + O)).
    refine ((plus_assoc _ _ _)^ @ _).
    refine ((ap (fun s => s + k') p) @ _).
    refine (_ @ (plus_O_r _)).
    apply p'.
  apply plus_cancelL in q.
  apply plus_eq_O in q.
  refine ((plus_O_r _) @ _).
  refine ((ap (plus n) (fst q))^ @ _).
  apply p.
Defined.
  
Lemma decidable_paths_nat : decidable_paths nat.
Proof.
  intros n m. 
  generalize dependent m.
  generalize dependent n.
  induction n, m.
  left. reflexivity.
  right. intro H. apply nat_encode in H. contradiction.
  right. intro H. apply nat_encode in H. contradiction.
  destruct (IHn m). 
    left. apply (ap S p).
    right. intro H. apply S_inj in H. contradiction.
Defined.

Lemma hset_nat : IsHSet nat.
Proof. apply hset_decidable. apply decidable_paths_nat. Defined.

Lemma hprop_le (n m : nat) : IsHProp (n <= m).
Proof.
  apply hprop_allpath. intros p q.
  refine (path_sigma_hprop _ _ _).
  intro k. apply hprop_allpath. refine set_path2. apply hset_nat.
  destruct p as [k p], q as [k' p']. simpl.
  apply (plus_cancelL n).
  apply (p @ p'^).
Defined.

Lemma hprop_dependent `{Funext} (A : Type) (P : A -> Type) :
  (forall a, IsHProp (P a)) -> IsHProp (forall a, P a).
Proof.
  intro HP. 
  apply hprop_allpath. intros p p'. apply path_forall; intro a. apply HP.
Defined.

Definition n_le_n (n : nat) : n <= n := (O; (plus_O_r n)^).
Definition n_le_Sn (n : nat) : n <= S n := (S O; (plus_1_r n)^).

Lemma Spred (n : nat) : (n <> O) -> S (pred n) = n.
Proof.
  induction n; intro H; [contradiction H|]; reflexivity.
Defined.

Lemma le_partitions (n : nat) : forall m, (m <= n) + (n <= m).
Proof.
  induction n.
  intro m. right. exists m. reflexivity.

  intro m.
  destruct (IHn m) as [IHnm | IHnm].
  left. apply (le_trans _ n). apply IHnm. apply n_le_Sn.
  destruct IHnm as [k p].
  destruct (decidable_paths_nat n m).
  left. exists 1. refine ((plus_1_r _)^ @ _). apply (ap S p0^).
  right. exists (pred k). refine ((plus_n_Sm _ _) @ _). refine (_ @ p).
  f_ap. apply Spred.
  intro H. apply n0.
  refine ((plus_O_r _) @ _). refine ((ap (plus n) H^) @ _). apply p.
Defined.


Lemma le_neq__lt (n m : nat) : (n <= m) -> (n <> m) -> (n < m).
Proof.
  intros H1 H2. destruct H1 as [k p].
  exists (pred k). refine (_ @ p). f_ap.
  apply Spred. intro Hk. apply H2. 
  refine (_ @ p). refine ((plus_O_r _) @ _). f_ap.
  apply Hk^.
Defined.

Lemma lt_partitions (n m : nat) : (n < m) + (n = m) + (m < n).
Proof.
  destruct (decidable_paths_nat n m).
  left. right. apply p.
  destruct (le_partitions n m).
  right. apply le_neq__lt. apply l. intro H. apply n0. apply H^.
  left. left. apply le_neq__lt. apply l. apply n0.
Defined.

Lemma p_nnp : forall P, P -> ~ ~ P.
Proof. auto. Defined.

Lemma n_nlt_n (n : nat) : ~ (n < n).
Proof.
  intros H. destruct H as [k p].
  apply (nat_encode (S k) O).
  apply (plus_cancelL n).
  apply (p @ (plus_O_r _)). 
Defined.

Lemma n_neq_Sn (n : nat) : n <> S n.
Proof.
  induction n.
  intro H. apply nat_encode in H. contradiction.
  intro H. apply IHn. apply S_inj in H. apply H.
Defined.

Lemma n_lt_Sm__n_le_m (n m : nat) : (n < S m) -> (n <= m).
Proof.
  intro H. destruct H as [k p]. exists k.
  apply S_inj. refine (_ @ p).
  apply plus_n_Sm.
Defined.

Lemma le_O (n : nat) : n <= O -> n = O.
Proof.
  intro H. destruct H as [k p].
  apply plus_eq_O in p. apply (fst p).
Defined.

Lemma lt_1 (n : nat) : n < 1 -> n = O.
Proof.
  intro H.
  apply le_O. apply n_lt_Sm__n_le_m. apply H.
Defined.

Lemma lt_le (n m : nat) : n < m -> n <= m.
Proof.
  intro H. destruct H as [k p].
  exists (S k). apply p.
Defined.

Lemma Sn_lt_Sm__n_lt_m (n m : nat) : S n < S m -> n < m.
Proof.
  intro H. destruct H as [k p]. exists k.
  simpl in p. apply S_inj in p. apply p.
Defined.

Lemma lt_neq (n m : nat) : n < m -> n <> m.
Proof.
  generalize dependent m.
  induction n.
  intros m H HX.
  destruct H as [k p]. simpl in p.
  apply (nat_encode (S k) O).
  apply (p @ HX^).

  induction m.
  intros H HX.
  apply (nat_encode (S n) O). apply HX.
  intros H Hx.
  apply Sn_lt_Sm__n_lt_m in H.
  apply IHn in H. apply H. apply S_inj. apply Hx.
Defined.
  
Lemma lt_trans (n m k : nat) : n < m -> m < k -> n < k.
Proof.
  intros H1 H2.
  destruct H1 as [l p], H2 as [l' p'].
  exists (l + S l').
  refine (_ @ p').
  change (S (l + S l')) with (S l + S l').
  refine ((plus_assoc _ _ _)^ @ _). f_ap.
Defined.
  
Lemma n_lt_Sn (n : nat) : n < S n.
Proof.
  exists O. apply (plus_1_r _)^.
Defined.

Lemma bound_up (n m : nat) : (n <= m) -> (n <> m) -> (S n <= m).
Proof.
  intros H1 H2.
  apply le_neq__lt in H1.
  destruct H1 as [k p]. exists k.
  refine ((plus_n_Sm _ _) @ _). apply p. apply H2.
Defined.

Lemma le_lt__lt (n m k : nat) : n <= m -> m < k -> n < k.
Proof.
  intros H1 H2.
  destruct (decidable_paths_nat n m).
  destruct H2 as [l q].
  exists l. refine (_ @ q). f_ap.
  apply (lt_trans _ m).
  apply le_neq__lt. apply H1. apply n0. apply H2.
Defined.

Lemma lt_le__lt (n m k : nat) : n < m -> m <= k -> n < k.
Proof.
  intros H1 H2.
  destruct (decidable_paths_nat m k).
  destruct H1 as [l q].
  exists l. refine (_ @ p). apply q.
  apply (lt_trans _ m).
  apply H1. apply le_neq__lt. apply H2. apply n0.
Defined.

Lemma le_eq__le (n m k : nat) : (n <= m) -> (m = k) -> (n <= k).
Proof.
  intros H1 H2.
  destruct H1 as [l p].
  exists l. apply (p @ H2).
Defined.

Lemma n_le_m__Sn_le_Sm (n m : nat) : n <= m -> (S n <= S m).
Proof.
  intro H. destruct H as [k p]. exists k. simpl. apply (ap S). apply p.
Defined.

Lemma Sn_le_Sm__n_le_m (n m : nat) : S n <= S m -> n <= m.
Proof.
  intro H. destruct H as [k p]. exists k.
  simpl in p. apply S_inj in p. apply p.
Defined.

Lemma n_nlt_O (n : nat) : ~ (n < O).
Proof.
  induction n. apply n_nlt_n.
  intro H. destruct H as [k p]. apply nat_encode in p. contradiction.
Defined.

Lemma O_lt_n (n : nat) : (n <> O) -> (O < n).
Proof.
  intro H.
  exists (pred n).
  apply Spred. apply H.
Defined.

Lemma n_lt_m__Sn_lt_Sm (n m : nat) : n < m -> S n < S m.
Proof.
  intro H. destruct H as [k p]. exists k. simpl. apply (ap S). apply p.
Defined.

Lemma n_lt_m__n_le_Sm (n m : nat) : n < m -> n <= S m.
Proof.
  intro H. destruct H as [k p].
  exists (S (S k)). apply (ap S) in p. refine (_ @ p).
  symmetry. apply plus_n_Sm.
Defined.


Lemma lt_bound_down (n m : nat) : n < S m -> (n <> m) -> n < m.
Proof.
  intros. destruct H as [k p].
  exists (pred k). refine ((plus_n_Sm _ _)^ @ _).
  refine ((plus_n_Sm _ _) @ _). apply S_inj. refine (_ @ p).
  refine ((plus_n_Sm _ _) @ _). f_ap. apply (ap S). apply Spred.
  intro H. apply X. apply S_inj. refine (_ @ p).
  refine (_ @ (plus_n_Sm _ _)). apply (ap S). refine ((plus_O_r _) @ _). f_ap.
  apply H^.
Defined.

Lemma lt_bound_up (n m : nat) : n < m -> (S n <> m) -> S n < m.
Proof.
  intros.
  destruct H as [k p]. exists (pred k). refine (_ @ p).
  refine ((plus_n_Sm _ _) @ _). f_ap. f_ap. apply Spred. intro H.
  apply X. refine (_ @ p). refine ((plus_1_r _) @ _). f_ap. f_ap. apply H^.
Defined.

Lemma pred_n_eq_O : forall n, pred n = O -> (n = O) + (n = 1).
Proof.
  induction n.
  intros. left. reflexivity.
  intros H. simpl in H. right. apply (ap S H).
Defined.

Lemma bound_down (n m : nat) : (n <= S m) -> (n <> S m) -> (n <= m).
Proof.
  intros H1 H2.
  apply le_neq__lt in H1.
  destruct H1 as [k p]. exists k.
  apply S_inj. refine ((plus_n_Sm _ _) @ _). apply p. apply H2.
Defined.

Lemma nle_lt (n m : nat) : ~ (n <= m) -> (m < n).
Proof.
  generalize dependent m.
  induction n.
  intros m H. assert Empty. apply H. exists m. reflexivity. contradiction.
  intros m H. destruct m. 
    exists n. reflexivity.
    apply n_lt_m__Sn_lt_Sm. apply IHn. intro H'. apply H.
    destruct H' as [k p]. exists k. simpl. apply (ap S). apply p.
Defined.

Lemma Sn_neq_n (n : nat) : S n <> n.
Proof.
  intro H.
  apply (nat_encode 1 0).
  apply (plus_cancelL n).
  refine ((plus_1_r _)^ @ _). refine (_ @ (plus_O_r _)).
  apply H.
Defined.

Lemma lt_antisymmetric (n m : nat) : n < m -> ~ (m < n).
Proof.
  intros H HX.
  destruct H as [k p], HX as [k' p'].
  transparent assert (H : (S k + S k' = O)).
  apply (plus_cancelL n). refine (_ @ (plus_O_r _)).
  refine (_ @ p'). refine ((plus_assoc _ _ _)^ @ _). f_ap.
  apply nat_encode in H. contradiction.
Defined.

Lemma lt_eq__lt (n m k : nat) : (n < m) -> (m = k) -> (n < k).
Proof.
  intros H1 H2.
  destruct H1 as [l p].
  exists l. refine (p @ _). apply H2.
Defined.

Lemma nlt_le (n m : nat) : ~ (n < m) -> (m <= n).
Proof.
  generalize dependent m.
  induction n.
  intros m H. destruct (decidable_paths_nat m O). exists O. refine (_ @ p).
  symmetry. apply plus_O_r.
  assert Empty. apply H. apply O_lt_n. apply n. contradiction.
  
  induction m.
  intro H. exists (S n). reflexivity.
  intro H. apply n_le_m__Sn_le_Sm. apply IHn.
  intro H'. apply H. apply n_lt_m__Sn_lt_Sm. apply H'.
Defined.
  
Lemma n_lt_m__Sn_le_m (n m : nat) : (n < m) -> (S n <= m).
Proof.
  intro H.
  apply n_lt_m__Sn_lt_Sm in H.
  apply n_lt_Sm__n_le_m in H.
  apply H.
Defined.

Lemma n_le_m__n_lt_Sm (n m : nat) : n <= m -> n < S m.
Proof.
  intro H.
  destruct H as [k p].
  exists k. refine ((plus_n_Sm _ _)^ @ _). f_ap.
Defined.

Section Exercise3_19.

Context {P : nat -> Type} {HP : forall n, IsHProp (P n)}
        {DP : forall n, P n + ~ P n}.

Local Definition Q (w : {n : nat & P n}) : Type := 
  forall w' : {n : nat & P n}, w.1 <= w'.1.

Lemma hprop_Q `{Funext} : forall w, IsHProp (Q w).
Proof.
  intro w. unfold Q. apply hprop_dependent. intro w'. apply hprop_le.
Defined.

Lemma hprop_sigma_Q `{Funext} : IsHProp {w : {n : nat & P n} & Q w}.
Proof.
  apply hprop_allpath. intros w w'.
  refine (path_sigma_hprop _ _ _). apply hprop_Q.
  apply path_sigma_hprop. apply le_antisymmetric.
  apply (w.2 w'.1). apply (w'.2 w.1).
Defined.

Definition bmin (bound : nat) : nat.
Proof.
  induction bound as [|z].
  destruct (DP O). apply O. apply 1.

  destruct (lt_partitions IHz (S z)) as [[Ho | Ho] | Ho].
  apply IHz.
  destruct (DP (S z)).
    apply (S z).
    apply (S (S z)).
  apply (S (S z)).
Defined.

Lemma bmin_correct_O (n : nat) : P O -> bmin n = O.
Proof.
  intro H.
  induction n. simpl. destruct (DP O). reflexivity. apply n in H. contradiction.
  simpl. rewrite IHn. reflexivity.
Defined.

Lemma bmin_correct_self_P (n : nat) : bmin n = n -> P n.
Proof.
  induction n.
  intros. simpl in H. 
  destruct (DP O). 
    apply p. 
    apply nat_encode in H. contradiction.
  intro H.
  simpl in H.
  destruct (lt_partitions (bmin n) (S n)) as [[Ho | Ho] | Ho]. 
  rewrite H in Ho. apply n_nlt_n in Ho. contradiction.
  destruct (DP (S n)). apply p.
  transparent assert (X : Empty).
    apply (n_neq_Sn (S n)). apply H^.
  contradiction.
  transparent assert (X : Empty).
    apply (n_neq_Sn (S n)). apply H^.
  contradiction.
Defined.

Lemma bmin_correct_bound (n : nat) : bmin n <= S n.
Proof.
  induction n.
  simpl.
  destruct (DP O). exists 1. reflexivity.
  exists O. apply plus_n_Sm.
  
  simpl.
  destruct (lt_partitions (bmin n) (S n)) as [[Ho | Ho] | Ho].
    apply (le_trans _ (S n)). apply IHn. apply n_le_Sn.
    destruct (DP (S n)).
      apply n_le_Sn.
      apply n_le_n.
    apply n_le_n.
Defined.
  
Lemma bmin_correct_nPn (n : nat) : bmin n = S n -> ~ P n.
Proof.
  induction n.
  intros H HX.
  apply (bmin_correct_O O) in HX.
  apply (nat_encode 1 O). refine (H^ @ _). refine (_ @ HX). reflexivity.

  intros H HX. simpl in H.
  destruct (lt_partitions (bmin n) (S n)) as [[Ho | Ho] | Ho].
  rewrite H in Ho. apply (n_nlt_n (S (S n))).
  apply (lt_trans _ (S n)). apply Ho. apply n_lt_Sn.
  destruct (DP (S n)).
  apply (n_neq_Sn (S n)). apply H.
  apply n0. apply HX.
  clear H.
  
  apply (n_nlt_n (bmin n)).
  apply (le_lt__lt _ (S n)).
  apply bmin_correct_bound.
  apply Ho.
Defined.

Lemma bmin_correct_success (n : nat) : bmin n < S n -> P (bmin n).
Proof.
  induction n.
  intro H. apply lt_1 in H. apply bmin_correct_self_P in H.
  apply ((bmin_correct_O _ H)^ # H).
  
  simpl.
  destruct (lt_partitions (bmin n) (S n)) as [[Ho | Ho] | Ho].
  intro H. apply IHn. apply Ho.
  destruct (DP (S n)). 
  intro H. apply p.
  intro H. apply n_nlt_n in H. contradiction.
  intro H. apply n_nlt_n in H. contradiction.
Defined.

Lemma bmin_correct_i (n : nat) : forall m, (m < n) -> (m < bmin n) -> ~ P m.
Proof.
  induction n.
  intros m H1 H2.
  apply n_nlt_O in H1. contradiction.
  
  induction m. intro H. clear H.
  destruct (decidable_paths_nat n O).
  (* Case: n = O *)
  (* we just want the contrapositive of bmin_correct_O *)
  intro H.
  apply (contrapositive (bmin_correct_O (S n))).
  intro H'. rewrite H' in H. apply n_nlt_n in H. contradiction.
  (* Case: n <> O *)
  intro H. apply IHn. apply O_lt_n. apply n0.
  simpl in H.
  destruct (lt_partitions (bmin n) (S n)) as [[Ho | Ho] | Ho].
  (* Case: bmin n < S n *)
  apply H.
  (* Case: bmin n = S n *)
  rewrite Ho. apply O_lt_n. apply Sn_neq_O.
  apply (lt_trans _ (S n)). apply O_lt_n. apply Sn_neq_O. apply Ho.

  intros H1. apply Sn_lt_Sm__n_lt_m in H1. simpl. 
  destruct (lt_partitions (bmin n) (S n)) as [[Ho | Ho] | Ho].
  (* Case: bmin n < S n *)
  intro H. apply IHn.
  destruct (decidable_paths_nat (bmin n) n).
  rewrite <- p. apply H. 
  apply lt_bound_down in Ho.
  apply (lt_trans _ (bmin n)). apply H. apply Ho. apply n0. apply H.
  
  (* Case: bmin n = S n *)
  intro H.
  destruct (decidable_paths_nat (S m) n).
  apply bmin_correct_nPn. rewrite p. apply Ho.
  apply lt_bound_up in H1. apply IHn. apply H1.
  apply (lt_trans _ n). apply H1. rewrite Ho. apply n_lt_Sn.
  apply n0.
  
  (* Case: bmin n > S n *)
  set (H := (bmin_correct_bound n)).
  assert Empty. apply (n_nlt_n (S n)).
  apply (lt_le__lt _ (bmin n)).
  apply Ho. apply H. contradiction.
Defined.

Lemma bmin_correct_i' (n : nat) : forall m, (m <= n) -> (m < bmin n) -> ~ P m.
Proof.
  intros m H.
  destruct (decidable_paths_nat m n).
  clear H.
  intro H. 
  set (H' := (bmin_correct_nPn n)). rewrite p. apply H'. clear H'.
  set (H' := (bmin_correct_bound n)). rewrite p in H.
  apply le_antisymmetric. apply H'. destruct H as [k q].
  exists k. refine ((plus_n_Sm _ _) @ _). apply q.

  apply le_neq__lt in H. generalize H. apply bmin_correct_i. apply n0.
Defined.

Lemma bmin_correct_leb (n : nat) : P n -> (bmin n <= n).
Proof.
  induction n.
  intro H. apply (bmin_correct_O O) in H.
  exists O. refine (_ @ H). symmetry. apply plus_O_r.

  intro H.
  simpl. destruct (lt_partitions (bmin n) (S n)) as [[Ho | Ho] | Ho].
  destruct Ho as [k p]. exists (S k). apply p.
  destruct (DP (S n)). exists O. symmetry. apply plus_O_r.
  apply n0 in H. contradiction.
  apply (le_trans _ (bmin n)).
  apply n_lt_m__Sn_le_m. apply Ho.
  apply (bmin_correct_bound n).
Defined.
  
  
Lemma bmin_correct_i_cp (n m : nat) : P m -> (bmin n <= m).
Proof.
  intro H.
  transparent assert (H' : (
  forall n m : nat, (m < n /\ m < bmin n) -> ~ P m
  )).
  intros n' m' H'. apply (bmin_correct_i n'). apply (fst H'). apply (snd H').
  transparent assert (H'' : (~ ~ P m)). apply p_nnp. apply H.
  apply (contrapositive (H' n m)) in H''.
  transparent assert (H''' : (sum (~ (m < n)) (~ (m < bmin n)))).
    destruct (lt_partitions n m) as [[Ho | Ho] | Ho].
    left. apply lt_antisymmetric. apply Ho.
    left. intro H'''. apply (n_nlt_n n). apply (lt_eq__lt m n m) in H'''.
    apply (n_nlt_n m) in H'''. contradiction.
    apply Ho.
    right. intro H'''.
    apply H''. split. apply Ho. apply H'''.
  destruct H'''; clear H'' H'.
  apply nlt_le in n0.
  apply nlt_le. intro H'.
  set (H'' := (bmin_correct_bound n)).
  transparent assert (Heq : (n = m)).
  apply le_antisymmetric. apply n0. apply n_lt_Sm__n_le_m.
  apply (lt_le__lt _ (bmin n) _). apply H'. apply H''.
  transparent assert (Hle : (m <= n)).
  exists O. refine (_ @ Heq^). symmetry. apply plus_O_r.
  generalize H. change (P m -> Empty) with (~ P m).
  apply (bmin_correct_i' n). apply Hle. apply H'.
  
  apply nlt_le in n0. apply n0.
Defined.

Lemma bmin_correct (bound : nat) : 
  {n : nat & P n /\ n <= bound} -> forall n, P n -> bmin bound <= n.
Proof.
  induction bound.
  intros w n p.
  destruct w as [w [a b]].
  apply le_O in b. 
  exists n. transitivity (O + n). f_ap. apply bmin_correct_O. apply (b # a).
  reflexivity.

  intros w n p. simpl.
  destruct (lt_partitions (bmin bound) (S bound)) as [[Ho | Ho] | Ho].
  (* bmin bound < S bound *)
  apply IHbound. exists (bmin bound). split.
  apply bmin_correct_success. apply Ho.
  destruct Ho as [k q]. exists k. apply S_inj. refine (_ @ q).
  refine ((plus_n_Sm _ _) @ _). reflexivity.
  apply p.
  
  (* bmin bound = S bound *)
  destruct w as [w [a b]].
  destruct (decidable_paths_nat w (S bound)).
  destruct (DP (S bound)).
  apply nlt_le. intro H.
  generalize p. change (P n -> Empty) with (~ P n).
  apply (bmin_correct_i' bound).
  apply n_lt_Sm__n_le_m. apply H. rewrite Ho. apply H.
  rewrite <- p0 in n0. apply n0 in a. contradiction.
  
  apply le_neq__lt in b.
  apply n_lt_Sm__n_le_m in b.
  transparent assert (Hlt : (w < bmin bound)).
    apply (lt_eq__lt _ (S bound)).
    apply n_le_m__n_lt_Sm. apply b. apply Ho^.
  assert Empty. generalize a. change (P w -> Empty) with (~ P w).
  apply (bmin_correct_i' bound). apply b. apply Hlt. contradiction. apply n0.
                      
  (* S bound < bmin bound *)
  set (H := (bmin_correct_bound bound)).
  apply (lt_le__lt _ _ (S bound)) in Ho.
  apply n_nlt_n in Ho. contradiction.
  apply H.
Defined.


Lemma ex3_19 `{Funext} : Brck {n : nat & P n} -> {n : nat & P n}.
Proof.
  intro w.
  apply (@pr1 _ Q).
  set (H' := hprop_sigma_Q).
  strip_truncations.
  transparent assert (w' : {n : nat & P n}).
  exists (bmin w.1).
  apply bmin_correct_success.
  apply n_le_m__n_lt_Sm. apply bmin_correct_leb. apply w.2.
  exists w'.
  unfold Q.
  intro w''.
  apply bmin_correct.
  exists w.1. split. apply w.2. apply n_le_n. apply w''.2.
Defined.

End Exercise3_19.

Local Close Scope nat_scope.
        
(** %\exerdone{3.20}{128}%
Prove Lemma 3.11.9(ii): if $A$ is contractible with center $a$, then
$\sm{x:A}P(x)$ is equivalent to $P(a)$.
*)

(** %\soln%
Suppose that $A$ is contractible with center $a$.  For the forward direction,
suppose that $w : \sm{x:A} P(x)$.  Then $\fst(w) = a$, since $A$ is
contractible, so from $\snd(w) : P(\fst(w))$ and the indiscernibility
of identicals, we have $P(a)$.  For the backward direction, suppose
that $p : P(a)$.  Then we have $(a, p) : \sm{x:A} P(x)$.

To show that these are quasi-inverses, suppose that $p : P(a)$.  Going backward
gives $(a, p) : \sm{x:A} P(x)$, and going forward we have
$(\contr_{a}^{-1})_{*}p$.  Since $A$ is contractible, $\contr_{a} =
\refl{a}$, so this reduces to $p$, as needed.
For the other direction, suppose that $w : \sm{x:X} P(x)$.  Going forward gives
$(\contr_{\fst(w)}^{-1})_{*}\snd(w) : P(a)$, and going back gives
%\[
  (a, (\contr_{\fst(w)}^{-1})_{*}\snd(w)) : \sm{x:A} P(x)
\]%
By Theoremm 2.7.2, it suffices to show that $a = \fst(w)$ and that
%\[
  (\contr_{\fst(w)})_{*}(\contr_{\fst(w)}^{-1})_{*} \snd(w) = \snd(w)
\]%
The first of these is given by the fact that $A$ is contractible.  The second
results from the functorality of transport.
*)

Theorem equiv_sigma_contr_base (A : Type) (P : A -> Type) (HA : Contr A) : 
  {x : A & P x} <~> P (center A).
Proof.
  refine (equiv_adjointify _ _ _ _).
  intro w. apply (transport _ (contr w.1)^). apply w.2.
  intro p. apply (center A; p).

  intro p. simpl. 
  assert (Contr (center A = center A)). apply contr_paths_contr.
  assert (contr (center A) = idpath). apply allpath_hprop.
  rewrite X0. reflexivity.

  intro w. apply path_sigma_uncurried.
  simpl. exists (contr w.1).
  apply transport_pV.
Defined.
  

(** %\exerdone{3.21}{128}%
Prove that $\isprop(P) \eqvsym (P \eqvsym \brck{P})$.
*)

(** %\soln%
$\isprop(P)$ is a mere proposition by Lemma 3.3.5.  $P \eqvsym \brck{P}$ is
also a mere proposition.  An equivalence is determined by its underlying
function, and for all $f, g : P \to \brck{P}$, $f = g$ by function
extensionality and the fact that $\brck{P}$ is a mere proposition.  Since each
of the two sides is a mere proposition, we just need to show that they imply
each other, by Lemma 3.3.3.  Lemma 3.9.1 gives the forward direction.  For the
backward direction, suppose that $e : P \eqvsym \brck{P}$, and let $x, y : P$.
Then $e(x) = e(y)$, since $\brck{P}$ is a proposition, and applying $e^{-1}$ to
each side gives $x = y$.  Thus $P$ is a mere proposition.
*)

Theorem ex3_21 `{Funext} (P : Type) : IsHProp P <~> (P <~> Brck P).
Proof.
  assert (IsHProp (P <~> Brck P)). apply hprop_allpath; intros e1 e2.
  apply path_equiv. apply path_forall; intro p.
  apply hprop_allpath. apply allpath_hprop.
  apply equiv_iff_hprop.

  intro HP. apply equiv_iff_hprop. apply tr.
  apply Trunc_rect. intro p. apply HP. apply idmap.
  
  intro e. apply hprop_allpath; intros x y.
  assert (e x = e y) as p. apply hprop_allpath. apply allpath_hprop.
  rewrite (eissect e x)^. rewrite (eissect e y)^.
  apply (ap e^-1 p). 
Defined.
  

(** %\exer{3.22}{128}%
As in classical set theory, the finite version of the axiom of choice is a
theorem.  Prove that the axiom of choice holds when $X$ is a finite type
$\Fin(n)$.
*)

(** %\soln%
We want to show that for all $n$, $A : \Fin(n) \to \UU$, and 
$P : \prd{m_{n} : \Fin(n)} A(m_{n}) \to \UU$, if $A$ is a family of sets and
$P$ a family of propositions, then
%\[
  \left(
    \prd{m_{n} : \Fin(n)} \left\lVert \sm{a:A(m_{n})} P(m_{n}, a)\right\rVert
  \right)
  \to
  \brck{
    \sm{g : \prd{m_{n} : \Fin(n)} A(m_{n})} \prd{m_{n} : \Fin(n)}
        P(m_{n}, g(m_{n}))
  }
\]%

We proceed by induction on $n$.  Note first that $\eqv{\Fin(0)}{\emptyt}$ and
that $\eqv{\Fin(n + 1)}{\Fin(n) + \unit}$, which follow quickly from the fact
that $\N$ is a set.  In particular, we'll use the equivalence which sends
$n_{n+1}$ to $\star$ and $m_{n+1}$ to $m_{n}$ for $m < n$.

For the base case, $n \equiv 0$, everything is easily provided by ex falso
quodlibet.  
For the induction step, we can define a new family of sets $A' : (\Fin(n) +
\unit) \to \UU$ as follows:
%\begin{align*}
  A'(z) &= \begin{cases}
             A(m_{n+1}) & \text{if $z \equiv m_{n}$} \\
             A(n_{n+1}) & \text{if $z \equiv \star$}
           \end{cases}
\end{align*}%
And if $e : \eqv{\Fin(n+1)}{\Fin(n) + \unit}$, then we clearly have
$h : \eqv{A(z)}{A'(e(z))}$ for all $z : \Fin(n+1)$.  Similarly, we can define
%\begin{align*}
  P'(z, a) &= \begin{cases}
                P(m_{n+1},  h^{-1}(a)) & \text{if $z \equiv m_{n}$} \\
                P(n_{n+1}, h^{-1}(a)) & \text{if $z \equiv \star$}
              \end{cases}
\end{align*}%
For which we clearly have $g : \eqv{P(z, a)}{P'(e(z), h(a))}$ for all $z$ and
$a$.  So, by the functorality of equivalence (Ex.%~%2.17), we have
%\[
  \eqv{
    \prd{m_{n+1} : \Fin(n + 1)} \brck{\sm{a : A(m_{n+1})} P(m_{n+1}, a)}
  }{
    \prd{z : \Fin(n) + \unit} \brck{\sm{a : A'(z)} P'(z, a)}
  }
\]%
But, since the induction principle for the sum type is an equivalence, we also
have
%\[
  \eqv{
    \prd{z : \Fin(n) + \unit} \brck{\sm{a : A'(z)} P'(z, a)}
  }{
    \left(\prd{z : \Fin(n)} \brck{\sm{a : A'(\inl(z))} P'(\inl(z), a)}\right)
    \times
    \left(\prd{z : \unit} \brck{\sm{a : A'(\inr(z))} P'(\inr(z), a)}\right)
  }
\]%
And to construct an arrow out of this, we just need to give an arrow out of
each one.  Now, by the same equivalences, we can rewrite the conclusion as
%\[
  \brck{
    \sm{g : \prd{z : \Fin(n) + \unit} A'(z)}
    \prd{z : \Fin(n) + \unit}
    P'(z, g(z))
  }
\]%
Using the universal property of $\Sigma$ types, we get
%\[
  \brck{
    \prd{z : \Fin(n) + \unit} \sm{a : A'(z)} P'(z, a)
  }
\]%
and the functorality of the induction principle for the sum gives
%\[
  \brck{
    \left(\prd{z : \Fin(n)} \sm{a : A'(\inl(z))} P'(\inl(z), a)\right)
    \times
    \left(\prd{z : \unit} \sm{a : A'(\inr(z))} P'(\inr(z), a)\right)
  }
\]%
Since this is only a finite product, we can take it outside of the truncation,
giving
%\[
  \brck{
    \prd{z : \Fin(n)} \sm{a : A'(\inl(z))} P'(\inl(z), a)
  }
    \times
  \brck{
    \prd{z : \unit} \sm{a : A'(\inr(z))} P'(\inr(z), a)
  }
\]%
and using the universal property of $\Sigma$ types to go back once more, we
finally arrive at
%\[
  \brck{
    \sm{g : \prd{z : \Fin(n)} A'(\inl(z))} 
    \prd{z : \Fin(n)} 
    P'(\inl(z), g(z))
  }
    \times
  \brck{
    \prd{z : \unit} 
    \sm{a : A'(\inr(z))}
    P'(\inr(z), a)
  }
\]%
Since each of the domain and codomain are products, we can produce the required
map by giving one between the first items of each product and one between the
second.  So first we need an arrow
%\[
  \prd{m_{n} : \Fin(n)} \brck{\sm{a : A'(\inl(m_{n}))} P'(\inl(m_{n}), a)}
  \to
  \brck{
    \sm{g : \prd{m_{n} : \Fin(n)} A'(\inl(m_{n}))}
    \prd{m_{n} : \Fin(n)}
    P'(\inl(m_{n}), g(m_{n}))
  }
\]%
but by definition of $A'$ and $P'$, this is just
%\[
  \prd{m_{n} : \Fin(n)} \brck{\sm{a : A(m_{n})} P(m_{n}, a)}
  \to
  \brck{
    \sm{g : \prd{m_{n} : \Fin(n)} A(m_{n})}
    \prd{m_{n} : \Fin(n)}
    P(m_{n}, g(m_{n}))
  }
\]%
which is the induction hypothesis. For the second map, we need
%\[
  \prd{z : \unit}\brck{\sm{a : A'(\inr(z))} P'(\inr(z), a)}
  \to
  \brck{\prd{z : \unit}\sm{a : A'(\inr(z))} P'(\inr(z), a)}
\]%
which by the computation rules for $A'$ and $P'$ is
%\[
  \left(\unit \to \brck{\sm{a : A(n_{n+1})} P(n_{n+1}, a)}\right)
  \to
  \brck{\unit \to \sm{a : A(n_{n+1})} P(n_{n+1}, a)}
\]%
and this is easily constructed using the recursor for truncation.
*)

Definition cardO : Fin O -> Empty.
Proof.
  intro w. destruct w as [n [k p]].
  apply plus_eq_O in p. apply (nat_encode (S k) O). apply (snd p).
Defined.

Theorem isequiv_cardO : IsEquiv cardO.
Proof.
  refine (isequiv_adjointify _ _ _ _).
  apply Empty_rect.

  (* Section *)
  intro w. contradiction.

  (* Retraction *)
  intro w. destruct w as [n [k p]].
  assert Empty.
  apply (nat_encode (S k) O).
  apply (@snd (n = O) _).
  apply plus_eq_O.
  apply p.
  contradiction.
Defined.
  
Definition cardF {n : nat} : Fin (S n) -> Fin n + Unit.
Proof.
  intro w. 
  destruct w as [m [k p]].
  destruct (decidable_paths_nat m n).
  right. apply tt.
  left. exists m. exists (pred k). 
  apply S_inj. refine (_ @ p).
  refine ((plus_n_Sm _ _) @ _). f_ap. f_ap. apply Spred.
  intro H. apply n0. apply S_inj. refine (_ @ p).
  refine ((plus_O_r _) @ _). refine ((plus_n_Sm _ _) @ _). f_ap. f_ap.
  apply H^.
Defined.

Lemma plus_cancelR (n m k : nat) : plus m n = plus k n -> m = k.
Proof.
  intro H.
  apply (plus_cancelL n).
  refine ((plus_comm _ _) @ _). refine (H @ _). apply (plus_comm _ _)^.
Defined.

Lemma hprop_lt (n m : nat) : IsHProp (lt n m).
Proof.
  apply hprop_allpath. intros x y.
  transparent assert (H : (
    forall k : nat, IsHProp ((n + S k)%nat = m)
  )).
  intro k. apply hprop_allpath. apply (@set_path2 nat hset_nat).
  apply path_sigma_hprop.
  destruct x as [x p], y as [y p'].
  simpl. apply S_inj. apply (plus_cancelL n). apply (p @ p'^).
Defined.

Lemma path_Fin (n : nat) (w w' : Fin n) : (w.1 = w'.1) -> w = w'.
Proof.
  intro p.
  destruct w as [m w], w' as [m' w'].
  simpl. apply path_sigma_uncurried. exists p.
  set (H := hprop_lt m' n).
  apply allpath_hprop.
Defined.

Theorem isequiv_cardF : forall n, IsEquiv (@cardF n).
Proof.
  intro n.
  refine (isequiv_adjointify _ _ _ _).

  (* inverse *)
  intro H. destruct H as [w | t]. destruct w as [m [k p]].
  exists m. exists (S k). refine ((plus_n_Sm _ _)^ @ _). apply (ap S). apply p.
  exists n. exists O. apply (plus_1_r _)^.

  (* Section *)
  intro H. destruct H as [w | t]. 
    
    (* w : Fin n *)
    destruct w as [m [k p]]. unfold cardF. simpl.
    destruct (decidable_paths_nat m n).
    assert Empty. apply (nat_encode (S k) O). apply (plus_cancelL m).
    refine (_ @ (plus_O_r _)). refine (_ @ p0^). apply p. contradiction.
    apply (ap inl). apply path_Fin. reflexivity.

    (* t : Unit *)
    unfold cardF. simpl. destruct (decidable_paths_nat n n). 
    apply (ap inr). apply contr_unit. contradiction (n0 1).

  (* Retraction *)
  intro w. destruct w as [m [k p]]. unfold cardF. simpl.
  destruct (decidable_paths_nat m n).
  apply path_Fin. apply p0^.
  apply path_Fin. reflexivity.
Defined.

Lemma eq_lt__lt (n m k : nat) : (n = m) -> (lt m k) -> (lt n k).
Proof.
  intros p w.
  destruct w as [l q].
  exists l. refine (_ @ q). f_ap.
Defined.

Lemma pred_inj (n m : nat) : n <> O -> m <> O -> (pred n = pred m) -> n = m.
Proof.
  intros Hn Hm H.
  refine ((Spred n Hn)^ @ _). refine (_ @ (Spred m Hm)).
  apply (ap S). apply H.
Defined.

Lemma pn_lt_n (n : nat) : n <> O -> (lt (pred n) n).
Proof.
  intro H. exists O. refine ((plus_1_r _)^ @ _). apply Spred. apply H.
Defined.

Lemma brck_equiv (A B : Type) : (A <~> B) -> (Brck A <~> Brck B).
Proof.
  intro e.
  apply equiv_iff_hprop.
  intro a'. strip_truncations. apply tr. apply e. apply a'.
  intro b'. strip_truncations. apply tr. apply e^-1. apply b'.
Defined.

Definition Book_2_15_6 (X : Type) (A : X -> Type) (P : forall x, A x -> Type) :
  (forall x, {a : A x & P x a}) 
  ->
  {g : forall x, A x & forall x, P x (g x)}.
Proof.
  intro f.
  exists (fun x => (f x).1).
  intro x. apply (f x).2.
Defined.

Theorem Book_2_15_7 `{Funext} (X : Type) (A : X -> Type) 
        (P : forall x, A x -> Type) 
  : IsEquiv (Book_2_15_6 X A P).
Proof.
  refine (isequiv_adjointify _ _ _ _).
  intros f x. apply (f.1 x; f.2 x).

  (* Section *)
  intro w. unfold Book_2_15_6.
  apply path_sigma_uncurried. simpl. exists 1.
  simpl. reflexivity.

  (* Retraction *)
  intro f. apply path_forall; intro x.
  unfold Book_2_15_6. simpl. apply eta_sigma.
Defined.


Theorem brck_functor_prod (A B : Type) : Brck (A * B) <~> Brck A * Brck B.
Proof.
  apply equiv_iff_hprop.
  intro x. split; strip_truncations; apply tr. apply (fst x). apply (snd x).
  intro x. destruct x as [a b]. strip_truncations. apply tr. apply (a, b).
Defined.

(* The induction step of the proof *)
Section ISFAC.
Context {n : nat} {A : Fin (S n) -> Type} {P : forall m, A m -> Type}.

Local Definition A' := A o (@equiv_inv _ _ cardF (isequiv_cardF n)).
Local Definition P' : forall m, A' m -> Type.
Proof.
  intros m a.
  refine (P _ _).
  apply (@equiv_inv _ _ cardF (isequiv_cardF n)).
  apply m. apply a.
Defined.

Theorem domain_trans `{Funext} :
  (forall m, Brck {a : A m & P m a})
  <~>
  (forall z, Brck {a : A ((@equiv_inv _ _ cardF (isequiv_cardF n)) (inl z))
                         & P ((@equiv_inv _ _ cardF (isequiv_cardF n)) (inl z)) a})
  *
  (forall z : Unit, Brck {a : A (n; (O; (plus_1_r _)^)) & 
                                P (n; (O; (plus_1_r _)^)) a}).
Proof.
  equiv_via (forall z, Brck {a : A' z & P' z a}).
  refine (equiv_functor_forall' _ _).
  apply equiv_inverse. apply (BuildEquiv _ _ cardF (isequiv_cardF n)).
  intro z.
  apply brck_equiv.
  refine (equiv_functor_sigma' _ _).
  unfold A'. unfold compose. apply equiv_idmap. 
  intro a. unfold P'. unfold compose. simpl. apply equiv_idmap.
  
  equiv_via (
    (forall z, Brck {a : A' (inl z) & P' (inl z) a})
    *
    (forall z, Brck {a : A' (inr z) & P' (inr z) a})
  ).
  apply equiv_inverse. 
  refine (equiv_sum_rect _).
  
  apply equiv_functor_prod'; apply equiv_idmap.
Defined.
  

Theorem codomain_trans `{Funext} :
  Brck {g : forall m, A m & forall m, P m (g m)}
  <~>
  Brck {g : forall z, (A o (@equiv_inv _ _ cardF (isequiv_cardF n)) o inl) z
            & forall z, 
                   P ((@equiv_inv _ _ cardF (isequiv_cardF n)) (inl z)) (g z)}
  *
  Brck (forall z : Unit, {a : A (n; (O; (plus_1_r _)^)) &
                                P (n; (O; (plus_1_r _)^)) a}).
Proof.
  equiv_via (Brck {g : forall z, A' z & forall z, P' z (g z)}).
  apply brck_equiv.
  refine (equiv_functor_sigma' _ _).
  refine (equiv_functor_forall' _ _).
  apply equiv_inverse. apply (BuildEquiv _ _ cardF (isequiv_cardF n)).
  intro z. apply equiv_idmap.
  intro g. refine (equiv_functor_forall' _ _).
  apply equiv_inverse. apply (BuildEquiv _ _ cardF (isequiv_cardF n)).
  intro z. apply equiv_idmap.
  
  equiv_via (Brck (forall z, {a : A' z & P' z a})).
  apply brck_equiv.
  apply equiv_inverse. 
  apply (BuildEquiv _ _ (Book_2_15_6 _ _ _) (Book_2_15_7 _ _ _)).
  
  equiv_via (Brck ((forall z, {a : A' (inl z) & P' (inl z) a})
                   *
                   (forall z, {a : A' (inr z) & P' (inr z) a}))).
  apply brck_equiv.
  apply equiv_inverse. refine (equiv_sum_rect _).
  
  equiv_via (Brck (forall z : Fin n, {a : A' (inl z) & P' (inl z) a}) 
             * 
             Brck (forall z : Unit, {a : A' (inr z) & P' (inr z) a})).
  apply brck_functor_prod.

  refine (equiv_functor_prod' _ _).
  apply brck_equiv.
  unfold A', P', compose.
  apply (BuildEquiv _ _ 
                    (Book_2_15_6 _ _ _) 
                    (Book_2_15_7 _ _ (fun z a => P (cardF^-1 (inl z)) a))).
  apply brck_equiv. apply equiv_idmap.
Defined.

End ISFAC.


Theorem finite_AC `{Funext} (n : nat) (A : Fin n -> Type) 
        (P : forall m, A m -> Type) : 
  (forall m, Brck {a : A m & P m a}) 
  -> Brck {g : forall m, A m & forall m, P m (g m)}.
Proof.
  induction n.
  intro H'. apply tr.
  exists (fun m : Fin 0 => Empty_rect (fun _ => A m) (cardO m)).
  intro m. contradiction (cardO m).

  intro f.
  apply domain_trans in f.
  destruct f as [fn f1].
  apply codomain_trans.
  split.
  apply (IHn _ ((fun z a =>
                 P ((@equiv_inv _ _ cardF (isequiv_cardF n)) (inl z)) a))).
  apply fn.
  set (z := tt).
  apply f1 in z. strip_truncations. apply tr. intro t. apply z.
Defined.

(**
There's also a shorter proof by way of Lemma 3.8.2.  It suffices to show 
for all $n : \N$ and $Y : \Fin(n) \to \UU$
%\[
  \left(\prd{m_{n} : \Fin(n)} \brck{Y(m_{n})}\right)
  \to
  \brck{\prd{m_{n} : \Fin(n)} Y(x)}
\]%
Things proceed by induction, as before.  For $n \equiv 0$ everything follows
from a contradiction.  For the induction step, we can define a new family $Y' :
(\Fin(n) + \unit) \to \UU$ as before.  Then
%\[
  \prd{m_{n+1} : \Fin(n+1)} \brck{Y(m_{n+1})}
  \eqvsym
  \prd{z : \Fin(n) + \unit} \brck{Y'(z)}
  \eqvsym
  \left(\prd{z : \Fin(n)} \brck{Y'(\inl(z))}\right)
  \times
  \left(\prd{z : \unit} \brck{Y'(\inr(z))}\right)
\]%
and
%\begin{align*}
  \brck{\prd{m_{n+1} : \Fin(n+1)} Y(m_{n+1})}
  &\eqvsym
  \brck{\prd{z : \Fin(n) + \unit} Y'(z)}
  \\&\eqvsym
  \brck{\left(\prd{z : \Fin(n)} Y'(\inl(z))\right)
  \times
  \left(\prd{z : \unit} Y'(\inr(z))\right)}
  \\&\eqvsym
  \brck{\prd{z : \Fin(n)} Y'(\inl(z))}
  \times
  \brck{\prd{z : \unit} Y'(\inr(z))}
\end{align*}%
As before, we pair the induction hypothesis with a trivially constructed map to
produce the required arrow.
*)

(* the induction step *)
Section ISFAC'.
Context {n : nat} {Y : Fin (S n) -> Type}.

Local Definition Y' := Y o (@equiv_inv _ _ cardF (isequiv_cardF n)).

Theorem domain_trans' `{Funext} :
  (forall m, Brck (Y m))
  <~>
  (forall z, Brck (Y ((@equiv_inv _ _ cardF (isequiv_cardF n)) (inl z)))) 
  * (forall z : Unit, Brck (Y (n; (O; (plus_1_r _)^)))).
Proof.
  equiv_via (forall z, Brck (Y' z)).
  refine (equiv_functor_forall' _ _).
  apply equiv_inverse. apply (BuildEquiv _ _ cardF (isequiv_cardF n)).
  intro b. apply equiv_idmap.

  equiv_via ((forall z, Brck (Y' (inl z))) * (forall z, Brck (Y' (inr z)))).
  apply equiv_inverse. refine (equiv_sum_rect _).
  
  apply equiv_idmap.
Defined.

Theorem codomain_trans' `{Funext} : 
  Brck (forall z, Y ((@equiv_inv _ _ cardF (isequiv_cardF n)) (inl z)))
  *
  Brck (forall z : Unit, Y (n; (O; (plus_1_r _)^)))
  <~>
  Brck (forall m, Y m).
Proof.
  equiv_via (Brck (forall z, Y' (inl z)) * Brck (forall z : Unit, Y' (inr z))).
  apply equiv_idmap.
  
  equiv_via (Brck ((forall z, Y' (inl z)) * (forall z, Y' (inr z)))).
  apply equiv_inverse. apply brck_functor_prod. 

  equiv_via (Brck (forall z, Y' z)).
  apply brck_equiv. refine (equiv_sum_rect _).

  apply brck_equiv. refine (equiv_functor_forall' _ _).
  apply (BuildEquiv _ _ cardF (isequiv_cardF n)).
  intro b. unfold Y', compose. apply equiv_path.
  f_ap. apply eissect.
Defined.

End ISFAC'.

Theorem finite_AC' `{Funext} (n : nat) (Y : Fin n -> Type) :
  (forall m, Brck (Y m)) -> Brck (forall m, Y m).
Proof.
  induction n.
  intro H'. apply tr. intro m. contradiction (cardO m).
  
  intro f.
  apply domain_trans' in f. destruct f as [fn f1].
  apply codomain_trans'. split.
  
  apply IHn. apply fn.
  set (z := tt). apply f1 in z. strip_truncations. apply tr. intro t. apply z.
Defined.

Theorem finite_AC_eqv_finite_AC' `{Funext} : 
  (forall (n : nat) (A : Fin n -> Type) P, 
     (forall m, Brck {a : A m & P m a})
     ->
     Brck {g : forall m, A m & forall m, P m (g m)})
  <~>
  (forall (n : nat) (Y : Fin n -> Type),
     (forall m, Brck (Y m)) -> Brck (forall m, Y m)).
Proof.
  apply equiv_iff_hprop.
  
  (* forward *)
  intros finite_AC n Y f.
  transparent assert (e : (
    Brck {g : forall m, Y m & forall m, (fun z a => Unit) m (g m)}
    <~>
    Brck (forall m, Y m)
  )).
  equiv_via (Brck (forall m, {y : Y m & (fun z a => Unit) m y})).
  apply brck_equiv. apply equiv_inverse.
  apply (BuildEquiv _ _ (Book_2_15_6 _ _ _) (Book_2_15_7 _ _ (fun z a => Unit))).
  apply brck_equiv. refine (equiv_functor_forall' _ _). apply equiv_idmap.
  intro b. apply equiv_sigma_contr. intro y. apply contr_unit.
  apply e. clear e.
  
  apply (finite_AC n Y (fun z a => Unit)).
  intro m. assert (Brck (Y m)). apply (f m).
  strip_truncations. apply tr. exists X. apply tt.

  (* back *)
  intros finite_AC' n A P f.
  
  transparent assert (e : (
    Brck (forall m, (fun x => {a : A x & P x a}) m)
    <~>
    Brck {g : forall m : Fin n, A m & forall m : Fin n, P m (g m)}
  )).
  apply brck_equiv.
  apply (BuildEquiv _ _ (Book_2_15_6 _ _ _) (Book_2_15_7 _ _ _)).
  apply e. clear e.

  apply finite_AC'. apply f.
Defined.

Theorem finite_AC_alt `{Funext} (n : nat) (A : Fin n -> Type) 
        (P : forall m, A m -> Type) : 
  (forall m, Brck {a : A m & P m a}) 
  -> Brck {g : forall m, A m & forall m, P m (g m)}.
Proof.
  generalize dependent n.
  apply finite_AC_eqv_finite_AC'.
  apply finite_AC'.
Defined.