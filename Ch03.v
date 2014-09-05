(* begin hide *)
Require Export HoTT Ch02.
(* end hide *)
(** printing <~> %\ensuremath{\eqvsym}% **)
(** printing == %\ensuremath{\sim}% **)
(** printing ^-1 %\ensuremath{^{-1}}% **)
(** * Sets and logic *)

Notation Brck Q := (minus1Trunc Q).

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

Theorem ex3_4 (A : Type) : IsHProp A <-> Contr (A -> A).
Proof.
  split; intro H.

  (* forward *)
  exists idmap; intro f.
  apply path_forall; intro x. apply H.

  (* backward *)
  apply hprop_allpath; intros x y.
  assert ((fun z:A => x) = (fun z:A => y)).
  destruct H. transitivity center. 
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

Theorem ex3_5 (A : Type) : IsHProp A <~> (A -> Contr A).
Proof.
  (* Lemma 3.3.3 *)
  apply equiv_iff_hprop. 
  (* Lemma 3.11.3 *)
  apply contr_inhabited_hprop. 
  apply hprop_inhabited_contr. 
Qed.

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


Theorem ex3_6 {A} : IsHProp A -> IsHProp (A + ~A).
Proof.
  intro H. 
  assert (IsHProp (~A)) as H'. 
  apply hprop_allpath. intros f f'. apply path_forall; intro x. contradiction.
  apply hprop_allpath. intros x y.
  destruct x as [a | f], y as [a' | f'].
  apply (ap inl). apply H.
  contradiction.
  contradiction.
  apply (ap inr). apply H'.
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

Definition ex3_8_i : Q -> (Brck Q) := min1.

Definition ex3_8_ii : (Brck Q) -> Q.
  intro q. apply H2. apply (@minus1Trunc_rect_nondep Q E).
  apply H1. apply H3. apply q.
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
  destruct (LEM (Brck A) minus1Trunc_is_prop).
  apply (minus1Trunc_rect_nondep (fun a => min1 (fun _ : Brck A => a))).
  apply minus1Trunc_is_prop. apply m.
  apply min1. intro a. contradiction n.
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

Definition AC_simpl := forall (X : hSet) (Y : X -> Type),
  (forall x, IsHSet (Y x)) -> 
  ((forall x, Brck (Y x)) -> Brck (forall x, Y x)).

Lemma hprop_is_hset (A : Type) : IsHProp A -> IsHSet A.
Proof.
  typeclasses eauto.
Defined.

Lemma Lemma382 : AC <~> AC_simpl.
Proof.
  apply equiv_iff_hprop; unfold AC, AC_simpl.

  intros AC. intros X Y HY D.
  assert (Brck ({g : forall x, Y x & forall x, (fun x a => Unit) x (g x)})
               <~> Brck (forall x, Y x)).
  apply equiv_iff_hprop. 
  intro w. strip_truncations. apply min1. apply w.1.
  intro g. strip_truncations. apply min1. exists g. intro x. apply tt.
  apply X0. apply (AC X Y (fun x a => Unit)). apply X. apply HY.
  intros. apply hprop_Unit. intros. 
  assert (Brck (Y x)) as y by apply D. strip_truncations. 
  apply min1. exists y. apply tt.

  intros AC_simpl X A P HX HA HP D.
  assert (Brck (forall x, {a : A x & P x a}) 
            <~> Brck {g : forall x, A x & forall x, P x (g x)}).
  apply equiv_iff_hprop.
  intros. strip_truncations. apply min1. exists (fun x => (X0 x).1).
  intro x. apply (X0 x).2.
  intros. strip_truncations. apply min1. intro x. apply (X0.1 x; X0.2 x). 
  apply X0. apply (AC_simpl (default_HSet X HX) (fun x => {a : A x & P x a})).
  intros. apply ex3_3. apply (HA x). intro a.
  apply hprop_is_hset. apply (HP x a).
  intro x. apply (D x).
Defined.

Section Exercise3_13.

Hypothesis LEM' : forall A, A + ~A.

Theorem ex3_13: AC.
Proof.
  apply Lemma382. unfold AC_simpl. intros X Y HX HY.
  apply min1. intros. 
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

Theorem ex3_16 (X : hSet) (Y : X -> Type) :
  (forall x, IsHProp (Y x)) -> 
  (forall x, ~ ~ Y x) <~> ~ ~ (forall x, Y x).
Proof.
  intro HY. apply equiv_iff_hprop; intro H.
  
  intro f. apply f. intro x. 
  destruct (LEM (Y x)). 
    apply HY. apply y.
    contradiction (H x).
  
  intro x. 
  destruct (LEM (Y x)). 
    apply HY. intro f. contradiction.
    assert (~ (forall x, Y x)). intro f. contradiction (f x).
    contradiction H.
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
  (forall x, IsHProp (B x)) -> (forall a, B (min1 a)) -> (forall x, B x).
Proof.
  intros HB f. intro x.
  apply (@minus1Trunc_rect_nondep A (B x)).
  intro a. assert (min1 a = x) as p. apply allpath_hprop.
  apply (transport _ p). apply (f a).
  apply allpath_hprop. apply x.
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

Theorem ex3_18: 
  (forall A, IsHProp A -> (A + ~A)) <-> (forall A, IsHProp A -> (~ ~A -> A)).
Proof.
  split.
  intros LEM A H f. destruct (LEM A H). apply a. contradiction.
  intros DN A H. apply (DN (A + ~A) (ex3_6 H)).
  exact (fun g : ~ (A + ~ A) => g (inr (fun a:A => g (inl a)))).
Qed.
  
  

(** %\exer{3.19}{128}%
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
elements of this type.  By $\snd(w)$ and $\snd(w')$, we have $\fst(w) \leq
\fst(w')$ and $\fst(w') \leq \fst(w)$, so $\fst(w) = \fst(w')$.  Since
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

I'm having just the damnedest time trying to work everything out in Coq.  At
some point I'll sort out my loadpath to cut out the [nat] lemmas.  I'm sure I'm
overcomplicating the correctness proofs for [bounded_min], though.  No way can
they be this long.
*)

Local Open Scope nat_scope.

Definition le (n m : nat) := {k : nat & n + k = m}.
Infix "<=" := le : nat_scope.

Definition lt (n m : nat) := S n <= m.
Infix "<" := lt : nat_scope.

Fixpoint leb n m :=
  match n, m with
    | O, _ => true
    | S n', O => false
    | S n', S m' => leb n' m'
  end.

Infix "<=?" := leb (at level 70) : nat_scope.


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

Definition nat_encode (n m : nat) (p : n = m) := 
  transport (fun k => nat_code n k) p (nat_r n).

Definition nat_decode : forall (n m : nat) (p : nat_code n m), n = m.
  induction n, m; intro.
  reflexivity. contradiction. contradiction.
  apply (ap S). apply IHn. apply p.
Defined.
  
Theorem Theorem2131 : forall n m, (nat_code n m) <~> (n = m).
Proof.
  intros. 
  (* Update to Coq broke this --- 
     9/5: it broke nat_encode; should be okay now
  refine (equiv_adjointify (nat_decode n m) (nat_encode n m) _ _);
  intro p.

  induction p. simpl. induction n. reflexivity.
  simpl. rewrite IHn. reflexivity.

  generalize dependent m. generalize dependent n.
  induction n. induction m. simpl in *. apply eta_unit. contradiction. 
  induction m. contradiction.
  intro p. simpl. unfold nat_encode. rewrite <- transport_compose. simpl. 
  change (transport (fun x : nat => nat_code n x) (nat_decode n m p) (nat_r n))
         with (nat_encode n m (nat_decode n m p)).
  simpl in p. apply IHn.
   *)
Admitted.

Theorem S_inj : forall n m, S n = S m -> n = m.
Proof.
  intros. induction n, m;
    try(reflexivity);
    try(apply Theorem2131 in H; contradiction).
    apply Theorem2131 in H.
    change (nat_code (S (S n)) (S (S m))) with (nat_code (S n) (S m)) in H.
    apply Theorem2131 in H. apply H.
Defined.

Lemma Sn_le_Sm__n_le_m (n m : nat) : (S n) <= (S m) -> n <= m.
  intros. destruct H. simpl in p. apply S_inj in p. apply (x; p).
Defined.

Lemma n_le_m__Sn_le_Sm (n m : nat) : n <= m -> (S n) <= (S m).
  intros. destruct H. exists x. simpl. apply (ap S). apply p.
Defined.

Lemma n_neq_Sn (n : nat) : ~ (n = S n).
Proof.
  induction n.
    intro p. apply Theorem2131 in p. contradiction.
    intro p. apply Theorem2131 in p. simpl in p. apply Theorem2131 in p.
      contradiction.
Defined.

Theorem Sn_plus_Sm__SS_n_plus_m (n m : nat) : S n + S m = S (S (n + m)).
Proof.
  induction n; [| simpl; rewrite <- IHn]; reflexivity.
Defined.

Theorem plus_O_r : forall n, n = n+0.
Proof.
  induction n; [| simpl; rewrite <- IHn]; reflexivity.
Defined.

Theorem n_plus_Sm__Sn_plus_m (n m :nat) : n + S m = S n + m.
Proof.
  revert m. induction n. reflexivity.
  intros. simpl. apply (ap S). simpl in IHn. apply IHn.
Defined.

Theorem plus_assoc : forall n m k, (n + m) + k = n + (m + k).
Proof.
  intros n m k.
  induction n; [| simpl; rewrite IHn ]; reflexivity.
Defined.

Lemma O_is_id : forall n m, n + m = n -> m = 0.
Proof.
  induction n.
    intros. apply H.
    intros m H. apply IHn. simpl in H. apply S_inj in H. apply H.
Defined.

Lemma sum_Ol : forall n m, n + m = 0 -> n = 0.
Proof.
  intros. induction n. reflexivity. 
  simpl in H. apply Theorem2131 in H. contradiction.
Defined.

Lemma leb_le n m : (n <=? m) = true <-> n <= m.
Proof.
  revert m.
  induction n; destruct m; simpl.
  - split; [exists 0|]; trivial.
  - split; trivial. exists (S m). trivial.
  - split; intros. apply false_ne_true in H. contradiction. 
    destruct H. apply sum_Ol in p. apply Theorem2131 in p. contradiction.
  - split. 
    + intros. apply n_le_m__Sn_le_Sm. apply IHn. apply H.
    + intros. apply IHn. apply Sn_le_Sm__n_le_m. apply H.
Defined.

Lemma subtract_on_left : forall n m k, (n + m = n + k) -> (m = k).
Proof.
  induction n. 
  intros. apply H.
  intros. simpl in H. apply S_inj in H. apply IHn. apply H.
Defined.

Lemma le_antisymmetric (n m : nat) : (n <= m) -> (m <= n) -> (n = m).
Proof.
  intros I1 I2. destruct I1 as [k1 p1], I2 as [k2 p2].
  generalize dependent m. generalize dependent n.
  induction n, m. 
    reflexivity. 
    intros. apply Theorem2131 in p2. contradiction.
    intros. apply Theorem2131 in p1. contradiction.
    intros. apply (ap S). apply IHn. simpl in p1. apply S_inj in p1. apply p1.
    intros. simpl in p2. apply S_inj in p2. apply p2.
Defined.

Lemma le_refl n : n <= n.
Proof.
  exists 0. symmetry. apply plus_O_r.
Defined.

Lemma le_trans n m k : (n <= m) -> (m <= k) -> (n <= k).
Proof.
  intros H H'. destruct H, H'.
  exists (x + x0). rewrite <- plus_assoc. rewrite p. apply p0.
Defined.

Theorem ishset_nat : IsHSet nat.
Proof.
  apply hset_decidable. intros n.
  induction n; intro m; destruct m.
      left. reflexivity.
      right. intro p. apply Theorem2131 in p. contradiction.
      right. intro p. apply Theorem2131 in p. contradiction.
      destruct (IHn m).
        left. apply (ap S). apply p.
        right. intro p. apply S_inj in p. contradiction.
Defined.
        
Section Exercise3_19.

Definition decidable {A} (P : A -> Type) := forall a, (P a + ~ P a).

Lemma nat_eq_decidable : forall (n m : nat), (n = m) + ~ (n = m).
Proof.
  intro n.
  induction n; intro m; destruct m.
      left. reflexivity.
      right. intro p. apply Theorem2131 in p. contradiction.
      right. intro p. apply Theorem2131 in p. contradiction.
      destruct (IHn m).
        left. apply (ap S). apply p.
        right. intro p. apply S_inj in p. contradiction.
Defined.

Lemma order_partitions : forall n m, (n <= m) + (m < n).
Proof.
  induction n.
    intro m. left. exists m. reflexivity.
  induction m.
    right. exists n. reflexivity.
    destruct IHm.
      left. destruct l. exists (S x).
      rewrite Sn_plus_Sm__SS_n_plus_m. apply (ap S). apply p.
      destruct (IHn m). 
        left. apply n_le_m__Sn_le_Sm. apply l0.
        right. destruct l0. exists x. simpl. apply (ap S). apply p.
Defined.
      
Definition Q {P : nat -> Type} (w : {n : nat & P n}) := 
  forall w' : {n : nat & P n}, w.1 <= w'.1. 

Lemma ishprop_dependent (A : Type) (P : A -> Type) :
  (forall a, IsHProp (P a)) -> IsHProp (forall a, P a).
Proof.
  intro HP. apply hprop_allpath. intros p p'.
  apply path_forall; intro a. apply HP.
Defined.
  
Lemma hprop_Q : forall P, (forall n, IsHProp (P n)) -> 
  IsHProp {w : {n : nat & P n} & Q w}.
Proof.
  intro P. intro HP. apply hprop_allpath. intros w w'.
  destruct w as [[n p] q], w' as [[n' p'] q'].
  apply path_sigma_uncurried. simpl. 
  assert ((n; p) = (n'; p')).
  apply path_sigma_uncurried. simpl.
  assert (n = n').
  assert (n <= n') as H. apply (q (n'; p')).
  assert (n' <= n) as H'. apply (q' (n; p)).
  destruct H as [k r], H' as [k' r'].
  rewrite <- r' in r. rewrite plus_assoc in r. apply O_is_id in r.
  apply sum_Ol in r. rewrite r in r'. symmetry in r'. 
  rewrite <- plus_O_r in r'. apply r'.
  induction X. exists 1%path. simpl.
  apply (HP n).
  exists X.
  assert (IsHProp (Q (n'; p'))).
  unfold Q. simpl. apply ishprop_dependent. intro w. destruct w as [n'' p''].
  simpl. apply hprop_allpath. intros w w'.
  apply path_sigma_uncurried.
  destruct w, w'. simpl. 
  assert (x = x0). apply subtract_on_left with (n := n').
  apply (p0 @ p1^). exists X0.
  induction X0. simpl. apply ishset_nat. apply X0.
Defined.
  
Definition decidable_to_bool {A} (P : A -> Type) (H : decidable P) : A -> Bool.
  intro a. destruct (H a). apply true. apply false.
Defined.

Fixpoint bounded_min (P : nat -> Type) (H : decidable P) (b : nat) : nat :=
  match b with
    | O => O
    | S n => if (bounded_min P H n <=? n) then (bounded_min P H n) else
               if ((decidable_to_bool P H) (S n)) then (S n) else (S (S n))
  end.

Lemma foo : forall n m, ~ (n = m) -> (n <= m) -> ~ (m <= n).
  intros. intro p. apply le_antisymmetric in H. symmetry in H.
  contradiction. apply p.
Defined.

Lemma bar : forall n m, ~ n = S n + m.
  induction n.
  intros m p. apply Theorem2131 in p. contradiction.
  intros m p. simpl in p. apply S_inj in p. apply (IHn m). apply p.
Defined.

Lemma baz : forall n m, ~ n = n + S m.
  induction n.
  intros m p. apply Theorem2131 in p. contradiction.
  intros m p. simpl in p. apply S_inj in p. apply (IHn m). apply p.
Defined.

Lemma bmin_short_circuit (P : nat -> Type) (H : decidable P) :
  P 0 -> forall n, bounded_min P H n = 0.
Proof.
  intros. induction n. simpl. unfold decidable_to_bool. 
  destruct (H 0). reflexivity. contradiction.
  simpl. assert (bounded_min P H n <=? n = true). apply leb_le.
  rewrite IHn. exists n. reflexivity.
  rewrite X0. apply IHn.
Defined.

Lemma bmin_correct_i (P : nat -> Type) (H : decidable P) (n : nat) :
  P n -> P (bounded_min P H n).
Admitted.

Lemma bmin_correct' (P : nat -> Type) (H : decidable P) (n : nat) :
  P n -> (bounded_min P H n) <= n.
Proof.
  intro p. induction n. simpl.
  assert (decidable_to_bool P H 0 = true) as HP0.
  unfold decidable_to_bool. destruct (H 0). reflexivity. contradiction.
  exists 0. reflexivity.
  
  simpl. destruct (order_partitions (bounded_min P H n) n).
  apply leb_le in l. rewrite l. apply leb_le in l. destruct l.
  exists (S x). rewrite n_plus_Sm__Sn_plus_m. simpl. apply (ap S). apply p0.
  assert ( ~ (bounded_min P H n <= n)).
  apply foo. intro. destruct l. rewrite <- p0 in H0. apply bar in H0.
  contradiction.
  destruct l. exists (S x). rewrite n_plus_Sm__Sn_plus_m. apply p0.
  assert ( ~ (bounded_min P H n <=? n = true)).
  intro H'. apply X. apply leb_le. apply H'.
  assert (bounded_min P H n <=? n = false).
  destruct (bounded_min P H n <=? n). assert (true = true) by reflexivity.
  contradiction X0. reflexivity.
  rewrite X1. unfold decidable_to_bool. destruct (H (S n)). 
  apply le_refl. contradiction.
Defined.

Lemma bmin_unique (P : nat -> Type) (H : decidable P) (n : nat) :
  P n -> forall m, P m -> (bounded_min P H n) = (bounded_min P H m).
Admitted.
  
Definition ex3_19_arrow (P : nat -> Type) (H : decidable P) : 
  (forall n, IsHProp (P n)) -> {n : nat & P n} -> {w : {n : nat & P n} & Q w}.
  intros HP X. destruct X as [n p].
  refine ((bounded_min P H n; bmin_correct_i P H n p); _).
  unfold Q. intro w'. simpl.
  apply le_trans with (m:=bounded_min P H w'.1).
  exists 0. rewrite <- plus_O_r. apply bmin_unique. apply p. apply w'.2.
  apply bmin_correct'. apply w'.2.
Defined.

Definition ex3_19 (P : nat -> Type) (H : decidable P) 
                  (HP : forall n, IsHProp (P n)) : 
  Brck {n : nat & P n} -> {n : nat & P n}.
  intros. apply (@pr1 {n : nat & P n} Q). 
  assert (IsHProp {w : {n : nat & P n} & Q w}) as H'. apply hprop_Q. apply HP.
  strip_truncations. apply ex3_19_arrow. apply H. apply HP. apply X.
Defined.  
  
End Exercise3_19.
  

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

Definition ex3_20_f (A : Type) (P : A -> Type) (HA : Contr A) : 
  {x : A & P x} -> P (center A).
  intros. apply (transport _ (contr X.1)^). apply X.2.
Defined.

Definition ex3_20_g (A : Type) (P : A -> Type) (HA : Contr A) : 
  P (center A) -> {x : A & P x}.
  intros. apply (center A; X).
Defined.
  
Theorem ex3_20 (A : Type) (P : A -> Type) (HA : Contr A) : 
  {x : A & P x} <~> P (center A).
Proof.
  refine (equiv_adjointify (ex3_20_f A P HA) (ex3_20_g A P HA)_ _); 
  unfold ex3_20_f, ex3_20_g.

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

Theorem ex3_31 (P : Type) : IsHProp P <~> (P <~> Brck P).
Proof.
  assert (IsHProp (P <~> Brck P)). apply hprop_allpath; intros e1 e2.
  apply path_equiv. apply path_forall; intro p.
  apply hprop_allpath. apply allpath_hprop.
  apply equiv_iff_hprop.

  intro HP. apply equiv_iff_hprop. apply min1.
  apply (minus1Trunc_rect_nondep idmap). apply HP.
  
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
  \left\lVert
    \sm{g : \prd{m_{n} : \Fin(n)} A(m_{n})} \prd{m_{n} : \Fin(n)}
        P(m_{n}, g(m_{n}))
  \right\rVert.
\]%

We proceed by induction.  For the base case, suppose that $n \equiv 0$, so we
are interested in $\Fin(0) \defeq \sm{n:\mathbb{N}}(m < 0)$, which is
equivalent to $\emptyt$.  Then we have $\ind{\emptyt}(A) : \prd{m_{0} :
\Fin(0)} A(m_{0})$, so
%\[
  \left(
    \ind{\emptyt}(A),
    \ind{\emptyt}(\lam{m_{0}}P(m_{0}, \ind{\emptyt}(A, m_{0})))
  \right)
\]%
is an element of the codomain.

For the induction step, suppose that we have an element
%\[
  f : \prd{m_{n+1} : \Fin(n+1)} 
        \left\lVert \sm{a:A(m_{n+1})} P(m_{n+1}, a)\right\rVert
\]%
which can be modified in the obvious way to give a function
%\[
  \tilde{f} : \prd{m_{n} : \Fin(n)} 
        \left\lVert \sm{a:A(m_{n})} P(m_{n}, a)\right\rVert
\]%
So by the induction step, and since the element we're trying to construct is a
mere proposition, we have an element
%\[
    w : \sm{g : \prd{m_{n} : \Fin(n)} A(m_{n})} \prd{m_{n} : \Fin(n)}
        P(m_{n}, g(m_{n}))
\]%

Now, we need to construct an element of
%\[
\left\lVert
    \sm{g : \prd{m_{n+1} : \Fin(n+1)} A(m_{n+1})} \prd{m_{n+1} : \Fin(n+1)}
        P(m_{n+1}, g(m_{n+1}))
\right\rVert
\]%
To construct the first slot, suppose that $k : \Fin(n + 1)$.  Then because we
have $e : \Fin(n+1) \eqvsym \Fin(n) + \unit$, there are two cases: either $e(k)
: \Fin(n)$ or $e(k) = *$.  In the first case, we set $g(e(k)) \defeq (\fst
w)(e(k))$.  In the second, we 



Suppose the first.  Then we can modify $f$ in the
obvious way to obtain
%\[
  \tilde{f} : \prd{m_{n} : \Fin(n)} 
        \left\lVert \sm{a:A(m_{n})} P(m_{n}, a)\right\rVert
\]%
So by the induction step, and since the element we're trying to construct is a
mere proposition, we have an element
%\[
    w : \sm{g : \prd{m_{n} : \Fin(n)} A(m_{n})} \prd{m_{n} : \Fin(n)}
        P(m_{n}, g(m_{n}))
\]%




*)

Infix "<>" := (fun n m => ~ (n = m)) : nat_scope. 

Definition pred (n : nat) :=
  match n with
    | O => O
    | S n' => n'
  end.

Lemma S_pred_inv : forall n, (n <> O) -> S (pred n) = n.
Proof.
  induction n. intros. contradiction X. reflexivity.
  intros. reflexivity.
Defined.


Definition cardF_f {n} : Fin (S n) -> (Fin n) + Unit.
  intro x. destruct x as [m [k p]].
  destruct (nat_eq_decidable m n).
  right. apply tt.
  left. exists m. exists (pred k). 
  rewrite S_pred_inv.
  simpl in p. rewrite <- plus_n_Sm in p. apply S_inj in p. apply p. 
  intro. rewrite H in p.  rewrite <- plus_1_r in p. apply S_inj in p. 
  contradiction.
Defined.

Definition Fin_incl {n : nat} : Fin n -> Fin (S n).
  intros m. destruct m as [m [k p]].
  exists m. exists (S k). apply ((plus_n_Sm m (S k))^ @ (ap S p)).
Defined.

Definition cardF_g {n} : (Fin n) + Unit -> Fin (S n).
  intro x. destruct x as [m | t]. apply (Fin_incl m).
  exists n. exists 0. apply (plus_1_r n)^.
Defined.
  
Lemma sum_O_r (n m : nat) : n + m = n -> m = 0.
Proof.
  induction n. simpl. apply idmap.
  intros. simpl in H. apply S_inj in H. apply IHn. apply H.
Defined.

Lemma cardFO : Fin O <~> Empty.
Proof.
  refine (equiv_adjointify _ _ _ _).
  intro n. destruct n as [n [k p]]. 
  assert (S (n + k) = 0). transitivity (n + S k). apply plus_n_Sm. apply p.
  apply Theorem2131 in X. contradiction.
  intro e. contradiction.
  intro e. contradiction.
  intro n. destruct n as [n [k p]].
  assert (S (n + k) = 0). transitivity (n + S k). apply plus_n_Sm. apply p.
  apply Theorem2131 in X. contradiction.
Defined.

Lemma cardF {n : nat} : Fin (S n) <~> (Fin n) + Unit.
Proof.
  intros. refine (equiv_adjointify cardF_f cardF_g _ _); intros x.
  unfold cardF_f, cardF_g. simpl.
  destruct x. simpl. destruct f as [m [k p]]. simpl.
  destruct (nat_eq_decidable m n). simpl.
  rewrite <- p in p0. assert (m <> m + S k). apply baz. contradiction.
  simpl. apply (ap inl). apply path_sigma_uncurried. simpl. exists idpath.
  simpl. apply path_sigma_uncurried. simpl. exists idpath.
  simpl. apply ishset_nat.
  destruct (nat_eq_decidable n n). apply (ap inr). apply path_unit.
  assert Empty. apply n0. reflexivity. contradiction.

  unfold cardF_f, cardF_g. simpl. destruct x as [m [k p]].
  destruct (nat_eq_decidable m n).
  apply path_sigma_uncurried. simpl. exists p0^. simpl.
  induction p0. simpl. apply path_sigma_uncurried. simpl.
  assert (0 = k). symmetry. apply sum_O_r with (n := S m). 
  rewrite <- plus_n_Sm in p. simpl.
  apply p. exists X.
  apply ishset_nat.
  apply path_sigma_uncurried. simpl. exists idpath. simpl. 
  apply path_sigma_uncurried. simpl.
  assert (k <> 0). intro. rewrite X in p.
  rewrite <- plus_n_Sm in p. apply S_inj in p. rewrite <- plus_0_r in p.
  contradiction.
  exists (S_pred_inv k X). apply ishset_nat.
Defined.

Theorem ex3_22 `{Univalence}: forall (n : nat) (A : Fin n -> Type)
                        (P : forall (m : Fin n), A m -> Type),
  (forall n, IsHSet (A n)) -> (forall m a, IsHProp (P m a)) ->
  (forall m, Brck {a : A m & P m a}) -> 
  Brck {g : forall m, A m & forall k, P k (g k)}.
Proof.
  induction n.
  
  (* case n = 0 *)
  intros A P HA HP f. apply min1.
  assert (forall m, A m). intros. contradiction (cardFO m).
  exists X. intro. contradiction (cardFO k).

  (* case n = S n *)
  intros A P HA HP f.
  assert (forall k : Fin n, Brck {a : A (Fin_incl k) & P (Fin_incl k) a}) as w.
  intros. apply (f (Fin_incl k)).
  apply IHn in w. 
  strip_truncations.
  assert (forall m : Fin (S n), A m) as g.
  intro m. 
  rewrite <- (eissect cardF m). 
  destruct (cardF m) as [em | m_m]; simpl.
    apply (w.1 em).
    Admitted.
    
  

Local Close Scope nat_scope.
