(* begin hide *)
Require Import HoTT.
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

(** %\exer{3.10}{127}%
Show that if $\UU_{i+1}$ satisfies $\LEM{}$, then the canonical inclusion
$\prop_{\UU_{i}} \to \prop_{\UU_{i+1}}$ is an equivalence.
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
  apply (@transport_arrow Type (fun A => Brck A) idmap).
  rewrite X in X0.
  assert (b = (transport (fun A : Type => Brck A) (path_universe negb) ^ b)).
  apply allpath_hprop. rewrite <- X1 in X0. symmetry in X0.
  assert (transport idmap (path_universe negb) (f Bool b) = negb (f Bool b)).
  apply transport_path_universe. rewrite X2 in X0. apply X0.
  apply (@negb_no_fixpoint (f Bool (min1 true))). 
  apply (X (min1 true)).
Qed.
  
  
  