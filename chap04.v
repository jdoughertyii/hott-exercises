(* begin hide *)
Require Export HoTT chap03.
(* end hide *)
(** printing <~> %\ensuremath{\eqvsym}% **)
(** printing == %\ensuremath{\sim}% **)
(** printing ^-1 %\ensuremath{^{-1}}% **)
(** * Equivalences *)

(** %\exer{4.1}{147}% 
Consider the type of ``two-sided adjoint equivalence data'' for $f : A \to B$,
%\[
  \sm{g:B \to A} 
  \sm{\eta : g \circ f \sim \idfunc{A}}
  \sm{\epsilon : f \circ g \sim \idfunc{B}}
  \left(\prd{x:A} f(\eta x) = \epsilon(f x)\right)
    \times
  \left(\prd{y:B} g(\epsilon y) = \eta(g y)\right)
\]%
By Lemma 4.2.2, we know that if $f$ is an equivalence, then this type is
inhabited.  Give a characterization of this type analogous to Lemma 4.1.1.
Give an example showing that this type is not generally a mere proposition.
*)


Definition tsaed {A B} (f : A -> B) :=
  {g : B -> A & {h : g o f == idmap & {e : f o g == idmap &
    (forall x, (ap f (h x)) = e (f x)) * (forall y, (ap g (e y)) = h (g y))}}}.


Definition step1_f {A B} (f : A -> B) : (tsaed f) -> 
  {g : B -> A & {h : g o f == idmap & {e : f o g == idmap &
    (forall x, (ap f (h x)) = e (f x))}}} 
  :=
  fun X => (X.1; (X.2.1; (X.2.2.1; fst X.2.2.2))).


(** %\exer{4.2}{147}% 
Show that for any $A, B : \UU$, the following type is equivalent to $A \eqvsym
B$.
%\[
  \sm{R : A \to B \to \UU}
  \left(\prd{a:A} \iscontr \left(\sm{b:B} R(a, b)\right)\right)
  \times
  \left(\prd{b:B} \iscontr \left(\sm{a:A} R(a, b)\right)\right).
\]%
Extract from this a definition of a type satisfying the three desiderata of
$\isequiv(f)$.
*)

(** %\exer{4.3}{147}% 
Reformulate the proof of Lemma 4.1.1 without using univalence.
*) 

Definition qinv {A B : Type} (f : A -> B) :=
  {g : B -> A & (f o g == idmap) * (g o f == idmap)}.

Axiom qinv_isequiv : forall A B (f : A -> B), qinv f -> IsEquiv f.
Axiom isequiv_qinv : forall A B (f : A -> B), IsEquiv f -> qinv f.

Definition ex4_3_f {A B : Type} {f : A -> B} : qinv f -> forall (x:A), x = x. 
  intros.
  destruct X as [g [alpha beta]].
  etransitivity (g (f x)).
  apply (beta x)^. apply (beta x).
Defined.

Theorem Theorem411 {A B : Type} (f : A -> B) : (qinv f) -> 
  (qinv f) <~> (forall x:A, x = x).
Proof.
Admitted.

(** %\exer{4.4}{147}% 
Suppose $f : A \to B$ and $g : B \to C$ and $b : B$.
%\begin{itemize}
  \item[(i)] Show that there is a natural map $\hfib{g \circ f}{g(b)} \to
      \hfib{g}{g(b)}$ whose fiber over $(b, \refl{g(b)})$ is equivalent to
      $\hfib{f}{b}$.
  \item[(ii)] Show that $\hfib{g \circ f}{g(b)} \eqvsym \sm{w:\hfib{g}{g(b)}}
      \hfib{f}{\fst w}$.
\end{itemize}%
*)

(** %\soln%
(i) Unfolding the $\mathsf{fib}$ notation, we are looking for a map
%\[
  \left(\sm{a:A} (g(f(a)) = g(b))\right) \to
  \left(\sm{b':B} (g(b') = g(b))\right)
\]%
The obvious choice is $f^{*} \defeq (a, p) \mapsto (f(a), p)$.  We then must
show that $\hfib{f^{*}}{b, \refl{g(b)}} \eqvsym \hfib{f}{b}$.  Unfolding the
notation again, we're looking for an equivalence
%\[
  \left(\sm{w:\hfib{g \circ f}{g(b)}} (f^{*}(w) = (b, \refl{g(b)}))\right)
  \eqvsym
  \left(\sm{a:A} (f(a) = b)\right)
\]%

For the arrow, suppose that $(w, p)$ is an element of the domain, so that $w :
\hfib{g \circ f}{g(b)}$ and $q : f^{*}(w) = (b, \refl{g(b)})$.  By the
induction principle for $\hfib{g \circ f}{g(b)}$, it suffices to consider the
case where $w \equiv (a, p)$, for $a : A$ and $p : g(f(a)) = g(b)$.  Then
%\[
  q : 
  (f^{*}(a, p) = (b, \refl{g(b)})) 
  \equiv
  ((f(a), p) = (b, \refl{g(b)})) 
\]%
thus $(a, \fst q) : \hfib{f}{b}$.  Explicitly, our map is
%\[
  z \mapsto (\fst(\fst z), \fst (\snd z))
\]%

For a quasi-inverse, suppose that $(a, p) : \hfib{f}{b}$.  Then $(a,
g(p)) : \hfib{g \circ f}{g(b)}$.  We need a proof that
%\[
  (f^{*}(a, g(p)) = (b, \refl{g(b)})) 
  \equiv
  ((f(a), g(p)) = (b, \refl{g(b)})) 
\]%
$p$ provides the proof of equality for the first slots.  For the
second, by induction we can consider the case where $f(a) \equiv b$
and $p \equiv \refl{b}$.  Then $g(p) \equiv \refl{g(b)}$, and the
proof we seek is just reflexivity.
*)

Section Exercise4_4.

Variables (A B C D : Type) (f : A -> B) (g : B -> C) (b : B).

Definition f_star (z : ((hfiber (g o f) (g b)))) : (hfiber g (g b)) := 
  (f z.1; z.2).
    
Definition ex4_4_f (z : (hfiber f_star (b; 1))) : (hfiber f b) :=
  (z.1.1; (base_path z.2)).

Definition ex4_4_g (w : (hfiber f b)) : (hfiber f_star (b; 1)).
  refine ((w.1; ap g w.2); _).
  unfold f_star. simpl.
  apply path_sigma_uncurried. exists w.2. simpl.
  induction w.2. reflexivity.
Defined.


Lemma ex4_4_alpha : Sect ex4_4_g ex4_4_f.
Proof.
  unfold ex4_4_f, ex4_4_g. 
  intro w. destruct w as [a p]. simpl.
  apply path_sigma_uncurried; simpl. 
  exists 1.  simpl. unfold f_star in *.
  induction p. reflexivity.
Defined.

Lemma ex4_4_beta : Sect ex4_4_f ex4_4_g.
Proof.
  unfold ex4_4_f, ex4_4_g, f_star. intro w.
  apply path_sigma_uncurried. simpl.
  assert (((w .1) .1; ap g (base_path w .2)) = w .1).
  apply path_sigma_uncurried. exists 1. simpl.
  destruct w as [[a p] q]. simpl in *.
  transitivity ((ap g (base_path q))^)^. symmetry. apply inv_V.
  transitivity (ap g (base_path q)^)^. hott_simpl.
  transitivity (ap g (base_path q^))^. unfold base_path. hott_simpl.
  apply moveR_V1.
  apply symmetry.
  apply (@hfiber_triangle B C g (g b) (b; 1) (f a; p) q^).
  exists X.
  destruct w as [[a p] q]. simpl in *.
Admitted.
  



Theorem ex4_4 : (hfiber (f_star) (b; 1)) <~> (hfiber f b).
Proof.
  apply (equiv_adjointify ex4_4_f ex4_4_g ex4_4_alpha ex4_4_beta).
Defined.

End Exercise4_4.

(** %\exerdone{4.5}{147}% 
Prove that equivalences satisfy the _2-out-of-6 property_: given $f : A \to B$
and $g : B \to C$ and $h : C \to D$, if $g \circ f$ and $h \circ g$ are
equivalences, so are $f$, $g$, $h$, and $h \circ g \circ f$.  Use this to give
a higher-level proof of Theorem 2.11.1.
*) 

(** %\soln%
Suppose that $g \circ f$ and $h \circ g$ are equivalences.

 - $f$ is an equivalence with quasi-inverse $(g \circ f)^{-1} \circ g$.  It's a
   retract because
   %\begin{align*}
     f \circ (g \circ f)^{-1} \circ g
     &\sim
     (h \circ g)^{-1} \circ (h \circ g) \circ f \circ (g \circ f)^{-1} \circ g
     \\&\sim
     (h \circ g)^{-1} \circ h \circ g
     \\&\sim
     \idfunc{B}
   \end{align*}%
   and a section because $(g \circ f)^{-1} \circ g \circ f \sim \idfunc{A}$.

 - $g$ is an equivalence with quasi-inverse $(h \circ g)^{-1} \circ h$.  First
   we have
   %\begin{align*}
     g \circ (h \circ g)^{-1} \circ h
     &\sim
     g \circ (h \circ g)^{-1} \circ h \circ g \circ f \circ (g \circ f)^{-1}
     \\&\sim
     g \circ f \circ (g \circ f)^{-1}
     \\&\sim
     \idfunc{C}
   \end{align*}%
   and second $(h \circ g)^{-1} \circ h \circ g \sim \idfunc{B}$.
 
 - $h$ is an equivalence with quasi-inverse $g \circ (h \circ g)^{-1}$.  First,
   $h \circ g \circ (h \circ g)^{-1} \sim \idfunc{D}$, and we have
   $g \circ (h \circ g)^{-1} \circ h \sim \idfunc{C}$ by the previous part.

 - $h \circ g \circ f$ is an equivalence with quasi-inverse $f^{-1} \circ (h
   \circ g)^{-1}$.  Both directions are immediate:
   %\begin{align*}
     h \circ g \circ f \circ f^{-1} \circ (h \circ g)^{-1} &\sim \idfunc{D} \\
     f^{-1} \circ (h \circ g)^{-1} \circ h \circ g \circ f &\sim \idfunc{A}
   \end{align*}%


Now we must give a higher-level proof that if $f : A \to B$ is an equivalence,
then for all $a, a' : A$ so is $\mapfunc{f}$.  This uses the following
somewhat obvious fact, which I don't recall seeing in the text or proving yet:
if $f : A \to B$ is an equivalence and $f \sim g$, then $g$ is an equivalence.
For any $a : A$ we have $f^{-1}(g(a)) = f^{-1}(f(a)) = a$
and for any $b : B$, $g(f^{-1}(b)) = f(f^{-1}(b)) = b$, giving $\isequiv(g)$.

Consider the sequence
%\[
   \left(a = a'\right) \xrightarrow{\mapfunc{f}} 
   \left(f(a) = f(a')\right) \xrightarrow{\mapfunc{f^{-1}}} 
   \left(f^{-1}(f(a)) = f^{-1}(f(a'))\right) \xrightarrow{\mapfunc{f}} 
   \left(f(f^{-1}(f(a))) = f(f^{-1}(f(a')))\right)
\]%
Since $f$ is an equivalence, we have
%\[
  \alpha : \prd{b:B} f(f^{-1}(b)) = b
  \qquad\qquad
  \beta : \prd{a:A} f^{-1}(f(a)) = a
\]%
For all $p : a = a'$, 
$\mapfunc{f^{-1}}(\mapfunc{f}(p)) = \beta_{a} \ct p \ct \beta_{a'}^{-1}$, 
which follows from the functorality of $\mapfunc{}$ and the naturality of
homotopies (Lemmas 2.2.2 and 2.4.3).  In other words, the composition of the
first two arrows is homotopic to concatenating with $\beta$ on either side,
which is obviously an equivalence.  Similarly, the composition of the second
two arrows is homotopic to concatenating with the appropriate $\alpha$ on
either side, again an obvious equivalence.  So by the 2-out-of-6 property, the
first arrow is an equivalence, which was to be proved.
*)

Theorem two_out_of_six {A B C D : Type} (f : A -> B) (g : B -> C) (h : C -> D) :
  IsEquiv (g o f) -> IsEquiv (h o g) ->
  (IsEquiv f /\ IsEquiv g /\ IsEquiv h /\ IsEquiv (h o g o f)).
Proof.
  intros Hgf Hhg. split.
  
  (* case f *)
  refine (isequiv_adjointify f ((g o f) ^-1 o g) _ _).
  intro b. 
  change (f (((g o f) ^-1 o g) b)) with ((f o (g o f) ^-1 o g) b).
  assert ((f o (g o f) ^-1 o g) b
          =
          ((h o g) ^-1 o (h o g) o f o (g o f) ^-1 o g) b).
  change (((h o g) ^-1 o (h o g) o f o (g o f) ^-1 o g) b)
         with ((((h o g) ^-1 ((h o g) ((f o (g o f) ^-1 o g) b))))).
  rewrite (eissect (h o g)). reflexivity.
  rewrite X.
  change (((h o g) ^-1 o (h o g) o f o (g o f) ^-1 o g) b)
         with ((((h o g) ^-1 o h) ((((g o f) ((g o f) ^-1 (g b))))))).
  rewrite (eisretr (g o f)).
  change (((h o g) ^-1 o h) (g b)) with (((h o g) ^-1 o (h o g)) b).
  apply (eissect (h o g)).

  intro a. apply (eissect (g o f)).

  split.
  (* case g *)
  refine (isequiv_adjointify g ((h o g) ^-1 o h) _ _).
  intro c.
  change (g (((h o g) ^-1 o h) c)) with ((g o (h o g) ^-1 o h) c).
  assert ((g o (h o g) ^-1 o h) c
          =
          (g o (h o g) ^-1 o h o g o f o (g o f) ^-1) c).
  change ((g o (h o g) ^-1 o h o g o f o (g o f) ^-1) c)
         with (((g o (h o g) ^-1 o h) ((g o f) ((g o f) ^-1 c)))).
  rewrite (eisretr (g o f)). reflexivity.
  rewrite X.
  change ((g o (h o g) ^-1 o h o g o f o (g o f) ^-1) c)
         with (g (((h o g) ^-1 ((h o g) ((f o (g o f) ^-1) c))))).
  rewrite (eissect (h o g)).
  change (g ((f o (g o f) ^-1) c)) with (((g o f) o (g o f) ^-1) c).
  apply (eisretr (g o f)).

  intro b. apply (eissect (h o g)).

  split.
  (* case h *)
  refine (isequiv_adjointify h (g o (h o g) ^-1) _ _).
  intro d. apply (eisretr (h o g)).
  
  intro c.
  change ((g o (h o g) ^-1) (h c)) with ((g o (h o g) ^-1 o h) c).
  assert ((g o (h o g) ^-1 o h) c
          =
          (g o (h o g) ^-1 o h o g o f o (g o f) ^-1) c).
  change ((g o (h o g) ^-1 o h o g o f o (g o f) ^-1) c)
         with (((g o (h o g) ^-1 o h) ((g o f) ((g o f) ^-1 c)))).
  rewrite (eisretr (g o f)). reflexivity.
  rewrite X.
  change ((g o (h o g) ^-1 o h o g o f o (g o f) ^-1) c)
         with (g ((h o g) ^-1 ((h o g) ((f o (g o f) ^-1) c)))).
  rewrite (eissect (h o g)).
  change (g ((f o (g o f) ^-1) c)) with (((g o f) o (g o f) ^-1) c).
  apply (eisretr (g o f)).
  
  (* case h o g o f *)
  refine (isequiv_adjointify (h o g o f) ((g o f) ^-1 o g o (h o g) ^-1) _ _).
  intro d.
  change ((h o g o f) (((g o f) ^-1 o g o (h o g) ^-1) d))
         with (h ((g o f) ((g o f) ^-1 ((g o (h o g) ^-1) d)))).
  rewrite (eisretr (g o f)).
  apply (eisretr (h o g)).

  intro a.
  change (((g o f) ^-1 o g o (h o g) ^-1) ((h o g o f) a))
         with ((((g o f) ^-1 o g) ((h o g) ^-1 ((h o g) (f a))))).
  rewrite (eissect (h o g)). apply (eissect (g o f)).
Qed.
  
Theorem isequiv_homotopic' : forall (A B : Type) (f g : A -> B),
  IsEquiv f -> f == g -> IsEquiv g.
Proof.
  intros A B f g p h.
  refine (isequiv_adjointify g f^-1 _ _).
  intros b. apply ((h (f^-1 b))^ @ (eisretr f b)).
  intros a. apply ((ap f^-1 (h a))^ @ (eissect f a)).
Defined.


Theorem Theorem2111' (A B : Type) (a a' : A) (f : A -> B) (H : IsEquiv f) :
  IsEquiv (fun p : a = a' => ap f p).
Proof.
  apply (two_out_of_six (fun p : a = a' => ap f p)
                        (fun p : (f a) = (f a') => ap f^-1 p)
                        (fun p : (f^-1 (f a)) = (f^-1 (f a')) => ap f p)).
  apply (isequiv_homotopic (fun p => (eissect f a) @ p @ (eissect f a')^)).
  refine (isequiv_adjointify _ 
                             (fun p => (eissect f a)^ @ p @ (eissect f a')) 
                             _ _);
  intro; hott_simpl.
  intro p. induction p. hott_simpl.
  
  apply (isequiv_homotopic (fun p => (eisretr f (f a)) @ p @ (eisretr f (f a'))^)).
  refine (isequiv_adjointify _ 
                        (fun p => (eisretr f (f a))^ @ p @ (eisretr f (f a'))) 
                        _ _);
  intro; hott_simpl.
  intro p. induction p. hott_simpl.
Defined.


(** %\exer{4.6}{147}% 
For $A, B : \UU$, define
%\[
  \mathsf{idtoqinv}(A, B) : (A = B) \to \sm{f : A \to B} \qinv(f)
\]%
by path induction in the obvious way.  Let %\qinv%-univalence denote the
modified form of the univalence axiom which asserts that for all $A, B : \UU$
the function $\mathsf{idtoqinv}(A, B)$ has a quasi-inverse.
%\begin{itemize}
  \item[(i)] Show that \qinv-univalence can be used instead of univalence in
      the proof of function extensionality in \S4.9.
  \item[(ii)] Show that \qinv-univalence can be used instead of univalence in
      the proof of Theorem 4.1.3.
  \item[(iii)] Show that \qinv-univalence is inconsistent.  Thus, the use of a
      ``good'' version of $\isequiv$ is essential in the statement of
      univalence.
\end{itemize}%
*)

(** %\soln%
(i)  The proof of function extensionality uses univalence in the proof of
Lemma 4.9.2.  Assume that $\UU$ is $\qinv$-univalent, and that $A, B, X : \UU$
with $e : A \eqvsym B$.  From $e$ we obtain $f : A \to B$ and $p :
\ishae(f)$, and from the latter we obtain an element $q : \qinv(f)$.
$\qinv$-univalence says that we may write $(f, q) = \mathsf{idtoqinv}_{A,
B}(r)$ for some $r : A = B$.  Then by path induction, we may assume that $r
\equiv \refl{A}$, making $e = \idfunc{A}$, and the function $g \mapsto g \circ
\idfunc{A}$ is clearly an equivalence $(X \to A) \eqvsym (X \to B)$,
establishing Lemma 4.9.2.  Since the rest of the section is either an
application of Lemma 4.9.2 or doesn't use the univalence axiom, the proof of
function extensionality goes through.
*)

Section Exercise4_6.

Definition idtoqinv {A B} : (A = B) -> {f : A -> B & (qinv f)}.
  path_induction. exists idmap. exists idmap.
  split; intro a; reflexivity.
Defined.

Hypothesis qinv_univalence : forall A B, qinv (@idtoqinv A B).

Theorem ex4_6i (A B X : Type) (e : A <~> B) : (X -> A) <~> (X -> B).
Proof.
  destruct e as [f p].
  assert (qinv f) as q. exists f^-1. split. 
    apply (eisretr f). apply (eissect f).
  assert (A = B) as r. apply (qinv_univalence A B). apply (f; q).
  path_induction. apply equiv_idmap.
Defined.

(**
(ii) Theorem 4.1.3 provides an example of types $A$ and $B$ and a function $f:
A \to B$ such that $\qinv(f)$ is not a mere proposition, relying on the result
of Lemma 4.1.1.  Since Lemma 4.1.1 does not actually rely on univalence
%(cf.~Exercise 4.3)%, we only need to worry about the use of univalence in the
proof of Theorem 4.1.3.  Define $X \defeq \sm{A : \UU} \brck{\bool = A}$ and
$a \defeq (\bool, \lvert \refl{\bool} \rvert) : X$.  Let $e : \bool \eqvsym
\bool$ be the non-identity equivalence from Exercise 2.13, which gives us
$\lnot : \bool \to \bool$ and $r : \qinv(\lnot)$.  Define $q \defeq
\mathsf{idtoqinv}_{\bool, \bool}^{-1}(\lnot, r)$.  Now we can run the proof as
before, applying Lemma 4.1.2.  
    
Here univalence is used only in establishing that $a = a$ is a set, by showing
that it's equivalent to $(\bool \eqvsym \bool)$.
*)

Lemma Lemma412 (A : Type) (a : A) (q : a = a) :
  IsHSet (a = a) -> (forall x, Brck (a = x)) 
  -> (forall p : a = a, p @ q = q @ p)
  -> {f : forall (x:A), x = x & f a = q}.
Proof.
  intros i g iii.
  assert (forall (x y : A), IsHSet (x = y)).
  intros x y. 
  assert (Brck (a = x)) as gx. apply (g x). 
  assert (Brck (a = y)) as gy. apply (g y).
  strip_truncations.
  apply (ex3_1' (a = a)).
  refine (equiv_adjointify (fun p => gx^ @ p @ gy) (fun p => gx @ p @ gy^) _ _);
  intros p; hott_simpl.
  apply i.
  assert (forall x, IsHProp ({r : x = x & forall s : a = x, r = s^ @ q @ s})).
  intro x. assert (Brck (a = x)) as p. apply (g x). strip_truncations.
  apply hprop_allpath; intros h h'; destruct h as [r h], h' as [r' h'].
  apply path_sigma_uncurried. exists ((h p) @ (h' p)^).
  simpl. apply path_forall; intro s. 
  apply (X x x).
  assert (forall x, {r : x = x & forall s : a = x, r = (s ^ @ q) @ s}).
  intro x. assert (Brck (a = x)) as p. apply (g x). strip_truncations.
  exists (p^ @ q @ p). intro s. 
  apply (cancelR _ _ s^). hott_simpl.
  apply (cancelL p). hott_simpl.
  transitivity (q @ (p @ s^)). hott_simpl.
  symmetry. apply (iii (p @ s^)).
  exists (fun x => (X1 x).1). 
  transitivity (1^ @ q @ 1).
  apply ((X1 a).2 1). hott_simpl.
Defined.
  
Definition idtoqinv_Bool : 
  ((Bool:Type) <~> (Bool:Type)) -> ((Bool:Type) = (Bool:Type)).
  intros.
  apply (qinv_univalence Bool Bool).1.
  destruct X. exists equiv_fun.
  destruct equiv_isequiv. exists equiv_inv.
  split. apply eisretr. apply eissect.
Defined.

Definition a_a_to_Bool_Bool : 
  (((Bool:Type); min1 1):{A : Type & Brck ((Bool:Type) = A)}) 
  =
  (((Bool:Type); min1 1):{A : Type & Brck ((Bool:Type) = A)}) 
  -> ((Bool:Type) <~> (Bool:Type)).
  intros. simpl. apply base_path in X. simpl in X.
  apply idtoqinv in X. 
  apply (BuildEquiv Bool Bool X.1).
  apply (isequiv_adjointify X.1 X.2.1 (fst X.2.2) (snd X.2.2)).
Defined.

Theorem ex4_6ii : {A : Type & {B : Type & {f : A -> B & ~ IsHProp (qinv f)}}}.
Proof.
  set (X := {A : Type & Brck ((Bool:Type) = A)}).
  refine (X; (X; _)).
  set (a := ((Bool:Type); min1 1) : X).
  set (e := negb_isequiv). destruct e as [lnot H].
  set (r := (lnot^-1; (eisretr lnot, eissect lnot)) : qinv lnot).
  set (q := (path_sigma_hprop a a ((qinv_univalence Bool Bool).1 (lnot; r)))).
  assert {f : forall x, x = x & (f a) = q}.
  apply Lemma412.
  apply (ex3_1' (Bool <~> Bool)).
  refine (equiv_adjointify ((path_sigma_hprop a a) o idtoqinv_Bool) 
                           (a_a_to_Bool_Bool)
                           _ _);
  unfold idtoqinv_Bool, a_a_to_Bool_Bool, compose.
  intro p. simpl.
Admitted.
  
  
  
  
  
  
  
  

  
  


End Exercise4_6.
