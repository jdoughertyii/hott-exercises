(* begin hide *)
Require Export HoTT Ch03.
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


(** %\exerdone{4.2}{147}% 
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

(** %\soln%
Suppose that this type is inhabited; by induction we may suppose that the
inhabitant breaks down into
%\begin{align*}
  R &: A \to B \to \UU \\
  f &: \prd{a:A} \iscontr\left(\sm{b:B}R(a, b)\right) \\
  g &: \prd{b:B} \iscontr\left(\sm{a:A}R(a, b)\right)
\end{align*}%
We have to construct an element $e : \eqv{A}{B}$.  For the forward map, suppose
that $a : A$.  Then
%\[
  f(a) : \iscontr\left(\sm{b:B}R(a, b)\right)
\]%
so there is some $(b, p) : \sm{b:B}R(a,b)$, and we set $e(a) \defeq b$.  For
the inverse, suppose that $b:B$.  Then $g(b) : \iscontr(\sm{a:A}R(a, b))$, so
there is some center $(a, p) : \sm{a:A}R(a,b)$, and we set $e^{-1}(b) \defeq
a$.  To prove that these are quasi-inverses, suppose that $a : A$.  Then $f(a)
: \iscontr(\sm{b:B}R(a,b))$, so the center is $(b, p) : \sm{b:B}R(a,b)$ and
$e(a) \equiv b$.  But then $g(e(a)) : \iscontr(\sm{a:A}R(a, b))$, and the
center of this is $(a', q) : \sm{a:A}R(a,b)$, so $e^{-1}(e(a)) = a'$.  But
now we have $(a, p) : \sm{a:A}R(a, b)$, and since this type is contractible we
have $(a, q) = (a', p)$, hence $e^{-1}(e(a)) = a' = a$.  The other direction
goes just the same way.

For the other direction, suppose that $e : \eqv{A}{B}$, and consider the
relation $R \defeq \lam{a}{b}(e(a) = b) : A \to B \to \UU$.  For any $a : A$,
$\sm{b:B}(e(a) = b)$ is contractible by Lemma 3.11.8.  For any $b:B$,
$\sm{a:A}(e(a) = b)$ is equivalent to $\sm{a:A}(e^{-1}(b) = a)$, and this is
also contractible by Lemma 3.11.8.  So we have an element of the type above.

To show that these are quasi-inverses, let $e : \eqv{A}{B}$, and take it once
around the loop to get an equivalence with underlying map $e : A \to B$.  Since
an equivalence is determined by its underlying map, we're back where we
started.  For the other direction, suppose that we have an element of the type
in the problem statement, and take it once around the loop.  Since
contractibility is a mere proposition and products preserve these, it suffices
to show that the first components are equal, or that $(b' = b) = R(a, b)$ for
$b'$ the center of $\sm{b:B}R(a, b)$.  By univalence it suffices to show that
these are equivalent, and since they are mere propositions it suffices to show
that they logically imply one another.  Transport gives us the first
direction, and the other is given by the contractibility of $\sm{b:B}R(a, b)$.
So we've established an equivalence.

For $f : A \to B$, define 
%\[
  \isequiv'(f) \defeq
  \left(\prd{a:A}\iscontr\left(\sm{b:B}(f(a) = b)\right)\right)
  \times
  \left(\prd{b:B}\iscontr\left(\sm{a:A}(f(a) = b)\right)\right)
\]%
To show that desideratum (i) is satisfied, suppose that $p : \qinv(f)$.  Then
$\isequiv(f)$ is inhabited, so $\eqv{A}{B}$ is as well.  But then the
equivalence just established gives us an element whose second entry is an
element of $\isequiv'(f)$.  So we have an arrow $\qinv(f) \to \isequiv'(f)$.
For the other direction, suppose that we have an element $p : \isequiv'(f)$.
Then $\lam{a}{b}(f(a) = b)$ gives us an element that our equivalence takes to
$\eqv{A}{B}$, and the second element of this is of type $\isequiv(f)$.  But
then we have $\isequiv(f) \to \qinv(f)$, so our desideratum is satisfied.
Finally, $\isequiv'(f)$ is constructed out of products of mere propositions, so
it too is a mere proposition.
*)

Definition equiv_to_contr_rel_equiv (A B : Type) :
  (A <~> B)
  ->
  {R : A -> B -> Type & (forall a, Contr {b : B & R a b})
                      * (forall b, Contr {a : A & R a b})}.
Proof.
  intro e.
  exists (fun a b => (e a = b)). split. 
  intro a. apply contr_basedpaths.
  intro b. refine (@contr_equiv' {a : A & e^-1 b = a} _ _ _).
  refine (equiv_functor_sigma' _ _).
  apply equiv_idmap. intro a. simpl.
  refine (equiv_adjointify _ _ _ _).
  intro eq. refine (_ @ (eisretr e b)). apply (ap e). apply eq^.
  intro eq. refine (_ @ (eissect e a)). apply (ap e^-1). apply eq^.
  intro eq. induction eq. simpl. 
  apply moveR_pM. refine (_ @ (concat_1p _)^). refine ((ap_V _ _) @ _).
  apply inverse2. refine ((ap_pp _ _ _) @ _).
  apply moveR_pM. refine ((ap_1 _ _ ) @ _). apply moveL_pV.
  refine ((concat_1p _) @ _). apply (eisadj e a)^.

  intro eq. induction eq. simpl.
  apply moveR_pM. refine ((ap_V _ _) @ _). refine (_ @ (concat_1p _)^).
  apply inverse2. refine ((ap_pp _ _ _) @ _). apply moveR_pM.
  refine ((ap_1 _ _) @ _). apply moveL_pV. refine ((concat_1p _) @ _).
  apply (other_adj _)^.
Defined.

Theorem isequiv_equiv_to_contr_rel_equiv `{Univalence} (A B : Type) :
  IsEquiv (equiv_to_contr_rel_equiv A B).
Proof.
  refine (isequiv_adjointify _ _ _ _).
  intro R. destruct R as [R [f g]].
  refine (equiv_adjointify _ _ _ _).
  intro a. apply (center _ (f a)).1.
  intro b. apply (center _ (g b)).1.
  
  intro b. simpl. 
  destruct (center {a : A & R a b}) as [a p]. simpl.
  destruct (center {b0 : B & R a b0}) as [b' q]. change b with (b; p).1.
  apply (ap pr1). apply allpath_hprop.

  intro a. simpl.
  destruct (center {b : B & R a b}) as [b q]. simpl.
  destruct (center {a0 : A & R a0 b}) as [a' p]. 
  change a with (@pr1 _ (fun a' => R a' b) (a; q)).
  apply (ap pr1). apply allpath_hprop.

  intro R. apply path_sigma_hprop. destruct R as [R [f g]]. simpl.
  apply path_forall; intro a. apply path_forall; intro b.
  destruct (center {b0 : B & R a b0}) as [b' p]. simpl. 
  apply path_universe_uncurried.
  refine (equiv_adjointify _ _ _ _).
  intro eq. apply (transport _ eq). apply p.
  intro q. change b with (b; q).1. change b' with (b'; p).1. apply (ap pr1).
  refine (path_contr _ _). apply (f a).
  intro q. refine ((fiber_path (path_contr (b'; p) (b; q))) @ _). reflexivity.
  intro eq. induction eq. simpl. refine (_ @ (ap_1 _ _)). f_ap.
  refine (path_contr _ _). refine (contr_paths_contr _ _). apply (f a).

  intro e. simpl. apply path_equiv. simpl. reflexivity.
Defined.

Definition qinv {A B : Type} (f : A -> B) :=
  {g : B -> A & (f o g == idmap) * (g o f == idmap)}.

Definition qinv_isequiv A B (f : A -> B) (p : qinv f) : IsEquiv f
  := isequiv_adjointify f p.1 (fst p.2) (snd p.2).

Definition isequiv_qinv : forall A B (f : A -> B), IsEquiv f -> qinv f.
Proof.
  intros A B f p. destruct p.
  exists equiv_inv. split. apply eisretr. apply eissect.
Defined.

Definition isequiv' {A B} (f : A -> B) :=
  (forall a, Contr {b : B & f a = b}) * (forall b, Contr {a : A & f a = b}).

Theorem ex4_2_i A B (f : A -> B) : qinv f -> isequiv' f.
Proof.
  intro p. apply qinv_isequiv in p. 
  set (Hf := BuildEquiv A B f p).
  set (HR := equiv_to_contr_rel_equiv A B Hf).
  set (R := pr1 HR). 
  set (Q := pr2 HR).
  split. apply (fst Q). apply (snd Q).
Defined.

Theorem ex4_2_ii A B (f : A -> B) : isequiv' f -> qinv f.
Proof.
  intro p. destruct p as [sect retr].
  transparent assert (g : (B -> A)).
  intro b. destruct (retr b). apply center.1.
  exists g. split.
  unfold compose, g. intro b. destruct (retr b). apply center.2.
  unfold compose, g. intro a. destruct (retr (f a)). 
  change a with (a; 1).1. apply (ap pr1 (contr (a; 1))).
Defined.

Lemma hprop_prod : forall A, IsHProp A -> forall B, IsHProp B -> IsHProp (A * B).
Proof.
  intros A HA B HB z z'.
  apply (trunc_equiv (equiv_path_prod z z')).
Defined.

Theorem ex4_2_iii A B (f : A -> B) : IsHProp (isequiv' f).
Proof.
  unfold isequiv'.
  apply hprop_prod; apply hprop_dependent; intro; apply hprop_contr.
Defined.
  

(** %\exer{4.3}{147}% 
Reformulate the proof of Lemma 4.1.1 without using univalence.
*) 

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
  assert ((w.1.1; ap g (base_path w.2)) = w.1).
  unfold hfiber in w.
  apply (@path_sigma A (fun x:A => (g o f) x = g b) 
                     (w.1.1; ap g (base_path w.2))
                     w.1
                     1).
  simpl. 
  (*
  apply (@hfiber_triangle B C g (g b) (b; 1) (f w.1.1; w.1.2) w.2^).
                     
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
  *)
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
  
Definition Bool_Bool_to_a_a : 
  ((Bool:Type) <~> (Bool:Type)) -> 
  (((Bool:Type); min1 1):{A : Type & Brck ((Bool:Type) = A)}) 
  =
  (((Bool:Type); min1 1):{A : Type & Brck ((Bool:Type) = A)}).
  intros.
  apply path_sigma_hprop. simpl.
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
  (* Coq update broke this
  set (q := (path_sigma_hprop a a ((qinv_univalence Bool Bool).1 (lnot; r)))).
  assert {f : forall x, x = x & (f a) = q}.
  apply Lemma412.
  apply (ex3_1' ((Bool:Type) <~> (Bool:Type))).
  refine (equiv_adjointify Bool_Bool_to_a_a a_a_to_Bool_Bool _ _);
  unfold Bool_Bool_to_a_a, a_a_to_Bool_Bool.
  intro p. simpl.
   *)
Admitted.
  
End Exercise4_6.
