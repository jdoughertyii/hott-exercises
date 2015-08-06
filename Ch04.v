(* begin hide *)
Require Export HoTT Ch03.
Require Import hit.TwoSphere.
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

(** %\soln%
If $f : A \to B$ is an equivalence, then this type is equivalent to
$\prd{x:A}(\refl{x} = \refl{x})$.  The idea is that the extra half-adjoint
data pins down the path $x = x$ to $\refl{x}$, but the further data allows for
nontrivial paths $\refl{x} = \refl{x}$. To fix this one would have to
add another higher coherence condition.

To prove this, suppose that $e : \isequiv(f)$, so $(f, e) : \eqv{A}{B}$.  By
univalence, we may assume that $(f, e)$ is of the form $\idtoeqv(r)$ for some
$r : A = B$, and by path induction we can assume this is $\refl{A}$, so
$\idtoeqv(r)$ is $\idfunc{A}$.  Now our type reduces to
%\[
  \sm{g:A \to A} 
  \sm{\eta : g \sim \idfunc{A}}
  \sm{\epsilon : g \sim \idfunc{A}}
  \left(\eta \sim \epsilon \right)
    \times
  \left((\lam{x}g(\epsilon x)) \sim (\lam{x}\eta(g x))\right)
\]%
and by function extensionality and associativity of $\Sigma$ types this is
equivalent to 
%\[
  \sm{h : \sm{g:A \to A} (g = \idfunc{A})}
  \sm{\epsilon : \fst(h) = \idfunc{A}}
  \left(\snd(h) = \epsilon \right)
    \times
  \left((\lam{x}(\fst(h))(\epsilon x)) = (\lam{x}(\snd(h))((\fst(h)) x))\right)
\]%
But $\sm{g : A \to A}(g = \idfunc{A})$ is contractible with center
$(\idfunc{A}, \refl{\idfunc{A}})$, so our type is equivalent to
%\[
  \sm{\epsilon : \idfunc{A} = \idfunc{A}}
  \left(\refl{\idfunc{A}} = \epsilon \right)
    \times
  \left(\epsilon = \refl{\idfunc{A}}\right)
\]%
again by associativity, this is equivalent to 
%\[
  \sm{h: \sm{\epsilon : \idfunc{A} = \idfunc{A}} (\epsilon =
  \refl{\idfunc{A}})}
  \left(\fst(h) = \refl{\idfunc{A}}\right)
\]%
and again we can apply 3.11.9 to obtain the equivalent $\refl{\idfunc{A}} =
\refl{\idfunc{A}}$.  By function extensionality, this is equivalent to
%\[
  \prd{x:A}(\refl{x} = \refl{x})
\]%

This type is not generally a mere proposition.  Clearly one term of this type is $x
\mapsto \refl{x}$.  In the case of $X \jdeq \Sn^{2}$, we get a different
inhabitant by sending $\base$ to $\surf$.  This is a generalization of Lemmas
6.4.1 and 6.4.2 of the HoTT Book.
*)

Theorem ex4_1 `{Univalence} (A B : Type) (f : A <~> B) :
  {g : B -> A & {h : g o f == idmap & {e : f o g == idmap &
    (forall x, ap f (h x) = e (f x)) * (forall y, ap g (e y) = h (g y))}}}
  <~>
  forall x : A, @idpath _ x = @idpath _ x.
Proof.
  set (p := path_universe f).
  assert (fisp : f = equiv_path _ _ p).
    apply path_equiv. apply path_forall; intro a. simpl.
    unfold p. symmetry. apply transport_path_universe.
  clearbody p. induction p. rewrite fisp. simpl. 

  equiv_via ({g : A -> A & {h : g == idmap & {e : g == idmap &
    (h == e) 
  * ((fun y => ap g (e y)) == (fun y => h (g y)))}}}).
  refine (equiv_functor_sigma' _ _). apply equiv_idmap. intro g. simpl.
  refine (equiv_functor_sigma' _ _). apply equiv_idmap. intro h. simpl.
  refine (equiv_functor_sigma' _ _). apply equiv_idmap. intro e. simpl.
  refine (equiv_functor_prod' _ _). 
  refine (equiv_functor_forall' _ _). apply equiv_idmap. intro b. simpl.
  refine (equiv_adjointify _ _ _ _). 
    intro eq. apply ((ap_idmap _)^ @ eq).
    intro eq. apply ((ap_idmap _) @ eq).
    intro eq. hott_simpl.
    intro eq. hott_simpl.
  apply equiv_idmap.
  
  equiv_via ({g : A -> A & {h : g == idmap & {e : g == idmap &
   (h = e) * ((fun y => ap g (e y)) = (fun y => h (g y)))}}}).
  refine (equiv_functor_sigma' _ _). apply equiv_idmap. intro g. simpl.
  refine (equiv_functor_sigma' _ _). apply equiv_idmap. intro h. simpl.
  refine (equiv_functor_sigma' _ _). apply equiv_idmap. intro e. simpl.
  refine (equiv_functor_prod' _ _). 
  apply equiv_path_forall.
  apply equiv_path_forall.

  equiv_via ({h : {g : A -> A & g == idmap} & {e : h.1 == idmap &
   (h.2 = e) * ((fun y => ap h.1 (e y)) = (fun y => h.2 (h.1 y)))}}).
  refine (equiv_sigma_assoc _ _).

  transparent assert (HC : (Contr {g : A -> A & g == idmap})).
  exists (idmap; (fun x => 1)).
  intro h. destruct h as [g h].
  apply path_sigma_uncurried. simpl.
  exists (path_forall (fun x : A => x) g (fun x : A => (h x)^)).
  unfold pointwise_paths.
  apply path_forall; intro a.
  refine ((transport_forall_constant _ _ _) @ _).
  refine ((@path_forall_1_beta _ A (fun _ => A) a (fun z => z = a)
                               idmap g _ 1) @ _).
  refine ((transport_paths_l _ _) @ _).
  refine ((concat_p1 _) @ _).
  apply inv_V.
  equiv_via ({e : (center {g : A -> A & g == idmap}).1 == idmap &
   ((center {g : A -> A & g == idmap}).2 = e) 
   * ((fun y => ap (center {g : A -> A & g == idmap}).1 (e y)) 
      = (fun y => (center {g : A -> A & g == idmap}).2 
                     ((center {g : A -> A & g == idmap}).1 y)))}).
  refine (equiv_sigma_contr_base _ _ _).
  simpl. clear HC.
  
  equiv_via ({e : (fun x : A => x) == idmap & 
             {p : (fun x => 1) = e 
             & ((fun y : A => ap idmap (e y)) = (fun y : A => 1))}}).
  refine (equiv_functor_sigma' _ _). apply equiv_idmap. intro e.
  refine (equiv_adjointify _ _ _ _); simpl.
  intro p. apply (fst p; snd p).
  intro p. split. apply p.1. apply p.2.
  intro p. simpl. apply eta_sigma.
  intro p. simpl. apply eta_prod.

  equiv_via ({h : {e : (fun x:A => x) == idmap & (fun x => 1) = e} 
                    & (fun y : A => ap idmap (h.1 y)) = (fun y : A => 1)}).
  refine (equiv_sigma_assoc _ _).

  equiv_via ({h : {e : (fun x:A => x) == idmap & (fun x : A => 1) = e} 
                    & (fun y : A => h.1 y) = (fun y : A => 1)}).
  refine (equiv_functor_sigma' _ _). apply equiv_idmap. intro e. simpl.
  refine (equiv_adjointify _ _ _ _); simpl.
  intro eq. apply path_forall; intro a. refine (_ @ (apD10 eq a)).
    apply (ap_idmap _)^.
  intro eq. apply path_forall; intro a. refine ((ap_idmap _) @ _).
    apply (apD10 eq a).
  intro eq. refine (_ @ (eta_path_forall _ _ _)).
    apply (ap (path_forall _ _)). apply path_forall; intro a.
    apply moveR_Vp. refine ((apD10_path_forall _ _ _ a) @ _).
    reflexivity.
  intro eq. refine (_ @ (eta_path_forall _ _ _)).
    apply (ap (path_forall _ _)). apply path_forall; intro a.
    apply moveR_Mp. refine ((apD10_path_forall _ _ _ a) @ _).
    reflexivity.

  equiv_via ((fun y : A => (center {e : (fun x:A => x) == idmap & (fun x : A => 1) = e}).1 y) = (fun y : A => 1)).
  refine (equiv_sigma_contr_base _ _ _).

  refine (equiv_adjointify _ _ _ _).
  - intro eq. intro x. refine (_ @ (apD10 eq x)).
    apply (apD10 (center {e: (fun x:A => x) == idmap & (fun x:A => 1) = e}).2 x).
  - intro eq. apply path_forall. intro y.
    refine (_ @ (eq y)).
    apply (apD10 (center {e: (fun x:A => x) == idmap & (fun x:A => 1) = e}).2^ y).
  - intro eq. apply path_forall. intro x.
    apply moveR_Mp. refine ((apD10_path_forall _ _ _ _) @ _).
    refine (whiskerR _ (eq x)). refine (apD10_V _ x).
  - intro eq. apply (ap apD10)^-1. apply path_forall. intro x.
    refine ((apD10_path_forall _ _ _ _) @ _). apply moveR_Mp.
    refine (whiskerR _ (apD10 eq x)).
    refine (_ @ (apD10_V _ _)). f_ap. 
Defined.

Lemma not_all_sets `{Univalence} : ~ forall A, IsHSet A.
Proof.
  intro oops.
  apply idmap_bool_ne_negb.
  refine ((equiv_path_path_universe _)^ @ _).
  refine (_ @ (equiv_path_path_universe _)). f_ap.
  apply oops.
Defined.

Lemma loop_ne_1 `{Univalence} : loop <> 1.
Proof.
  intro oops.
  apply not_all_sets. intros A x y. apply hprop_allpath.
  intros p q. induction q.
  refine ((S1_rec_beta_loop A x p)^ @ _).
  refine (ap (ap _) oops).
Defined.

Lemma Book_6_4_2 `{Univalence} : {h : forall (x : S1), x = x & h <> (fun x => 1)}.
Proof.
  refine (S1_ind _ loop _; _).
  - refine ((transport_paths_lr _ _) @ _).
    refine ((ap (fun w => w @ _) (concat_Vp _)) @ _).
    refine (concat_1p _).
  - intro oops. apply loop_ne_1.
    apply (apD10 oops Circle.base).
Defined.

Definition not_all_1type `{U : Univalence} : ~ (forall A, IsTrunc 1 A).
Proof.
  intro oops. apply Book_6_4_2.2.
  refine (equiv_hprop_allpath _ _ _ _).
  refine (trunc_equiv (@paths (S1 -> S1) idmap idmap) _).
  - apply apD10.
  - refine (trunc_equiv (@equiv_idmap S1 = @equiv_idmap S1) 
                        (@path_equiv _ _ _ 1%equiv 1%equiv)^-1).
    apply hprop_allpath. refine (@set_path2 (S1 <~> S1) _ _ _).
    refine (trunc_equiv (S1 = S1) _).
    + apply equiv_path.
    + apply isequiv_equiv_path.
  - apply isequiv_apD10.
Defined.

Definition surf_ne_1 `{Univalence} : surf <> 1.
Proof.
  intro oops. apply not_all_1type.
  intros A x y p q. apply hprop_allpath. intros r s.
  induction s, p.
  refine ((S2_rec_beta_surf A x r)^ @ _).
  refine (ap (ap02 _) oops).
Defined.

Definition ap_homotopic {A B : Type} (f g : A -> B) (h : f == g)
         {x y : A} (q : x = y)
: ap f q = h x @ ap g q @ (h y)^.
Proof.
  apply moveL_pV. apply concat_Ap.
Defined.

  
Definition Book_6_4_2' `{Univalence}
: {h : forall x : S2, (idpath x) = 1 & h <> (fun x => 1)}.
Admitted.
    

Definition ex4_1' `{Univalence} : ~ IsHProp (forall x : S2, (idpath x) = 1).
Proof.
  intro oops. apply Book_6_4_2'.2.
  apply (equiv_hprop_allpath _ _ _ _).
Defined.
  

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
  apply (other_adj _ _)^.
Defined.

Theorem isequiv_equiv_to_contr_rel_equiv `{Univalence} (A B : Type) :
  IsEquiv (equiv_to_contr_rel_equiv A B).
Proof.
  refine (isequiv_adjointify _ _ _ _).
  intro R. destruct R as [R [f g]].
  refine (equiv_adjointify _ _ _ _).
  intro a. apply (center {b : B & R a b}).1.
  intro b. apply (center {a : A & R a b}).1.
  
  intro b. simpl. 
  destruct (center {a : A & R a b}) as [a p]. simpl.
  destruct (center {b0 : B & R a b0}) as [b' q]. change b with (b; p).1.
  apply (ap pr1). apply path_ishprop.

  intro a. simpl.
  destruct (center {b : B & R a b}) as [b q]. simpl.
  destruct (center {a0 : A & R a0 b}) as [a' p]. 
  change a with (@pr1 _ (fun a' => R a' b) (a; q)).
  apply (ap pr1). apply path_ishprop.

  intro R. apply path_sigma_hprop. destruct R as [R [f g]]. simpl.
  apply path_forall; intro a. apply path_forall; intro b.
  destruct (center {b0 : B & R a b0}) as [b' p]. simpl. 
  apply path_universe_uncurried.
  refine (equiv_adjointify _ _ _ _).
  intro eq. apply (transport _ eq). apply p.
  intro q. change b with (b; q).1. change b' with (b'; p).1. apply (ap pr1).
  refine (path_contr _ _). apply (f a).
  intro q. refine ((pr2_path (path_contr (b'; p) (b; q))) @ _). reflexivity.
  intro eq. induction eq. simpl.
  path_via (@ap {b : B & R a b} _ pr1 (b'; p) _ 1). f_ap.
  apply concat_Vp.

  intro e. apply path_equiv. reflexivity.
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
  unfold g. intro b. destruct (retr b). apply center.2.
  unfold g. intro a. destruct (retr (f a)). 
  apply (ap pr1 (contr (a; 1))).
Defined.

Lemma hprop_prod : forall A, IsHProp A -> forall B, IsHProp B -> IsHProp (A * B).
Proof.
  intros A HA B HB z z'.
  apply (trunc_equiv' _ (equiv_path_prod z z')).
Defined.

Theorem ex4_2_iii `{Funext} A B (f : A -> B) : IsHProp (isequiv' f).
Proof.
  unfold isequiv'.
  typeclasses eauto.
Defined.
  

(** %\exerdone{4.3}{147}% 
Reformulate the proof of Lemma 4.1.1 without using univalence.
*) 

(** %\soln%
Suppose that $f : A \to B$ such that $\qinv(f)$ is inhabited.  To show that
$\qinv(f) \eqvsym \prd{x:X}(x=x)$, note that by associativity we have
%\[
  \qinv(f) \eqvsym 
  \sm{h : \sm{g : B \to A}(f \circ g \sim \idfunc{A})}
    (\fst(h) \circ f \sim \idfunc{A})
\]%
Now, because $f$ is an equivalence, by function extensionality $f \circ g \sim
\idfunc{A}$ is equivalent to $g = f^{-1}$.  But then $\sm{g : B \to A}(g =
f^{-1})$ is contractible with center $(f^{-1}, \refl{f^{-1}})$, so we've
reduced to the type $f^{-1} \circ f \sim \idfunc{A}$.  Again by function
extensionality, this is equivalent to $\prd{x:A}(x=x)$.
*)


Theorem concat_Ap_w (A B : Type) (f g : A -> B) (p : forall x : A, f x = g x)
         (x y : A) (q : x = y)
  : ap f q  = p x @ ap g q @ (p y)^.
Proof.
  apply moveL_pV. apply concat_Ap.
Defined.


Theorem Book_4_1_1 `{Funext} (A B : Type) (f : A <~> B) :
  qinv f <~> forall x : A, x = x.
Proof.
  unfold qinv.
  equiv_via ({h : {g : B -> A & (f o g == idmap)} & (h.1 o f == idmap)}).
  refine (equiv_adjointify _ _ _ _).
  intro w. exists (w.1; fst w.2). apply (snd w.2).
  intro w. exists w.1.1. split. apply w.1.2. apply w.2.
  intro w. destruct w as [[g h] e]. reflexivity.
  intro w. destruct w as [g [h e]]. reflexivity.
  
  transparent assert (H' : (Contr {g : B -> A & f o g == idmap})).
  exists (f^-1; eisretr f). intro h. destruct h as [w h].
  apply path_sigma_uncurried. simpl.
  exists (path_forall f^-1 w (fun b : B => ap f^-1 (h b)^ @ eissect f (w b))).
  unfold pointwise_paths.
  apply path_forall; intro b.
  refine ((transport_forall_constant _ _ _) @ _).
  refine ((@path_forall_1_beta _ B (fun _ => A) b (fun z => f z = b) _ _ _ _) 
            @ _).
  refine ((transport_paths_Fl _ _) @ _).
  apply moveR_Vp. apply moveL_pM.
  refine (_ @ (ap_pp _ _ _)^).
  apply moveL_Mp. refine (_ @ (eisadj _ _)).
  apply moveR_Vp. apply moveL_pM.
  refine (_ @ (ap_compose _ _ _)).
  refine (_ @ (concat_Ap_w _ _ _ idmap (eisretr f) _ _ _)^).
  apply concat2. apply concat2. reflexivity. apply (ap_idmap _)^. reflexivity.

  equiv_via ((center {g : B -> A & f o g == idmap}).1 o f == idmap).
  refine (equiv_sigma_contr_base _ _ _).
  simpl. clear H'.

  refine (equiv_adjointify _ _ _ _).
  intro h. apply path_forall in h. intro x. refine ((eissect f _)^ @ _).
  apply (ap10 h x).
  intro h. intro x. refine ((eissect f _) @ _). apply (h x).
  intro h. apply path_forall; intro a.
  apply moveR_Vp. refine ((ap10_path_forall _ _ _ a) @ _). reflexivity.
  intro h. apply path_forall; intro a.
  apply moveR_Mp. apply concat2. reflexivity.
  refine ((ap10_path_forall _ _ _ a) @ _). reflexivity.
Defined.


(** %\exerdone{4.4}{147}% 
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
show that $\hfib{f^{*}}{b, \refl{g(b)}} \eqvsym \hfib{f}{b}$.  We have this by
the following chain of equivalences:
%\begin{align*}
  \hfib{f^{*}}{b, \refl{g(b)}}
  &\equiv
  \sm{w : \sm{a:A}(g(f(a)) = g(b))}(f^{*}(w) = (b, \refl{g(b)}))
  \\&\eqvsym
  \sm{a:A}\sm{p : g(f(a)) = g(b)}(f^{*}(a, p) = (b, \refl{g(b)}))
  \\&\equiv
  \sm{a:A}\sm{p : g(f(a)) = g(b)}((f(a), p) = (b, \refl{g(b)}))
  \\&\eqvsym
  \sm{a:A}\sm{p : g(f(a)) = g(b)}\sm{q : f(a) = b} q_{*}(p) = \refl{g(b)}
  \\&\eqvsym
  \sm{a:A}\sm{q : f(a) = b}\sm{p : g(f(a)) = g(b)} q_{*}(p) = \refl{g(b)}
  \\&\eqvsym
  \sm{a:A}\sm{q : f(a) = b}\sm{p : g(f(a)) = g(b)} p = q^{-1}_{*}(\refl{g(b)})
  \\&\eqvsym
  \sm{a:A}(f(a) = b)
  \\&\equiv
  \hfib{f}{b}
\end{align*}%

(ii) In this case it's a bit easier to come up with a chain of equivalences in
the other direction.  We have
%\begin{align*}
  \sm{w : \hfib{g}{g(b)}}\hfib{f}{\fst w}
  &\eqvsym
  \sm{b' : B}\sm{p : g(b') = g(b)} \hfib{f}{b'}
  \\&\eqvsym
  \sm{a:A}\sm{b' : B}\sm{p : g(b') = g(b)} (f(a) = b')
  \\&\eqvsym
  \sm{a:A}\sm{b' : B}\sm{p : f(a) = b'} (g(b') = g(b))
  \\&\eqvsym
  \sm{a:A}\sm{w : \sm{b':B}(f(a) = b')} (g(\fst w) = g(b))
  \\&\eqvsym
  \sm{a:A} (g(f(a)) = g(b))
  \\&\equiv
  \hfib{g \circ f}(g(b))
\end{align*}%
*)

Lemma equiv_prod_unit (A : Type) : A <~> A * Unit.
Proof.
  refine (equiv_adjointify (fun a => (a, tt)) (fun z => fst z) _ _).
  intro z. apply path_prod. reflexivity. apply eta_unit.
  intro a. reflexivity.
Defined.

Module Ex4.

Variables (A B C D : Type) (f : A -> B) (g : B -> C) (b : B).

Definition f_star (z : hfiber (g o f) (g b)) : hfiber g (g b) := 
  (f z.1; z.2).

Theorem ex4_4_i : hfiber (f_star) (b; 1) <~> hfiber f b.
Proof.
  equiv_via {a : A & {p : g (f a) = g b & (f_star (a; p) = (b; 1))}}.
  apply equiv_inverse. refine (equiv_sigma_assoc _ _). unfold f_star. simpl.

  equiv_via {a : A & {p : g (f a) = g b & {q : f a = b & 
               transport (fun x => g x = g b) q p = 1}}}.
  refine (equiv_functor_sigma_id _). intro a.
  refine (equiv_functor_sigma_id _). intro p.
  apply equiv_inverse. 
  refine (equiv_path_sigma (fun x => g x = g b) (f a; p) (b; 1)).
  
  equiv_via {a : A & {q : f a = b & {p : g (f a) = g b & 
               transport (fun x => g x = g b) q p = 1}}}.
  refine (equiv_functor_sigma_id _). intro a.
  refine (equiv_sigma_comm _ _ _).

  equiv_via {a : A & {q : f a = b & {p : g (f a) = g b & 
               p = transport (fun x => g x = g b) q^ 1}}}.
  refine (equiv_functor_sigma_id _). intro a.
  refine (equiv_functor_sigma_id _). intro p.
  refine (equiv_functor_sigma_id _). intro q.
  refine (BuildEquiv _ _ _ (isequiv_moveL_transport_V _ _ _ _)).
  
  equiv_via {a : A & {q : f a = b & Unit}}.
  refine (equiv_functor_sigma_id _). intro a.
  refine (equiv_functor_sigma_id _). intro p.
  refine equiv_contr_unit.

  refine (equiv_functor_sigma_id _). intro a.
  equiv_via ((f a = b) * Unit). refine (equiv_const_sigma_prod _ _).
  apply equiv_inverse. refine (equiv_prod_unit _).
Defined.

Theorem ex4_4_ii 
  : hfiber (g o f) (g b) <~> {w : hfiber g (g b) & hfiber f w.1}.
Proof.
  apply equiv_inverse. unfold hfiber.
  
  equiv_via {b' : B & {p : g b' = g b & {x : A & f x = b'}}}.
  apply equiv_inverse.
  refine (equiv_sigma_assoc _ _).

  equiv_via {b' : B & {x : A & {_ : g b' = g b & f x = b'}}}.
  refine (equiv_functor_sigma_id _). intro b'.
  refine (equiv_sigma_comm _ _ _).

  equiv_via {x : A & {b' : B & {_ : g b' = g b & f x = b'}}}.
  refine (equiv_sigma_comm _ _ _).
  
  refine (equiv_functor_sigma_id _). intro a.

  equiv_via {b' : B & {p : f a = b' & g b' = g b}}.
  refine (equiv_functor_sigma_id _). intro b'.
  equiv_via ((g b' = g b) * (f a = b')).
  refine (equiv_const_sigma_prod _ _).
  equiv_via ((f a = b') * (g b' = g b)).
  refine (equiv_prod_symm _ _).
  apply equiv_inverse.
  refine (equiv_const_sigma_prod _ _).
  
  
  equiv_via {w : {b' : B & f a = b'} & g w.1 = g b}.
  refine (equiv_sigma_assoc _ _).

  equiv_via (g (center {b' : B & f a = b'}).1 = g b).
  refine (equiv_sigma_contr_base _ _ _). simpl.

  refine (equiv_adjointify _ _ _ _).
  - intro eq. apply eq.
  - intro eq. apply eq.
  - intro eq. reflexivity.
  - intro eq. reflexivity.
Defined.
    
    

End Ex4.

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
This follows immediately from the assumption of function extensionality, but it
is true even without this assumption.
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
  intro p. induction p. hott_simpl.
  
  apply (isequiv_homotopic (fun p => (eisretr f (f a)) @ p @ (eisretr f (f a'))^)).
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

Module Ex6.

Hypothesis qinv_univalence : forall A B, qinv (equiv_path A B).

Theorem Book_4_9_2 (A B X : Type) (e : A <~> B) : (X -> A) <~> (X -> B).
Proof.
  destruct e as [f p].
  assert (qinv f) as q. exists f^-1. split. 
    apply (eisretr f). apply (eissect f).
  assert (A = B) as r. apply (qinv_univalence A B). 
  apply (BuildEquiv _ _ f p).
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

Lemma Book_4_1_2 `{Funext} (A : Type) (a : A) (q : a = a)
  : IsHSet (a = a) -> (forall x, Brck (a = x))
    -> (forall p : a = a, p @ q = q @ p)
    -> {f : forall (x : A), x = x & f a = q}.
Proof.
  intros eq g eta.
  transparent assert (Heq : (forall x y : A, IsHSet (x = y))).
  intros x y. 
  assert (Brck (a = x)) as p by auto. 
  assert (Brck (a = y)) as r by auto. 
  strip_truncations.
  refine (@trunc_equiv (a = a) _ _ _ _ _).
  intros s. apply (p^ @ s @ r).
  apply isequiv_concat_lr.
  set (B := fun x => {r : x = x & forall s : a = x, (r = s^ @ q @ s)}).
  transparent assert (HB : (forall x, (IsHProp (B x)))).
  intro x. assert (Brck (a = x)) as p by auto.
  strip_truncations.
  apply hprop_allpath. intros rh r'h'.
  destruct rh as [r h], r'h' as [r' h'].
  apply path_sigma_uncurried. exists ((h p) @ (h' p)^). simpl.
  apply path_forall. intro t. apply Heq.
  transparent assert (f' : (forall x, B x)).
  intro x. assert (Brck (a = x)) as p by auto. strip_truncations.
  exists (p^ @ q @ p). intro s. 
  apply moveL_pM. repeat (refine ((concat_pp_p _ _ _) @ _)).
  apply moveR_Vp. refine (_ @ (concat_pp_p _ _ _)).
  symmetry. apply eta.
  exists (fun x => (f' x).1).
  refine (((f' a).2 1) @ _).
  hott_simpl.
Defined.


(*
Theorem Book_4_1_3 `{Funext}
  : {A : Type & {B : Type & {f : A -> B & ~ IsHProp (qinv f)}}}.
Proof.
  set (X := {A : Type & Brck (Bool = A)}).
  exists X. exists X. exists idmap. intro H'.
  set (a := (Bool; tr 1) : X).
  assert (Q : (qinv (equiv_path Bool Bool))) by apply qinv_univalence.
  destruct Q as [path_equiv' [retr sect]].
  transparent assert (q : (a = a)).
    apply path_sigma_hprop. apply path_equiv'.
    apply (BuildEquiv _ _ negb isequiv_negb).
  transparent assert (e : (Bool <~> (a = a))). 
    equiv_via (Bool <~> Bool). apply equiv_bool_aut_bool.
    equiv_via (Bool = Bool).
    refine (equiv_adjointify _ _ _ _).
    apply path_equiv'. apply equiv_path.
    intro eq. apply (sect eq). intro e. apply (retr e).
    refine (equiv_adjointify _ _ _ _).
    intro eq. apply path_sigma_uncurried. exists eq. apply path_ishprop.
    intro eq. apply (pr1_path eq).
    intro eq. destruct eq.
    refine (_ @ (eta_path_sigma_uncurried _)). f_ap. 
    apply path_sigma_uncurried. exists 1. simpl. apply path_ishprop.
    intro eq.
    refine ((@pr1_path_sigma_uncurried Type _ a a _) @ _). reflexivity.
  assert (F : {f : forall x : X, x = x & f a = q}). apply Book_4_1_2.
  apply (trunc_equiv _ e).
  intro x. destruct x as [A eq]. strip_truncations. apply tr.
  unfold a. apply path_sigma_uncurried. exists eq. induction eq. reflexivity.
  intros p.
  set (b := e^-1 p). assert (pisb : p = e b). unfold b. symmetry. apply eisretr.
  set (b' := e^-1 q). assert (qisb' : q = e b'). unfold b'. symmetry. 
    apply eisretr.
    clearbody b b'.
  rewrite pisb, qisb'.
  assert (path_equiv' (BuildEquiv _ _ idmap _) = 1).
  path_via (path_equiv' (equiv_path _ _ 1)). apply sect.
  assert (path_ishprop (transport (fun A : Type0 => Brck (Bool = A)) 1 (tr 1))
       (tr 1) = 1) by apply path_ishprop.
  destruct b, b'.
  reflexivity.
  admit.
  admit.
  reflexivity.
  
  assert (Heq : (q <> 1)).
  unfold q. intro Heq.
  assert (negb <> idmap) as CX. intro h. apply (negb_no_fixpoint true).
  apply (ap10 h true). apply CX.
  path_via (equiv_fun (BuildEquiv _ _ negb _)).
  path_via (equiv_fun (BuildEquiv Bool _ idmap _)). f_ap.
  path_via (equiv_path Bool Bool (path_equiv' 
            {| equiv_fun := negb; equiv_isequiv := isequiv_negb |})).
  symmetry. apply retr.
  path_via (equiv_path Bool Bool (path_equiv'
            {| equiv_fun := idmap; equiv_isequiv := isequiv_idmap _ |})).
  f_ap.
  path_via ((path_sigma_hprop a a)^-1 (path_sigma_hprop a a (
    path_equiv' {| equiv_fun := negb; equiv_isequiv := isequiv_negb |}))).
  symmetry. apply eissect.
  path_via ((path_sigma_hprop a a)^-1 (path_sigma_hprop a a (
    path_equiv' {| equiv_fun := idmap; equiv_isequiv := isequiv_idmap _ |}))).
  f_ap.
  refine (Heq @ _).
  path_via (path_sigma_hprop a a ((path_equiv' o (equiv_path _ _)) 1)).
  rewrite (sect 1).
  path_via (path_sigma_hprop a a ((path_sigma_hprop a a)^-1 1)).
  symmetry. apply eisretr.
  apply eissect.
  apply (retr _).
  destruct F as [f eq].
  assert (Hf : (f <> (fun x => 1))).
  intro Hf. apply Heq. refine (eq^ @ _). apply (apD10 Hf a).
  assert (HP : (IsHProp (forall x : X, x = x))).
  apply (trunc_equiv' (Book_4_1_1 X X (BuildEquiv X X idmap _))).
  apply Hf. apply path_ishprop.
Admitted.
*)

(** 
(iii) $\qinv$-univalence implies that all equivalences are half-adjoint
equivalences and this because for any $p : A = B$, $\idtoeqv(p)$ is
half-adjoint.  To see this, suppose that $p : A = B$, which by induction we may
assume is $\refl{A}$.  Then $\idtoeqv(p) \equiv (\idfunc{A}, \idfunc{A},
\lam{x:A}\refl{x}, \lam{x:A}\refl{x})$, and to show that this is a half-adjoint
equivalence we must inhabit the type
%\[
\left(
  \prd{x : A}\idfunc{A}((\lam{x'}\refl{x'})x) 
             = (\lam{x'}\refl{x'})(\idfunc{A}x)
             \right)
  \equiv
  \left(
  \prd{x : A}\refl{x} = \refl{x}
  \right)
\]%
which is inhabited by reflexivity.  However, there are equivalences that aren't
half-adjoint, such as the one constructed in Exercise 4.1.
*)
  
End Ex6.
