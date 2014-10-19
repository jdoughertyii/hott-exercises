(* begin hide *)
Require Export HoTT Ch08.
(* end hide *)
(** printing <~> %\ensuremath{\eqvsym}% **)
(** printing <~=~> %\ensuremath{\cong}% **)
(** printing == %\ensuremath{\sim}% **)
(** printing ^-1 %\ensuremath{^{-1}}% **)
(** * Category theory *)

Require Import categories.
Local Open Scope morphism_scope.
Local Open Scope category_scope.


(** %\exer{9.1}{334}% 
For a precategory $A$ and $a : A$, define the slice precategory $A / a$.  Show
that if $A$ is a category, so is $A / a$.
*)

(** %\soln%
For the type of objects $(A / a)_{0}$, take 
%\[
  (A / a)_{0} \defeq \sm{b : A} \hom_{A}(b, a)
\]%
For $(b, f), (c, g) : (A / a)$, a morphism $h$ is given by the commutative
triangle
%\[\xymatrix{
  b \ar[dr]_{f} \ar[rr]^{h} & & c \ar[dl]^{g} \\
  & a &
}\]%
so
%\[
  \hom_{(A/a)}((b, f), (c, g)) \defeq \sm{h : \hom_{A}(b, c)} (f = g \circ h)
\]%
The identity morphisms $1_{(b,f)} : \hom_{A/a}((b, f), (b, f))$ are given by
$1_{b} : \hom_{A}(b, b)$, along with the proof that $f = f \circ 1_{b}$ from
the precategory $A$.  Composition in $A / a$ is just composition in $A$,
along with associativity of composition in $A$.  Since the unit and composition
in $A / a$ are really just those from $A$ with some contractible data added,
axioms (v) and (vi) follow directly.

The interesting bit is to show that if $A$ is a category, then so is $A / a$.
So suppose that there is an equivalence
%\[
  \idtoiso_{A} : \eqv{(a =_{A} b)}{(a \cong_{A} b)}
\]%
We want to construct a map
%\[
  \left((b, f) \cong_{A/a} (c, g)\right) \to \left((b, f) =_{A/a} (c, g)\right)
\]%
that is a quasi-inverse to $\idtoiso_{A/a}$.  So suppose that $i : ((b, f)
\cong (c, g))$.  Then $\fst(i) : \hom_{A}(b, c)$ is also iso, with inverse
$\fst(i^{-1}) : \hom_{A}(c, b)$.  Since $\idtoiso_{A}$ is an equivalence, we
obtain an element $\isotoid_{A}(\fst(i)) : b =_{A} c$.  So now we need to
show that
%\[
  \transfib{\hom_{A}(-, a)}{\isotoid_{A}(\fst(i))}{f} = g = f \circ
  \fst(i^{-1})
\]%
by the fact that $i$ is iso.  By Lemma 9.1.9, we can rewrite the left as
%\[
f \circ \idtoiso_{A}(\isotoid_{A}(\fst(i)))^{-1} = f \circ
  \fst(i^{-1})
\]%
and this follows from $\fst(i)^{-1} = \fst(i^{-1})$ and $\idtoiso \circ
\isotoid \sim \idfunc{}$.

To show that this is a quasi-inverse, suppose that $i : ((b, f) \cong (c, g))$,
and let $F(i) : ((b, f) = (c, g))$ be the map we just constructed.  We want to
show that $\idtoiso_{A/a}(F(i)) = i$.  An isomorphism is determined by its
underlying map, and an arrow in $A/a$ is determined by the underlying arrow in
$A$, so we just need to show that $\fst(\idtoiso_{A/a}(F(i))) = \fst(i)$.
*)

Module my_slice.

Section my_slice_parts.
Variable A : PreCategory.
Variable a : A.

Record object := 
  {b : A;
   f : morphism A b a}.

Local Notation object_sig_T := ({b : A | morphism A b a}).

Lemma issig_object : object_sig_T <~> object.
Proof.
  issig (@Build_object) (@b) (@f).
Defined.

Lemma path_object (bf cg : object)
: forall (eq : bf.(b) = cg.(b)), 
    transport (fun X => morphism A X _) eq bf.(f) = cg.(f)
    -> bf = cg.
Proof.
  destruct bf, cg; simpl.
  intros; path_induction; reflexivity.
Defined.

Definition path_object_uncurried (bf cg : object)
  : {eq : bf.(b) = cg.(b) &
      transport (fun X => morphism A X _) eq bf.(f) = cg.(f)} 
    -> bf = cg
  := fun H => path_object bf cg H.1 H.2.
    
Record morphism (bf cg : object) := 
  {h : Category.Core.morphism A (bf.(b)) (cg.(b));
   p : (bf.(f)) = (cg.(f)) o h}.

Local Notation morphism_sig_T bf cg :=
  ({ h : Category.Core.morphism A (bf.(b)) (cg.(b))
   | (bf.(f)) = (cg.(f)) o h}).

Lemma issig_morphism bf cg : (morphism_sig_T bf cg) <~> morphism bf cg.
Proof.
  issig (@Build_morphism bf cg)
        (h bf cg)
        (p bf cg).
Defined.

Lemma path_morphism bf cg (ip jq : morphism bf cg)
  : (h _ _ ip) = (h _ _ jq) -> ip = jq.
Proof.
  destruct ip, jq; simpl. 
  intro; path_induction.
  f_ap.
  exact (center _).
Defined.

Definition compose bf cg dh
           (ip : morphism cg dh) (jq : morphism bf cg)
  : morphism bf dh.
Proof.
  exists ((h _ _ ip) o (h _ _ jq)).
  refine (_ @ (associativity _ _ _ _ _ _ _ _)).
  transitivity (f cg o (h _ _ jq)).
  apply p. f_ap. apply p.
Defined.

Definition identity x : morphism x x.
Proof.
  exists (identity (x.(b))). 
  apply (right_identity _ _ _ _)^.
Defined.

End my_slice_parts.

Local Ltac path_slice_t :=
  intros;
  apply path_morphism;
  simpl;
  auto with morphism.

Definition slice_precategory (A : PreCategory) (a : A) : PreCategory.
Proof.
  refine (@Build_PreCategory (object A a)
                             (morphism A a)
                             (identity A a)
                             (compose A a)
                             _ _ _ _);
  try path_slice_t.
  intros s d. refine (trunc_equiv (issig_morphism A a s d)).
Defined.

Lemma sliceiso_to_iso (A : PreCategory) (a : A) 
      (bf cg : slice_precategory A a) :
  (bf <~=~> cg) -> ((b _ _ bf) <~=~> (b _ _ cg)).
Proof.
  intro H.
  destruct bf as [b f], cg as [c g].
  destruct H as [i H].
  destruct i as [i eq].
  apply Morphisms.issig_isomorphic.
  exists i.
  destruct H as [ii ri li].
  destruct ii as [ii eq'].
  refine (@Category.Build_IsIsomorphism _ _ _ i _ _ _).
  apply ii. 
  simpl in *. apply (ap (h _ _ _ _)) in ri. apply ri.
  simpl in *. apply (ap (h _ _ _ _)) in li. apply li.
Defined.
    
  
(*
(* This should really just be an application of [idtoiso_of_transport] *)
Lemma Lemma9_1_9 (A : PreCategory) (a a' b b' : A) (p : a = a') (q : b = b')
      (f : Category.morphism A a b) :
  transport (fun z : A * A => Category.morphism A (fst z) (snd z)) 
            (path_prod (a, b) (a', b') p q) f
  =
  (@morphism_isomorphic _ _ _ (idtoiso _ q)) o f o (idtoiso _ p)^-1.
Proof.
  path_induction.
  refine (_ @ (right_identity _ _ _ _)^).
  refine (_ @ (left_identity _ _ _ _)^).
  reflexivity.
Defined.
*)

(*
Theorem slice_cat_if_cat (A : PreCategory) (a : A) 
  : (IsCategory A) -> (IsCategory (slice_precategory A a)).
Proof.
  intro H.
  intros bf cg.
  destruct bf as [b f], cg as [c g].
  refine (isequiv_adjointify _ _ _ _).
  intro iso. 
  destruct iso as [[iso iso_comm] [[iso_inv iso_inv_comm] r_inv l_inv]].
  apply path_object_uncurried. 
  simpl in *.
  transparent assert (i : (b <~=~> c)).
    refine (@Build_Isomorphic _ b c iso _).
    refine (Build_IsIsomorphism _ _ _ _ iso_inv _ _).
    apply (ap (h _ _ _ _) r_inv). apply (ap (h _ _ _ _) l_inv).
  transparent assert (eq : (b = c)). apply H. apply i. exists eq. 
  unfold eq. 
  transitivity (
    transport (fun z => Category.morphism A (fst z) (snd z)) 
              (path_prod (b, a) (c, a) ((isotoid A b c) i) 1) f
  ).
  refine (_ @ (transport_path_prod _ _ _ _ _ _ _ _)^). reflexivity.
  refine ((Lemma9_1_9 _ _ _ _ _ _ _ _) @ _). simpl.
  refine ((associativity _ _ _ _ _ _ _ _) @ _).
  refine ((left_identity _ _ _ _) @ _).
  refine (_ @ iso_inv_comm^). 
  f_ap.
  apply iso_moveR_V1.
  refine ((@right_inverse _ _ _ _ i)^ @ _).
  (* this is just voodoo, basically *)
  f_ap. symmetry. destruct (H b c). rewrite <- (eisretr i). simpl. f_ap.

  intro iso. 
  apply path_isomorphic. simpl.
  destruct iso as [[iso iso_comm] [[iso_inv iso_inv_comm] r_inv l_inv]].
  apply path_morphism.
  simpl in *.
  path_induction. simpl in *.
Admitted.
*)
  
  

End my_slice.
  



(** %\exer{9.2}{334}% 
For any set $X$, prove that the slice category $\uset/X$ is equivalent to the
functor category $\uset^{X}$, where in the latter case we regard $X$ as a
discrete category.
*) 

(** %\soln%
Because $\uset$ is a category, so are $\uset/X$ (by the previous exercise) and
$\uset^{X}$ (by Theorem 9.2.5).  So it suffices to show that there is an
isomorphism of categories $F : A \to B$.  Define $F(f) \defeq \hfib{f}{-}$ and
%\begin{align*}
  F(h) \defeq (a, p) \mapsto \left(\fst(h)(a), \happly(\snd(h)^{-1},a) \ct
  p)\right) 
\end{align*}%
for $f : \uset/X$ and $h : \hom_{\uset/X}(f, g)$.  In topological terms, the
bundle $f : A \to X$ gets set to its fiber map, and the bundle map $h$ gets set
to the pullback.  

To show that $F_{0} : (\uset/X)_{0} \to (\uset^{X})_{0}$ is an equivalence of
types, we need a quasi-inverse.  Suppose that $G : \uset^{X}$, and define
$F^{-1}_{0}(G) \defeq \left(\sm{x:X}G(x), \fst\right) : \uset/X$.  That is, we
take the disjoint union of all the fibers to reconstruct the bundle.  Now to
show that this is a quasi-inverse.  Suppose that $(A, f) : \uset/X$.  Then
%\[
  F^{-1}(F(A, f)) 
  \equiv \left(\sm{x:X}\sm{a:A}(f(a) = x), \fst\right)
\]%
Now, we have
%\[
  e : 
  \sm{x:X} \sm{a:A} (f(a) = x)
  \eqvsym
  \sm{a:A} \sm{x:X} (f(a) = x)
  \eqvsym
  \sm{a:A} \unit
  \eqvsym
  A
\]%
So $\ua(e) : \fst(F^{-1}(F(A, f))) = A$.  Now we must show
%\[
  \transfib{\hom_{\uset}(-, X)}{\ua(e)}{\fst} = f
\]%                      
Suppose that $a:A$.  Applying the left side to $a$, we get
%\begin{align*}
  \left(\transfib{\hom_{\uset}(-,X)}{\ua(e)}{\fst}\right)(a)
  &=
  \transfib{X}{\ua(e)}{\fst(\transfib{X \mapsto X}{\ua(e)^{-1}}{a})}
  \\&=
  \fst(\transfib{X \mapsto X}{\ua(e)^{-1}}{a})
  \\&=
  \fst(e^{-1}(a))
  \\&=
  \fst(f(a), (a, \refl{f(a)}))
  \\&=
  f(a)
\end{align*}%
So by function extensionality, our second components are equal, and
$F^{-1}(F(A, f)) = (A, f)$.

Suppose instead that $G : \uset^{X}$.  Then
%\[
  F(F^{-1}(G)) \equiv \hfib{\fst}{-}
\]%
which we must show is equal to $G$.  Identity of functors is determined by
identity of the functions $X \to \uset$ and the corresponding functions on
hom-sets.  For the first, by function extensionality it suffices to show that
%\[
  G(x)
  =
  \sm{z : \sm{x:X}G(x)}(\fst(z) = x)
\]%
for any $x : X$.  Any by univalence, it suffices to show that 
%\[
  G(x)
  \eqvsym
  \sm{z : \sm{x':X}G(x')}(\fst(z) = x)
\]%
which is true:
%\begin{align*}
  \sm{z : \sm{x':X}G(x')}(\fst(z) = x)
  &\eqvsym \sm{x':X}\sm{g':G(x')}(x'=x)
  \\&\eqvsym \sm{x':X}\sm{g:G(x)}(x'=x)
  \\&\eqvsym \sm{g:G(x)}\sm{x':X}(x'=x)
  \\&\eqvsym \sm{g:G(x)}\unit
  \\&\eqvsym G(x)
\end{align*}%
For the function on the hom-set, we again use function extensionality.  Let $h
: \prd{x:X} \hfib{\fst}{x} = G(x)$ be the path we just constructed, and let
$x, x' : X$.  We need to show that
%\[
  (h(x), h(x'))_{*}\hfib{\fst}{-} = G 
  : \hom_{X}(x, x') \to \hom_{\uset}(G(x), G(x'))
\]%
Since $X$ is a discrete category, we have $\hom_{X}(x, x') \defeq (x = x')$.
By function extensionality, it suffices to show that for any $p : x = x'$,
%\[
  (h(x), h(x'))_{*}\hfib{\fst}{p} = G(p)
\]%
By path induction, it suffices to consider the case where $x \equiv x'$ and $p
\equiv \refl{x}$.  Then we have
%\[
  (h(x), h(x))_{*}\hfib{\fst}{\refl{x}}
  =
  (h(x), h(x))_{*}1
  = 
  \idtoiso(h(x)) \circ 1 \circ \idtoiso(h(x))^{-1}
  =
  1
  =
  G(\refl{x})
\]%
So $F(F^{-1}(G)) = G$.  Thus $F$ and $F^{-1}$ are quasi-inverses, so
%\[
  F : \uset/X \eqvsym \uset^{X}
\]%
*)


(** %\exer{9.3}{334}% 
Prove that a functor is an equivalence of categories if and only if it is a
%\emph{right}% adjoint whose unit and counit are isomorphisms.
*) 

(** %\soln%
A functor $F : A \to B$ is a right adjoint if there exist
 - A functor $G : B \to A$,
 - A natural transformation $\epsilon : GF \to 1_{A}$
 - A natural transformation $\eta : 1_{B} \to FG$
 - $(F\epsilon)(\eta F) = 1_{F}$
 - $(\epsilon G)(G\eta) = 1_{G}$

%\noindent%
Suppose that $F : \eqv{A}{B}$.  Then it is a left adjoint, so we have a
functor $G : B \to A$, a unit $\eta : 1_{A} \to GF$, a counit $\epsilon : FG
\to 1_{B}$, and the triangle identities $(\epsilon F)(F \eta) = 1_{F}$ and $(G
\epsilon)(\eta G) = 1_{G}$.  Furthermore, $\eta : 1_{A} \cong GF$ and $\epsilon
: FG \cong 1_{B}$.  Thus there are natural transformations $\eta^{-1} : GF \to
1_{A}$ and $\epsilon^{-1} : 1_{B} \to FG$, and we have for all $a : A$
%\[
  \left((F\eta)(F\eta^{-1})\right)_{a}
  =
  (F\eta)_{a}(F\eta^{-1})_{a}
  =
  F(\eta_{a}) \circ F(\eta^{-1}_{a})
  =
  F(\eta_{a} \circ \eta^{-1}_{a})
  =
  F(1_{a})
  =
  1_{Fa}
  =
  (1_{F})_{a}
\]%
and
%\[
  \left((\epsilon^{-1}F)(\epsilon F)\right)_{a}
  =
  (\epsilon^{-1}F)_{a}(\epsilon F)_{a}
  =
  \epsilon^{-1}_{Fa} \circ \epsilon_{Fa}
  =
  1_{Fa}
  =
  (1_{F})_{a}
\]%
So by function extensionality $(F\eta)(F\eta^{-1}) = 1_{F}$ and
$(\epsilon^{-1}F)(\epsilon F) = 1_{F}$.  Thus
%\begin{align*}
  (F\eta^{-1})(\epsilon^{-1}F)
  &=
  (\epsilon F)(F\eta)
  (F\eta^{-1})(\epsilon^{-1}F)
  (\epsilon F)(F \eta)
  =
  (\epsilon F)
  (F \eta)
  =
  1_{F}
  \\
  (\eta^{-1}G)(G\epsilon^{-1})
  &=
  (G\epsilon)(\eta G)
  (\eta^{-1}G)(G\epsilon^{-1})
  (G\epsilon)(\eta G)
  =
  (G\epsilon)
  (\eta G)
  =
  1_{G}
\end{align*}%
So $(G, \eta^{-1}, \epsilon^{-1})$ makes $F$ a right adjoint.


Suppose instead that $F$ is a right adjoint by $(G, \epsilon, \eta)$, and that
$\eta$ and $\epsilon$ are isomorphisms.  To show that it is an equivalence of
categories, we have to show that it is a left adjoint with isomorphisms for the
unit and counit.  We have $G : B \to A$, $\epsilon^{-1} : 1_{A} \to GF$, and
$\eta^{-1} : FG \to 1_{B}$, and these natural transformations are isos, meaning
that just need to show that the triangle identity holds here.  We have
%\begin{align*}
  (\eta^{-1}F)(F\epsilon^{-1})
  &=
  (F\epsilon)(\eta F)
  (\eta^{-1}F)(F\epsilon^{-1})
  (F\epsilon)(\eta F)
  =
  (F\epsilon)
  (\eta F)
  =
  1_{F}
  \\
  (G \eta^{-1})(\epsilon^{-1} G)
  &=
  (\epsilon G)(G \eta)
  (G \eta^{-1})(\epsilon^{-1} G)
  (\epsilon G)(G \eta)
  =
  (\epsilon G)(G \eta)
  =
  1_{G}
\end{align*}%
and so $(G, \eta^{-1}, \epsilon^{-1})$ makes $F$ a left adjoint, hence an
equivalence of categories.
*)

(** %\exer{9.4}{334}% 
Define the notion of pre-2-category.  Show that precategories, functors, and
natural transformations as defined in %\S9.2% form a pre-2-category.  Similarly,
define a pre-bicategory by replacing the equalities (such as those in Lemmas
9.2.9 and 9.2.11) with natural isomorphisms satisfying analogous coherence
conditions.  Define a function from pre-2-categories to pre-bicategories, and
show that it becomes an equivalence when restricted and corestricted to those
whose hom-precategories are categories.
*)

(** %\soln%
A pre-2-category $A$ consists of
%\begin{enumerate}
  \item A type $A_{0}$ of 0-cells
  \item For all $a, b : A$, a precategory $C(a, b)$ whose objects are 1-cells
  and whose morphisms are 2-cells.  Composition in this precategory is denoted
  $\circ_{1}$ and called vertical composition.
  \item For all $a : A$, an object $1_{a} : C(a, a)$.
  \item For all $a, b, c : A$, a functor $\circ_{0} : C(b, c) \to C(a, b) \to
  C(a, c)$ called horizontal composition, which is associative and takes
  $1_{A}$ and $1_{1_{A}}$ as identities, for which the analogues of Lemmata
  9.2.10 and 9.2.11 hold.
\end{enumerate}%

To check that precategories, functors, and natural transformations form a
pre-2-category, let precategories form the type of 0-cells.  To each pair of
precategories $A, B$, we have the functor precategory $B^{A}$, given by
definition 9.2.3.  For all precatgories $A$, let $1_{A} : A^{A}$ be the
identity functor.  For horizontal composition we have composition of functors,
which is associative by Lemma 9.2.9 and takes $1_{A}$ as an identity by Lemma
9.2.11.  So we're done.

A pre-bicategory $A$ consists of
%\begin{enumerate}
  \item A type $A_{0}$ of 0-cells
  \item For all $a, b : A$, a precategory $C(a, b)$ whose objects are 1-cells
  and whose morphisms are 2-cells.  Composition in this precategory is denoted
  $\circ_{1}$ and called vertical composition.
  \item For all $a : A$, an object $1_{a} : C(a, a)$.
  \item For all $a, b, c : A$, a functor $\circ_{0} : C(b, c) \to C(a, b) \to
  C(a, c)$ called horizontal composition.
  \item For all $a, b : A$ and $f : C(a, b)$, isomorphisms $\rho_{f} : f
  \circ_{0} 1_{a} \cong f$ and $\lambda_{f} : 1_{b} \circ_{0} f \cong f$.
  \item For all $a, b, c, d : A$, $f : C(a, b)$, $g : C(b, c)$, and $h : C(c,
  d)$, an isomorphism $\alpha_{h, g, f} : (h \circ_{0} g) \circ_{0} f \cong h
  \circ_{0} (g \circ_{0} f)$.
  \item Mac Lane's pentagon commutes.  For all $a, b, c, d, e : A$
  $f : C(a, b)$, $g : C(b, c)$, $h : C(c, d)$, and $i : C(d, e)$,
  \[\xymatrix@=1in{
    ((i \circ_{0} h) \circ_{0} g) \circ_{0} f
    \ar[r]^{\alpha_{i, h, g}\circ_{0} 1_{f}}
    \ar[d]_{\alpha_{i \circ_{0} h, g, f}}
    & 
    (i \circ_{0} (h \circ_{0} g)) \circ_{0} f 
    \ar[r]^{\alpha_{i, h \circ_{0} g, f}}  
    &
    i \circ_{0} ((h \circ_{0} g) \circ_{0} f)
    \ar[d]^{1_{i} \circ_{0} \alpha_{h, g, f}} \\
    (i \circ_{0} h) \circ_{0} (h \circ_{0} f)
    \ar[rr]_{\alpha_{i, h, g \circ_{0} f}}
    & & 
    i \circ_{0} (h \circ_{0} (g \circ_{0} f))
  }\]
  \item Identity and associativity commute:
  \[\xymatrix{
  (g \circ_{0} 1_{b}) \circ_{0} f
  \ar[rr]^{\alpha_{g, 1_{b}, f}}
  \ar[rd]_{\rho_{g}\circ_{0} 1_{f}}
  & &
  g \circ_{0} (1_{b} \circ_{0} f)
  \ar[dl]^{1_{b} \circ_{0} \lambda_{f}} \\
  & g \circ_{0} f
  }\]
\end{enumerate}%
The last two conditions can also be seen as Lemmata 9.2.10 and 9.2.11 with the
equalities replaced by isomorphisms.

Given a pre-2-category $A$, we can obtain a pre-bicategory using $\idtoiso$.
The type of 0-cells is the same, as are the precategories $C(a, b)$, the
identities $1_{a}$, and the functor $\circ_{0}$.  For a pre-2-category we have
$\bar{\rho}_{f} : f \circ_{0} 1_{a} = f$ and $\bar{\lambda}_{f} : 1_{b}
\circ_{0} f = f$, so $\rho_{f} \defeq \idtoiso(\bar{\rho}_{f}) : f \circ_{0}
1_{a} \cong f$ and $\lambda_{f} \defeq \idtoiso(\bar{\lambda}_{f}) : 1_{b}
\circ_{0} f \cong f$.  Similarly, we have $\bar{\alpha}_{h, g, f} : (h
\circ_{0} g) \circ_{0} f = h \circ_{0} (g \circ_{0} f)$ and $\alpha_{h, g, f}
\defeq \idtoiso(\bar{\alpha}_{h, g, f}) : (h
\circ_{0} g) \circ_{0} f \cong h \circ_{0} (g \circ_{0} f)$.  The coherence
conditions follow from Lemmata 9.2.10 and 9.2.11; since $\idtoiso(p \ct q) =
\idtoiso(q) \circ \idtoiso(p)$, applying $\idtoiso$ everywhere in these lemmata
give the commuting pentagon and triangle.

Finally, restrict and corestrict to pre-2-categories and pre-bicategories whose
hom-precategories are categories.  We need to construct a quasi-inverse to the
map just given, which will basically be systematic application of $\isotoid$.
The type of 0-cells, $C(a, b)$, $1_{a}$, and $\circ_{0}$ remain the same.  From
(v) we have $\rho_{f} : f \circ_{0} 1_{a} \cong f$, hence $\bar{\rho}_{f}
\defeq \isotoid(\rho_{f}) : f \circ_{0} 1_{a} = f$, and $\lambda_{f} : 1_{b}
\circ_{0} f \cong f$, hence $\bar{\lambda_{f}} \defeq \isotoid(\lambda_{f}) :
1_{b} \circ_{0} f = f$.  Applying $\isotoid$ to everything in sight gives the
rest of condition (iv) on pre-2-categories.

These two processes are clearly quasi-inverses, which follows from the fact
that $\idtoiso$ is an equivalence.
*)

(** %\exer{9.5}{334}% 
Define a 2-category to be a pre-2-category satisfying a condition analogous to
that of Definition 9.1.6.  Verify that the pre-2-category of categories $\ucat$
is a 2-category.  How much of this chapter can be done internally to an
arbitrary 2-category?
*)

(** %\exer{9.6}{334}% *)
(** %\exer{9.7}{334}% *)
(** %\exer{9.8}{334}% *)

(** %\exer{9.9}{334}% 
Prove that a function $X \to Y$ is an equivalence if and only if its image in
the homotopy category of Example 9.9.7 is an isomorphism.  Show that the type
of objects of this category is $\brck{\UU}_{1}$.
*)

(** %\exer{9.10}{335}% *)
(** %\exer{9.11}{335}% *)

(** %\exer{9.12}{335}% 
Let $X$ and $Y$ be sets and $p : Y \to X$ a surjection
%\begin{enumerate}
  \item Define, for any precategory $A$, the category $\mathrm{Desc}(A, p)$ of
  descent data in $A$ relative to $p$.
  \item  Show that any precategory $A$ is a prestack for $p$, i.e.~the
  canonical functor $A^{X} \to \mathrm{Desc}(A, p)$ is fully faithful.
  \item Show that if $A$ is a category, then it is a stack for $p$,
      i.e.~$A^{X} \to \mathrm{Desc}(A, p)$ is an equivalence.
  \item Show that the statement ``every strict category is a stack for every
      surjection of sets'' is equivalent to the axiom of choice.
\end{enumerate}%
*)
