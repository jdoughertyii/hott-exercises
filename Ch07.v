(* begin hide *)
Require Export HoTT Ch06_3.
(* end hide *)
(** printing <~> %\ensuremath{\eqvsym}% **)
(** printing == %\ensuremath{\sim}% **)
(** printing ^-1 %\ensuremath{^{-1}}% **)
(** * Homotopy $n$-types *)

(** %\exer{7.1}{250}% 
(i) Use Theorem 7.2.2 to show that if $\brck{A} \to A$ for every type $A$, then
    every type is a set.
(ii) Show that if every surjective function (purely) splits, i.e.%~%if
    $\prd{b:B}\brck{\hfib{f}{b}} \to \prd{b:B}\hfib{f}{b}$ for every $f : A \to
    B$, then every type is a set.
*) 

(** %\soln%
(i)  Suppose that $f : \prd{A:\UU}\brck{A} \to A$, and let $X$ be some type. To
apply Theorem 7.2.2, we need a reflexive mere relation on $X$ that implies
identity.  Let $R(x, y) \defeq \brck{x = y}$, which is clearly a reflexive mere
relation.  Moreoever, it implies the identity, since for any $x, y : X$ we have
%\[
  f(x = y) : R(x, y) \to (x = y)
\]%
So by Theorem 7.2.2, $X$ is a set.

*) 

(** %\exer{7.2}{250}% 
Express $\Sn^{2}$ as a colimit of a diagram consisting entirely of copies of
$\unit$.
*)

(** %\soln%
Recall that we can define $\Sn^{2} \defeq \susp\Sn^{1} \defeq \susp\susp\Sn^{0}
\defeq \susp\susp\susp\bool$.  Then note that $\eqv{\bool}{\unit + \unit}$, and
that $\susp{A}$ is the pushout of the span $\unit \leftarrow A \to \unit$.  So
we have a diagram
%\[\xymatrix{
  \unit + \unit \ar[r] \ar[d] & \unit \ar[d] & \\
  \unit \ar[r] & \Sn^{1} \ar[d] \ar[r] & \unit \ar[d] \\
  & \unit \ar[r] & \Sn^{2}
}\]%
where both squares are pushouts.  And, since the coproduct is the colimit
of the discrete diagram with two items, we can write
%\[\xymatrix{
               & \unit \ar[d] & & \\
  \unit \ar[r] & \bool \ar[r] \ar[d] & \unit \ar[d] & \\
  & \unit \ar[r] & \Sn^{1} \ar[d] \ar[r] & \unit \ar[d] \\
  & & \unit \ar[r] & \Sn^{2}
}\]%
where now every object that isn't a $\unit$ is a colimit.
*)

(** %\exer{7.3}{250}% *)

Inductive W_tree (A : Type) (B : A -> Type) : Type :=
  | sup : forall a : A, (B a -> W_tree A B) -> W_tree A B.


(** %\exer{7.4}{250}% *)
(** %\exer{7.5}{250}% *)
(** %\exer{7.6}{250}% *)
(** %\exer{7.7}{250}% *)
(** %\exer{7.8}{250}% *)
(** %\exer{7.9}{251}% *)
(** %\exer{7.10}{251}% *)
(** %\exer{7.11}{251}% *)

(** %\exer{7.12}{251}% 
Show that $X \mapsto (\lnot \lnot X)$ is a modality.
*) 

(** %\soln%
We must show that there are
%\begin{enumerate}
  \item functions $\eta^{\lnot \lnot}_{A} : A \to \lnot\lnot A$ for every type
  $A$,
  \item for every $A : \UU$ and every family $B : \lnot\lnot A \to \UU$, a
  function
  \[
    \ind{\lnot\lnot} : 
    \left(\prd{a : A}\lnot\lnot(B(\eta^{\lnot\lnot}_{A}(a)))\right)
    \to
    \prd{z : \lnot\lnot A}\lnot\lnot(B(z))
  \]
  \item A path $\ind{\lnot\lnot}(f)(\eta^{\lnot\lnot}_{A}(a)) = f(a)$ for each
  $f : \prd{a : A}\lnot\lnot(B(\eta^{\lnot\lnot}_{A}(a)))$, and
  \item For any $z, z' : \lnot \lnot A$, the function $\eta^{\lnot\lnot}_{z =
  z'} : (z = z') \to \lnot\lnot(z = z')$ is an equivalence.
\end{enumerate}%
Some of this has already been done.  The functions $\eta^{\lnot\lnot}_{A}$ were
given in Exercise 1.12; recall:
%\[
  \eta^{\lnot\lnot}_{A} \defeq \lam{a}{f}f(a)
\]%
Now suppose that we have an element $f$ of the antecedent of
$\ind{\lnot\lnot}$, and let $z : \lnot\lnot A$.  Suppose furthermore
that $g : \lnot B(z)$; we derive a contradiction.  It suffices to
construct an element of $\lnot A$, for then we can apply $z$ to obtain
an element of $\emptyt$.  So suppose that $a : A$.  Then 
%\[
  f(a) : \lnot \lnot B(\eta^{\lnot\lnot}_{A}(a))
\]%
but $\lnot X$ is a mere proposition for any type $X$, so $z =
\eta^{\lnot\lnot}_{A}(a)$, and transporting gives an element of $\lnot \lnot
B(z)$.  Applying this to $g$ gives a contradiction.

For (iii), suppose that $a : A$ and $f : \prd{a :
A}\lnot\lnot(B(\eta^{\lnot\lnot}_{A}(a)))$.  Then $f(a) : \lnot \lnot
(B(\eta^{\lnot\lnot}_{A}(a)))$, making this type contractible, giving a
canonical path $\ind{\lnot\lnot}(f)(\eta^{\lnot\lnot}_{A}(a)) = f(a)$.

Finally, for (iv), let $z, z' : \lnot\lnot A$.  Since $\lnot\lnot A$ is a mere
proposition, so is $z = z'$.  $\lnot\lnot(z = z')$ is also a mere proposition,
so if there is an arrow $\lnot\lnot(z = z') \to (z = z')$, then it is
automatically a quasi-inverse to $\eta^{\lnot\lnot}_{z = z'}$.  Such an arrow
is immediate from the fact that $\lnot \lnot A$ is a mere proposition.

The definition of a modalities in HoTT/HoTT is different from the one
in the book, in order to get better computation rules.
*)

Module Ex12.

Definition notnot_modality `{Funext} : Modality.
Proof.
  refine (Build_Modality_easy (fun A => ~ ~ A) _ _ _ _).
  - intros A a f. apply (f a).
  - intros A B f z g.
    apply z. intro a.
    refine ((transport (fun x => ~ ~ (B x)) 
                       (@allpath_hprop _ _ _ _)
                       (f a)) g).
  - intros A B f a. apply allpath_hprop.
  - intros A z z'.
    refine (isequiv_adjointify _ _ _ _).
    * intros f. apply allpath_hprop.
    * intro p. apply path_arrow; intro f. contradiction.
    * intro p. apply allpath_hprop.
Defined.

End Ex12.

  

(** %\exer{7.13}{251}% 
Let $P$ be a mere proposition
%\begin{enumerate}
\item Show that $X \mapsto (P \to X)$ is a left exact modality.
\item Show that $X \mapsto (P * X)$ is a left exact modality, where $*$ denotes
    the join.
\end{enumerate}%
*)

(** %\soln%
A left exact modality is one which preserves pullbacks as well as finite
products.  That is, if $A \times _{C} B$ is a pullback, then so is
$\modal (A \times_{C} B)$, which is to say that for all $X$,
%\[
  (X \to \modal(A \times_{C} B))
  \eqvsym
  (X \to \modal A) \times_{X \to \modal C} (X \to \modal B)
\]%
Likewise, if $A \times B$ is a product, then so is $\modal(A \times B)$;
i.e., for all $X$ we have
%\[
  \eqv{
    (X \to \modal(A \times B)) 
  }{
    (X \to \modal A) \times (X \to \modal B)
  }
\]%


%\vspace{.1in}
\noindent%
(i) Let $\modal X \defeq (P \to X)$, with $\eta^{\modal}_{A} : A \to
\modal A$ given by $\eta^{\modal}_{A}(a) \defeq \lam{p}a$.  To derive the
induction principle, suppose that $A : \UU$, $B : \modal A \to \UU$, $f :
\prd{a:A}\modal(B(\eta^{\modal}_{A}(a)))$, and $g : \modal A$.  We need to
construct an arrow $P \to B(g)$.  So suppose that $p : P$, so $g(p) : A$.  Then
$f(g(p)) : P \to B(\lam{p'}g(p))$.  But since $P$ is a mere proposition, by
function extensionality $\lam{p'}g(p) = g$, and we can transport the output of
$f(g(p))$ to obtain an element of $B(g)$, as required.

To demonstrate the computation rule, suppose that $f : \prd{a:A} P \to
B(\lam{p}a)$ and $a : A$.  Then $f(a) : P \to B(\lam{p}a)$ and $\ind{\modal
A}(f)(a) : P \to B(\lam{p}a)$.  So by function extensionality and the fact that
$P$ is a mere proposition, $\ind{\modal A}(f)(a) = f(a)$.

To show that $\eta^{\modal}_{z = z'}$ is an equivalence for all $f, g : \modal
A$, we first need an inverse.  Let $k : P \to (f = g)$, and suppose that $p :
P$.  Then $k(p) : f = g$, so $\lam{p}\happly(k(p)) : f \sim g$.  By function
extensionality, then, we have $f = g$.  These are clearly quasi-inverses.  If
$q : f = g$, then we want to show that
%\[
  \funext(\lam{p}\happly(q, p)) = q
\]%
which follows immediately from the fact that $\funext$ and $\happly$ are
inverses.  For the other direction, suppose that $k : P \to (f = g)$.  Then we
need to show that
%\[
  \lam{p}\funext(\lam{p'}\happly(k(p'), p')) = k
\]%
which we do by function extensionality.  Supposing that $p : P$, we need to
show that
%\[
  \lam{p'}\happly(k(p'), p')) = \happly(k(p))
\]%
and this follows from the fact that $P$ is a mere proposition, just as we
showed that $\lam{p'}g(p) = g$.

Now, to show that this modality is left exact, note that
%\begin{align*}
 (X \to \modal(A \times_{C} B))
 &\equiv
 (X \to P \to A \times_{C} B)
 \\&\eqvsym
 ((X \times P) \to A \times_{C} B)
 \\&\eqvsym
 ((X \times P) \to A) \times_{(X \times P) \to C} ((X \times P) \to B)
 \\&\eqvsym
 (X \to P \to A) \times_{X \to P \to C} (X \to P \to B)
 \\&\equiv
 (X \to \modal A) \times_{X \to \modal C} (X \to \modal B)
\end{align*}%
Using the cartesian closure adjunction.  Likewise,
%\begin{align*}
  (X \to \modal(A \times B))
  &\equiv
  (X \to P \to A \times B)
  \\&\eqvsym
  ((X \times P) \to (A \times B))
  \\&\eqvsym
  ((X \times P) \to A)
  \times
  ((X \times P) \to B)
  \\&\eqvsym
  (X \to P \to A)
  \times
  (X \to P \to B)
  \\&\equiv
  (X \to \modal A)
  \times
  (X \to \modal B)
\end{align*}%
By the universal property of the product.  So $\modal$ preserves both pullbacks
and finite products.

%\vspace{.1in}
\noindent%
(ii) Suppose now that $\modal X \defeq P * X$.  That is, suppose that $\modal X$ is
the pushout of the span $X \xleftarrow{\fst} X \times P \xrightarrow{\snd}
P$.  This is the higher inductive type presented by
 - a function $\inl : X \to P * X$
 - a function $\inr : P \to P * X$
 - for each $z : P \times X$ a path $\glue(z) : \inl(\fst(z)) = \inr(\snd(z))$
Note that if $P$ is contractible, then so is $\modal X$.  This is
straightforward: letting $p$ be the center of $P$, $\inl(p)$ is the center of
$\modal(X)$.  Using the induction principle for pushouts, we must first show
that for all $p' : P$, $\inl(p) = \inl(p')$, which follows from $P$'s
contractibility.  Next we need, for any $x : X$, $\inl(p) = \inr(x)$.  This
follows from $\glue((p, x)) : \inl(p) = \inr(x)$.  Finally, we must show that
for all $(p', x) : P \times X$, 
%\[
  (\inl(p) = \inl(p')) = (\inl(p) = \inr(x))
\]%
Which is pretty easy to show by some path algebra.

Now, suppose that $A : \UU$ and $B : \modal(A) \to \UU$, and let $f : \prd{a:A}
\modal(B(\eta^{\modal}_{A}(a)))$.  We use pushout induction to construct a map
$\prd{z:\modal A} \modal B(z)$.  When $z \equiv \inl(p)$, $P$ is inhabited, so
$\modal (B (z))$ is contractible and we can return its center.  When $z \equiv
\inr(a)$ then $f(a) : \modal(B(\inr(a)))$ is our element.  For the path,
suppose that $(p, x) : P \times X$.  Then $P$ is contractible, so all of its
higher path spaces are trivial and we're done.  This gives judgemental
computation rule, as well.

Finally, we need to show that $\eta^{\modal}_{z = z'}$ is an equivalence for
all $z, z' : \modal A$.  To define an inverse, suppose that $p : \modal(z =
z')$.  If $p \equiv \inl(p')$, then $P$ is contractible and so is $\modal A$,
so the higher path spaces are trivial and $z = z'$.  If $p \equiv \inr(q)$,
then $q : z = z'$ and we're done.  Finally, supposing that $(p, a) : P \times
A$, $P$ is contractible so $(z = z')$ is as well, so all the paths are trivial.
To show that these are quasi-inverses involves some minor path algebra.  Thus,
$\modal$ is a modality.

Now, to show that it is left exact.
*)

Lemma ap11_V {A B : Type} {f g : A -> B} (p : f = g) (h : forall x y : A, x = y)
      (x y : A)
  : ap11 p^ (h x y)^ = (ap11 p (h x y))^.
Proof.
  induction p.
  induction (h x y).
  reflexivity.
Defined.
                                         

Module Ex13.

Require Import ReflectiveSubuniverse.

Section OpenModality.

Context (P : hProp).

Definition open_modality `{Funext} : Modality.
Proof.
  refine (Build_Modality_easy (fun X => P -> X) _ _ _ _).
  - intros X x p. apply x.
  - intros A B f g p.
    apply (transport B (path_arrow (fun _ : P => g p) g
                                    (fun p' : P => ap g (allpath_hprop p p')))).
    apply (f (g p) p).
  - intros A B f a.
    apply path_arrow; intro p. simpl in *.
    path_via (transport B 1 (f a p)). f_ap.
    apply (ap apD10)^-1.
    apply path_forall; intro p'.
    refine ((apD10_path_arrow _ _ _ _) @ _).
    apply ap_const.
  - intros A z z'.
    refine (equiv_adjointify _ _ _ _).
    + intro f. apply path_arrow. intro p.
      apply (ap10 (f p) p).
    + intro f. apply path_arrow. intro p.
      path_via (path_arrow z z' (ap10 (f p))). f_ap.
      * apply path_forall. intro p'. f_ap. apply (ap f). apply allpath_hprop.
      * apply eta_path_arrow.
    + intro p. apply eta_path_arrow.
Defined.

Definition preserves_pullbacks (M : Modality)
  := forall (A B C : Type) (f : A -> C) (g : B -> C),
       O (pullback f g) 
         <~> 
         pullback (O_functor f) (O_functor g).

Definition preserves_products (M : Modality)
  := forall (A B : Type), O (A * B) <~> (O A * O B).


Class IsLEM (M : Modality) := 
  BuildIsLEM {
      lem_pullbacks : preserves_pullbacks M ;
      lem_products : preserves_products M
    }.

Theorem lem_open `{Funext} : IsLEM open_modality.
Proof.
  refine (BuildIsLEM _ _ _).

  (* preserves pullbacks *)
  - intros A B C f g.
    unfold pullback. 
    simpl (O {b : A & {c : B & f b = g c}}).
    equiv_via {h : P -> A & {j : P -> B & f o h == g o j}}.
    + equiv_via {h : P -> A & forall p, {b : B & f (h p) = g b}}.
      * apply equiv_inverse. refine (equiv_sigT_corect _ _).
      * refine (equiv_functor_sigma_id _). intro h.
        apply equiv_inverse. refine (equiv_sigT_corect _ _).
    + apply equiv_functor_sigma_id. intro h.
      apply equiv_functor_sigma_id. intro j.
      equiv_via (f o h = g o j). apply equiv_path_arrow.
      equiv_via ((@O_unit open_modality C) o (f o h)
                 =
                 (@O_unit open_modality C) o (g o j)).
      refine (equiv_adjointify _ _ _ _).
        intro eq. apply path_arrow. intro p. apply path_arrow. intro p'.
        apply (ap10 eq p).
        
        intro eq. apply path_arrow. intro p. 
        apply (apD10 (apD10 eq p) p).

        intro eq.
        apply (ap apD10)^-1. apply path_forall. intro p.
        refine ((apD10_path_forall _ _ _ p) @ _).
        apply (ap apD10)^-1. apply path_forall. intro p'.
        refine ((apD10_path_forall _ _ _ p') @ _).
        refine ((ap10_path_arrow _ _ _ p) @ _).
        f_ap. apply allpath_hprop.

        intro eq.
        apply (ap apD10)^-1. apply path_forall. intro p.
        refine ((apD10_path_forall _ _ _ p) @ _).
        unfold O_unit. simpl.
        rewrite apD10_path_arrow. rewrite apD10_path_arrow. reflexivity.
        
      equiv_via (@O_functor open_modality _ _ (f o h) o (O_unit P)
                 =
                 O_functor (g o j) o (O_unit P)).
      refine (equiv_adjointify _ _ _ _).
        intro eq. apply path_forall. intro p.
        refine ((O_unit_natural _ _) @ _).
        refine (_ @ (O_unit_natural _ _)^).
        apply (apD10 eq p).

        intro eq. apply path_forall. intro p.
        refine ((O_unit_natural _ _)^ @ _).
        refine (_ @ (O_unit_natural _ _)).
        apply (apD10 eq p).

        intro eq.
        apply (ap apD10)^-1. apply path_forall. intro p.
        refine ((apD10_path_forall _ _ _ p) @ _).
        apply moveR_Mp. apply moveR_pV.
        refine ((apD10_path_forall _ _ _ p) @ _).
        hott_simpl.
        
        intro eq.
        apply (ap apD10)^-1. apply path_forall. intro p.
        refine ((apD10_path_forall _ _ _ p) @ _).
        apply moveR_Vp. apply moveR_pM.
        refine ((apD10_path_forall _ _ _ p) @ _).
        hott_simpl.

      equiv_via (@O_functor open_modality _ _ (f o h) 
                 =
                 O_functor (g o j)).
      refine (equiv_adjointify _ _ _ _).
        intros eq.
        apply path_arrow. intro k. apply path_arrow. intro p.
        path_via ((@O_functor open_modality _ _ (f o h) o O_unit P) p p).
        unfold compose. f_ap. apply allpath_hprop.
        path_via ((@O_functor open_modality _ _ (g o j) o O_unit P) p p).
        apply (ap10 (ap10 eq p) p).
        unfold compose. f_ap. apply allpath_hprop.
        
        intros eq. apply path_arrow. intro p. unfold compose. f_ap.
        
        intro eq.
        apply (ap ap10)^-1. apply path_forall. intro k.
        refine ((ap10_path_arrow _ _ _ _) @ _).
        apply (ap ap10)^-1. apply path_forall. intro p.
        refine ((ap10_path_arrow _ _ _ _) @ _).
        apply moveR_Mp. apply moveR_pM.
        path_via (ap10 (apD10 eq (O_unit P p)) p).
        f_ap. refine ((ap10_path_arrow _ _ _ _) @ _). reflexivity.
        unfold ap10.
        apply moveL_pV.
        path_via (apD10 ((apD10 eq (O_unit P p)) 
                         @ (ap11 1 (allpath_hprop (O_unit P p) k))) p).
        apply inverse. apply (apD10_pp (apD10 eq (O_unit P p)) _ p).
        apply moveL_Vp. 
        refine ((apD10_pp (ap11 1 (allpath_hprop k (O_unit P p))) _ p)^ @ _).
        f_ap. induction eq. hott_simpl.
        apply moveR_pM. refine (_ @ (concat_1p _)^).
        refine (_ @ (ap11_V _ _ _ _)).
        f_ap. apply allpath_hprop.

        intro eq.
        apply (ap ap10)^-1. apply path_forall. intro p.
        refine ((ap10_path_arrow _ _ _ _) @ _).



        admit.
        admit.
        
        
        

      (* XXX *)
        
        
        
        
        

        


  (* preserves products *)
  - intros A B. unfold O. simpl.
    apply equiv_inverse. apply equiv_prod_corect.
Admitted.
  

End OpenModality.

End Ex13.


(** %\exer{7.14}{251}% *)
(** %\exer{7.15}{251}% *)
