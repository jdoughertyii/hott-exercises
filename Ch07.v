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
(** %\exer{7.4}{250}% *)
(** %\exer{7.5}{250}% *)
(** %\exer{7.6}{250}% *)
(** %\exer{7.7}{250}% *)
(** %\exer{7.8}{250}% *)
(** %\exer{7.9}{251}% *)
(** %\exer{7.10}{251}% *)
(** %\exer{7.11}{251}% *)

(** %\exerdone{7.12}{251}% 
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
*)

Definition eta_nn (A : Type) : A -> ~ ~ A := fun a f => f a.

Lemma hprop_arrow (A B : Type) : IsHProp B -> IsHProp (A -> B).
Proof.
  intro HB.
  apply hprop_allpath. intros f g. apply path_forall. intro a. apply HB.
Defined.

Lemma hprop_neg {A : Type} : IsHProp (~ A).
Proof.
  apply hprop_arrow. apply hprop_Empty.
Defined.
  

Definition ind_nn (A : Type) (B : ~ ~ A -> Type) : 
  (forall a : A, ~ ~ (B (eta_nn A a))) -> forall z : ~ ~ A, ~ ~ (B z). 
Proof.
  intros f z. intro g.
  apply z. intro a.
  apply ((transport (fun x => ~ ~ (B x)) 
                    (@allpath_hprop _ hprop_neg _ _)
                    (f a)) g).
Defined.

Definition ind_nn_compute (A : Type) (B : ~ ~ A -> Type)
   (f : forall a, ~ ~ (B (eta_nn A a))) (a : A) :
    ind_nn A B f (eta_nn A a) = f a.
Proof.
  apply allpath_hprop.
Defined.

Lemma isequiv_hprop (P Q : Type) (HP : IsHProp P) (HQ : IsHProp Q)
      (f : P -> Q) :
  (Q -> P) -> IsEquiv f.
Proof.
  intro g.
  refine (isequiv_adjointify f g _ _).
  intro q. apply allpath_hprop.
  intro p. apply allpath_hprop.
Defined.

Lemma hprop_hprop_path (A : Type) (HA : IsHProp A) (x y : A) : IsHProp (x = y).
Proof.
  apply hprop_allpath.
  apply set_path2.
Defined.

Definition nn_isequiv_eta_path (A : Type) (z z' : ~ ~ A) : 
  IsEquiv (eta_nn (z = z')).
Proof.
  apply isequiv_hprop.
  apply hprop_hprop_path. apply hprop_neg. apply hprop_neg.
  intro f. apply hprop_neg.
Defined.

Theorem ismodality_DN : IsModality (fun A : Type => ~ ~ A).
Proof.
  apply (@Build_IsModality (fun A : Type => ~~ A)
                           eta_nn
                           ind_nn
                           ind_nn_compute
                           nn_isequiv_eta_path).
Defined.


  

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
\]% *)

Definition mod_fun (mod : Type -> Type) `{IsModality mod}
           {A B : Type} (f : A -> B) 
  : mod A -> mod B.
Proof.
  apply modality_ind.
  intro a.
  apply modality_eta.
  apply (f a).
Defined.

Lemma mod_fun_eta (mod : Type -> Type) `{IsModality mod} {A B : Type} 
      {f : A -> B} :
  (@mod_fun mod _ A B f) o (@modality_eta mod _ A)
  =
  (@modality_eta mod _ B) o f.
Proof.
  apply path_forall; intro a.
  unfold compose, mod_fun.
  refine (@modality_ind_compute mod _ _ _ _ _).
Defined.

Class IsLEModality (mod : Type -> Type) := 
  BuildIsLEModality {
      lem_ismodality : IsModality mod ;
      lem_pullbacks : forall (A B C : Type) (f : A -> C) (g : B -> C) X,
        (X -> mod {a : A & {b : B & f a = g b}})
        <~>
        {a : X -> mod A & { b : X -> mod B &
           (mod_fun mod f) o a 
           = (mod_fun mod g) o b}} ;
      lem_products : forall (A B X: Type),
        (X -> mod (A * B)) <~> (X -> mod A) * (X -> mod B)               
    }.


(** (i) Let $\modal X \defeq (P \to X)$, with $\eta^{\modal}_{A} : A \to
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

Coq is having a real hard time with the proof of
[coslice_compose_aux] below.  The right way to do it is to use the functorality of $\modal$, but instead I just did a bunch of path algebra.  Maybe I'll go back and do it right one day.*)

Definition eta_coslice (P : Type) (HP : IsHProp P) 
  : forall A : Type, A -> (P -> A)
  := fun A a p => a.

Definition ind_coslice (P : Type) (HP : IsHProp P)
  : forall (A : Type) (B : (P -> A) -> Type),
      (forall a : A, P -> (B (eta_coslice P HP A a))) 
      -> forall z : P -> A, P -> (B z).
Proof.
  intros A B f g p.
  apply (transport _ (path_forall (fun _ : P => g p) g
          (fun p' : P => ap g (allpath_hprop p p')))). 
  apply f. apply p.
Defined.

Lemma ind_coslice_compute (P : Type) (HP : IsHProp P) 
  : forall A B (f : forall a : A, P -> (B (eta_coslice P HP A a))) a,
      ind_coslice P HP A B f (eta_coslice P HP A a) = f a.
Proof.
  intros A B f a.
  apply path_forall; intro p.
  unfold ind_coslice. 
  unfold eta_coslice.
  etransitivity (transport B
     (path_forall (fun _ : P => a) (fun _ : P => a)
        (fun p' : P => 1)) 
     (f a p)).
  f_ap. f_ap. apply path_forall; intro p'.
  apply ap_const.
  etransitivity (transport B 1 (f a p)).
  f_ap. apply path_forall_1.
  reflexivity.
Defined.

Lemma isequiv_eta_coslice_path (P : Type) (HP : IsHProp P)
  : forall A (f g : P -> A),
      IsEquiv (eta_coslice P HP (f = g)).
Proof.
  intros.
  refine (isequiv_adjointify _ _ _ _).

  (* inverse *)
  intro H. 
  apply path_forall; intro p. 
  apply (apD10 (H p)).

  (* retract *)
  intro H.
  apply path_forall; intro p.
  unfold eta_coslice.
  transitivity (path_forall f g ((path_forall f g)^-1 (H p))).
  apply (ap (path_forall f g)).
  simpl. apply path_forall; intro p'.
  f_ap. f_ap. apply allpath_hprop.
  apply eisretr.

  (* section *)
  intro q.
  change (fun p : P => apD10 (eta_coslice P HP (f = g) q p) p)
         with (apD10 q).
  apply eta_path_forall.
Defined.


Definition ismodality_hprop_coslice (P : Type) (HP : IsHProp P) 
  : IsModality (fun A : Type => P -> A)
  := @Build_IsModality (fun A => P -> A)
                           (eta_coslice P HP)
                           (ind_coslice P HP)
                           (ind_coslice_compute P HP)
                           (isequiv_eta_coslice_path P HP).

Lemma isequiv_contr_coslice_fun {A B P : Type} `{Contr P} : 
  IsEquiv (@mod_fun (fun A => P -> A) 
                    (ismodality_hprop_coslice P _)
                    A B).
Proof.
  refine (isequiv_adjointify _ _ _ _).

  (* inverse *)
  intros f a.
  apply f. intro p. apply a. apply Contr0.
  
  (* section *)
  intro f.
  unfold mod_fun.
  apply path_forall; intro h.
  apply path_forall; intro p.
  unfold modality_ind. simpl.
  unfold eta_coslice, ind_coslice.
  refine ((path_forall_1_beta p (fun _ => B) _ _) @ _).
  refine ((transport_const _ _) @ _).
  f_ap. apply path_forall; intro p'. apply (ap h). 
  apply allpath_hprop. apply allpath_hprop. 

  (* retraction *)
  intro f.
  apply path_forall; intro a.
  unfold mod_fun.
  unfold modality_ind, modality_eta. simpl.
  unfold ind_coslice, eta_coslice.
  etransitivity (transport (fun _ : P -> A => B) 1 (f a)).
  f_ap. refine (_ @ (path_forall_1 (fun _ => a))).
  f_ap. apply path_forall; intro p. apply ap_const.
  reflexivity.
Defined.

Lemma ap11_V {A B : Type} {f g : A -> B} (h : f = g) {x y : A} (p : x = y) :
  ap11 h^ p^ = (ap11 h p)^.
Proof.
  induction h. induction p. reflexivity.
Defined.

Lemma coslice_compose_aux (A B C P X : Type) (HP : IsHProp P) 
      (f : A -> C) (g : B -> C) : 
{h : X * P -> A & {k : X * P -> B & f o h = g o k}} <~>
   {a : X -> P -> A &
   {b : X -> P -> B &
   @mod_fun (fun A0 : Type => P -> A0) (ismodality_hprop_coslice P HP) _ _ f o a
   =
   @mod_fun (fun A0 : Type => P -> A0) (ismodality_hprop_coslice P HP) _ _ g o b
   }}.
Proof.
  refine (equiv_functor_sigma' _ _).
  apply equiv_inverse. apply equiv_uncurry. intro h.
  refine (equiv_functor_sigma' _ _).
  apply equiv_inverse. apply equiv_uncurry. intro k.


  refine (equiv_adjointify _ _ _ _).

  (* forward *)
  intro r.
  unfold mod_fun, modality_ind, modality_eta. simpl.
  apply path_forall; intro x.
  apply path_forall; intro p.
  unfold compose.
  unfold ind_coslice, eta_coslice. simpl.
  refine ((path_forall_1_beta p (fun _ => C) _ _) @ _).
  refine ((apD10
           (ap11 1
              (ap _
                 (allpath_hprop (allpath_hprop p p) 1) @
               ap_1 _ _)) _) @ _).

  refine (_ @ (path_forall_1_beta p (fun _ => C) _ _)^).
  refine (_ @ (apD10
           (ap11 1
              ((ap_1 p _)^ @
               ap (ap _)
                 (allpath_hprop 1 (allpath_hprop p p)))) 
           (g (k (x, p))))).
  apply (apD10 r (x, p)).

  (* back *)
  intro r.
  apply path_forall. intro z.
  refine ((ap (f o h) (eta_prod z)^) @ _).
  unfold compose.
  change (f (h (fst z, snd z))) 
    with (transport (fun _ : A => C) 
                    (@idpath _ (h (fst z, snd z))) 
                    (f (h (fst z, snd z)))).
  refine ((apD10
           (ap11 1
              ((ap_1 _ (fun y : P => h (fst z, y)))^ @
               ap (ap _)
                 (allpath_hprop 1 (allpath_hprop (snd z) (snd z)))))
           _) @ _).
  refine ((path_forall_1_beta _ _
            (fun p' : P =>
             ap (fun y : P => h (fst z, y)) (allpath_hprop (snd z) p'))
            _)^ @ _).
  refine ((apD10 (apD10 r _) _) @ _). clear r.
  refine ((path_forall_1_beta (snd z) (fun _ => C) _ _) @ _).
  refine ((apD10
           (ap11 1
              (ap11 1 (allpath_hprop (allpath_hprop (snd z) (snd z)) 1) @
               ap_1 _ _))
           _) @ _).
  simpl.
  refine ((ap (g o k) (eta_prod z)) @ _).
  reflexivity.

  (* section *)
  intro r.
  etransitivity (path_forall _ _ (apD10 r)).
  f_ap. apply path_forall. intro x.
  etransitivity (path_forall _ _ (apD10 (apD10 r x))).
  f_ap. apply path_forall. intro p.
  apply moveR_Mp. 
  refine ((concat_p_pp _ _ _) @ _).
  apply moveR_pV. apply moveR_Mp. apply moveR_pM.
  refine ((apD10_path_forall _ _ _ (x, p)) @ _).
  apply moveR_pM.
  change (eta_prod (x, p)) with (@idpath _ (x, p)).
  refine ((ap_V _ _) @ _).
  refine ((ap inverse (ap_1 _ _)) @ _).
  apply moveL_pV. refine ((concat_1p _) @ _).
  refine (_ @ (concat_p_pp _ _ _ )).
  apply concat2.
  refine (_ @ (apD10_V _ (f (h (x, p))))).
  change (fst (x, p)) with x. change (snd (x, p)) with p.
  f_ap. refine (_ @ (ap11_V _ _)).
  hott_simpl.
  f_ap. refine (_ @ (ap_V _ _)).
  f_ap. apply allpath_hprop.
  hott_simpl.
  apply concat2.
  change (fst (x, p)) with x. change (snd (x, p)) with p.
  apply whiskerL.
  unfold equiv_uncurry, equiv_inverse, modality_eta. simpl.
  unfold eta_coslice. reflexivity.
  
  refine (_ @ (apD10_V _ _)).
  f_ap. refine (_ @ (ap11_V _ _)).
  f_ap. change (snd (x, p)) with p.
  refine (_ @ (ap_V (ap (fun y : P => k (x, y))) 
                    (allpath_hprop 1 (allpath_hprop p p)))).
  f_ap. apply allpath_hprop.
  
  apply eta_path_forall.
  apply eta_path_forall.
  

  (* retract *)
  intro r.
  etransitivity (path_forall _ _ (apD10 r)).
  f_ap. apply path_forall. intro z.
  destruct z as [x p].
  change (fst (x, p)) with x. change (snd (x, p)) with p.
  hott_simpl.


  unfold compose.
  repeat (refine ((concat_pp_p _ _ _) @ _)).
  apply moveR_Mp. apply moveR_Vp. apply moveR_pM.
  transitivity (apD10
            (path_forall
              (ind_coslice P HP A (fun _ : P -> A => C)
                 (fun a : A => eta_coslice P HP C (f a))
                 (fun y : P => h (x, y)))
              (ind_coslice P HP B (fun _ : P -> B => C)
                 (fun a : B => eta_coslice P HP C (g a))
                 (fun y : P => k (x, y)))
              (fun p0 : P =>
               path_forall_1_beta p0 (fun _ : A => C)
                 (fun p' : P =>
                  ap (fun y : P => h (x, y)) (allpath_hprop p0 p'))
                 (f (h (x, p0))) @
               (apD10
                  (ap11 1
                     (ap (ap (fun y : P => h (x, y)))
                        (allpath_hprop (allpath_hprop p0 p0) 1) @
                      ap_1 p0 (fun y : P => h (x, y)))) 
                  (f (h (x, p0))) @
                ((apD10 r (x, p0) @
                  apD10
                    (ap11 1
                       ((ap_1 p0 (fun y : P => k (x, y)))^ @
                        ap (ap (fun y : P => k (x, y)))
                          (allpath_hprop 1 (allpath_hprop p0 p0))))
                    (g (k (x, p0)))) @
                 (path_forall_1_beta p0 (fun _ : B => C)
                    (fun p' : P =>
                     ap (fun y : P => k (x, y)) (allpath_hprop p0 p'))
                    (g (k (x, p0))))^))))  p).
  f_ap. refine ((apD10_path_forall 
                   (fun x0 : X =>
         ind_coslice P HP A (fun _ : P -> A => C)
           (fun a : A => eta_coslice P HP C (f a)) 
           (fun y : P => h (x0, y)))
                   _ _ _) @ _).
  f_ap. refine ((apD10_path_forall _ _ _ _) @ _).
  refine (_ @ (concat_p_pp _ _ _)).
  apply whiskerL.
  repeat (apply moveL_Mp).
  refine (_ @ (inv_pp _ _)^).
  hott_simpl.
  apply concat2.
  
  repeat (refine ((concat_pp_p _ _ _) @ _)).
  apply moveR_Vp.
  hott_simpl. apply concat2.
  apply concat2.

  refine (_ @ (apD10_V _ _)). 
  f_ap. refine (_ @ (ap11_V _ _)).
  f_ap. refine (_ @ (ap_V _ (allpath_hprop 1 (allpath_hprop p p)))).
  f_ap. apply allpath_hprop.

  reflexivity.

  simpl modality_eta. unfold eta_coslice.
  refine (_ @ (apD10_V _ (g ((equiv_inverse (equiv_uncurry X P B)) k x p)))).
  simpl (g ((equiv_inverse (equiv_uncurry X P B)) k x p)).
  repeat (f_ap; refine (_ @ (ap11_V _ _))).
  f_ap. apply allpath_hprop.

  reflexivity.
  
  apply eta_path_forall.
Defined.
  
  
Theorem islemodality_hprop_coslice `{Funext} 
        (P : Type) (HP : IsHProp P)
  : IsLEModality (fun A : Type => P -> A).
Proof.
  refine (BuildIsLEModality _ _ _ _). 
  apply (ismodality_hprop_coslice P HP).

  (* preserves pullbacks *)
  intros.
  equiv_via ((X * P) -> {a : A & {b : B & f a = g b}}).
  apply equiv_uncurry.
  transparent assert (Hm : (IsModality (fun A => P -> A))).
    apply ismodality_hprop_coslice. apply HP.
  equiv_via {h : (X * P) -> A &
   {k : (X * P) -> B &
   f o h = g o k}}.
  apply ex2_11. 
  apply H.
  apply coslice_compose_aux.

  (* preserves products *)
  intros.
  equiv_via ((X * P) -> A * B). apply equiv_uncurry.
  equiv_via (((X * P) -> A) * ((X * P) -> B)). 
  apply equiv_inverse. apply equiv_prod_corect.
  apply equiv_inverse. 
  apply equiv_functor_prod'; apply equiv_uncurry.
Defined.

(** (ii)
Suppose now that $\modal X \defeq P * X$.  That is, suppose that $\modal X$ is
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

(* The main HoTT branch just added this definition today, but I
   couldn't get it to compile on the first try so I'll just recap it.
   I should come back and replace this with the real thing. *)

Module JoinModality.
  
Definition join (A B : Type) := pushout (@fst A B) (@snd A B).

Definition join_mod {P : Type} : Type -> Type := fun A => join P A.

Definition eta_hprop_join {P : Type} (A : Type) : A -> join_mod A 
  := fun a => push (@inr P A a).

Lemma contr_join (A B : Type) `{Contr A} : Contr (join A B).
Proof.
  exists (push (inl (center A))).
  intros y. refine (pushout_rect _ _ _ _ _ y).
  - intros [a | b].
    * apply ap, ap, contr.
    * exact (pp (center A, b)).
  - intros [a b]. cbn.
    refine (_ @ apD (fun a' => pp (a', b)) (contr a)^).
    refine ((transport_paths_r _ _) @ _).
    refine (_ @ (transport_paths_FlFr (contr a)^ _)^).
    apply moveL_pM. apply moveL_pM.
    refine (_ @ (ap_V _ (contr a)^)).
    refine (_ @ ap (ap (fun x => pushl (x, b))) (inv_V _)^).
    apply moveR_pV. apply moveR_Mp.
    refine ((ap_V _ (contr a)^)^ @ _).
    refine ((ap (ap (fun x => pushr (x, b))) (inv_V (contr a))) @ _).
    apply moveL_Vp. refine ((concat_pp_p _ _ _) @ _).
    apply moveR_pM. refine ((ap_compose _ _ _)^ @ _).
    unfold compose, pushl, pushr. simpl.
    apply moveL_pV. apply concat2. reflexivity.
    refine (_ @ (concat_p1 _)). apply concat2. reflexivity.
    apply ap_const.
Defined.

Definition ind_hprop_join (P : Type) `{IsHProp P} 
           (A : Type) (B : (join_mod A) -> Type)
  :  (forall a : A, @join_mod P (B (eta_hprop_join A a)))
       -> forall z : (@join_mod P A), (@join_mod P (B z)).
Proof.
  intro f.
  refine (pushout_rect _ _ _ _ _).
  intro z. destruct z. 
  apply push. left. apply p.
  unfold eta_hprop_join in f. 
  apply f.

  intro z. destruct z as (p, a).
  simpl.
  transparent assert (H : (IsHProp (@join_mod P (B (pushr (p, a)))))).
  apply hprop_inhabited_contr. intro b. apply contr_join.
  apply contr_inhabited_hprop. apply IsHProp0. apply p.
  apply allpath_hprop.
Defined.


Lemma ind_hprop_join_compute (P : Type) `{IsHProp P} 
  : forall A B (f : forall a : A, join_mod (B (eta_hprop_join A a))) a,
      ind_hprop_join P A B f (eta_hprop_join A a) = f a.
Proof.
  intros.
  reflexivity.
Defined.

Lemma isequiv_eta_hprop_join_path (P : Type) (HP : IsHProp P)
  : forall A (z z' : @join_mod P A), IsEquiv (@eta_hprop_join P (z = z')).
Proof.
  intros.
  refine (isequiv_adjointify _ _ _ _).

  (* inverse *)
  refine (pushout_rect _ _ _ _ _).
  intro p. destruct p.
  refine (path_contr _ _).
  apply contr_join. apply contr_inhabited_hprop. apply HP. apply p. 
  apply p.
  intros w. destruct w as [p q]. simpl.
  refine (path_contr _ _).
  refine (contr_paths_contr _ _).
  apply contr_join. apply contr_inhabited_hprop. apply HP. apply p.

  unfold Sect. refine (pushout_rect _ _ _ _ _).
  intro p. destruct p. simpl.
  unfold eta_hprop_join.
  refine ((pp ((p, path_contr z z')))^ @ _).
  unfold pushl. f_ap.

  unfold eta_hprop_join. reflexivity.
  
  intros w. destruct w as [p q].
  refine (path_contr _ _).
  refine (contr_paths_contr _ _).
  apply contr_join. apply contr_inhabited_hprop. apply HP. apply p.

  intros p. reflexivity.
Defined.

Definition ismodality_hprop_join (P : Type) `{IsHProp P}
  : IsModality (@join_mod P)
  := @Build_IsModality (@join_mod P)
                       (@eta_hprop_join P)
                       (@ind_hprop_join P _)
                       (@ind_hprop_join_compute P _)
                       (@isequiv_eta_hprop_join_path P _).


Theorem islemodality_hprop_join (P : Type) `{IsHProp P} :
  IsLEModality (@join_mod P).
Proof.
  refine (@BuildIsLEModality _ _ _ _).
  apply ismodality_hprop_join. apply IsHProp0.
  
  (* preserves pullbacks *)
  intros.
  admit.
  
  (* preserves products *)
  intros.
  refine (equiv_adjointify _ _ _ _).
  intros. split.
  Admitted.
  
  
  
  
  
  


End JoinModality. 


(** %\exer{7.14}{251}% *)
(** %\exer{7.15}{251}% *)
