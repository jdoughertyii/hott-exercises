(* begin hide *)
Require Export HoTT Ch05 hit.TwoSphere.
(* end hide *)
(** printing <~> %\ensuremath{\eqvsym}% **)
(** printing == %\ensuremath{\sim}% **)
(** printing ^-1 %\ensuremath{^{-1}}% **)
(** * Higher Inductive Types *)

(** %\exerdone{6.1}{217}% 
Define concatenation of dependent paths, prove that application of dependent
functions preserves concatenation, and write out the precise induction
principle for the torus $T^{2}$ with its computation rules.
*)

(** %\soln%
I found
%\href{http://ncatlab.org/homotopytypetheory/files/torus.pdf}{Kristina
Sojakova's answer posted to the HoTT Google group}%
helpful here, though I think my answer differs.

Let $W : \UU$, $P : W \to \UU$, $x, y, z : W$, $u : P(x)$, $v : P(y)$, and $w :
P(z)$ with $p : x = y$ and $q : y = z$.
We define the map
%\[
  \ctD : (\dpath{P}{p}{u}{v}) \to (\dpath{P}{q}{v}{w}) \to (\dpath{P}{p \ct q}{u}{w})
\]%
by path induction.
*)

Definition concatD {A} {P : A -> Type} {x y z : A} 
           {u : P x} {v : P y} {w : P z}
           {p : x = y} {q : y = z} :
  (p # u = v) -> (q # v = w) -> ((p @ q) # u = w).
  by path_induction.
Defined.

Notation "p @D q" := (concatD p q)%path (at level 20) : path_scope.

(** %\noindent%
To prove that application of dependent functions preserves concatenation,
we must show that for any $f : \prd{x:A}P(x)$, $p : x = y$, and $q : y = z$,
%\[
  \mapdep{f}{p \ct q} = \mapdep{f}{p} \ctD \mapdep{f}{q}
\]%
which is immediate by path induction.
*)

Theorem apD_pp {A} {P : A -> Type} (f : forall x : A, P x) 
        {x y z : A} (p : x = y) (q : y = z) :
  apD f (p @ q) = (apD f p) @D (apD f q).
Proof.
  by path_induction.
Defined.

(** %\noindent%
Suppose that we have a family $P : T^{2} \to \UU$, a point $b' : P(b)$, paths
$p' : \dpath{P}{p}{b'}{b'}$ and $q' : \dpath{P}{q}{b'}{b'}$ and a 2-path $t' :
\dpath{P}{t}{p' \ctD q'}{q' \ctD p'}$.  Then the induction principle gives a
section $f : \prd{x : T^{2}} P(x)$ such that $f(b) \equiv b'$, $f(p) = p'$, and
$f(q) = q'$.  As discussed in the text, we should also have $\apdtwo{f}{t} =
t'$, but this is not well-typed.  This is because $\apdtwo{f}{t} :
\dpath{P}{t}{f(p \ct q)}{f(q \ct p)}$, in contrast to the type of $t'$, and the
two types are not judgementally equal.

To cast $\apdtwo{f}{t}$ as the right type, note first that, as just proven,
$f(p \ct q) = f(p) \ctD f(q)$, and $f(q \ct p) = f(q) \ctD f(p)$.  The
computation rules for the 1-paths can be lifted as follows.  
Let $r, r' : \dpath{P}{p}{u}{v}$, and $s, s' : \dpath{P}{q}{v}{w}$.  Then we
define a map
%\[
  \ctdD : (r = r') \to (s = s') \to (r \ctD s = r' \ctD s')
\]%
by path induction.
*)

Definition concat2D {A : Type} {P : A -> Type} 
           {x y z : A} {p : x = y} {q : y = z} 
           {u : P x} {v : P y} {w : P z}
           {r r' : p # u = v} {s s' : q # v = w} :
  (r = r') -> (s = s') -> (r @D s = r' @D s').
  by path_induction.
Defined.

Notation "p @@D q" := (concat2D p q)%path (at level 20) : path_scope.
       

(** %\noindent%
Thus by the computation rules for $p$ and $q$,
we have for $\alpha : f(p) = p'$ and $\beta : f(q) = q'$,
%\begin{align*}
  \alpha \ctdD \beta &: f(p) \ctD f(q) = p' \ctD q' \\
  \beta \ctdD \alpha &: f(q) \ctD f(p) = q' \ctD p'
\end{align*}%
At this point it's pretty clear how to assemble the computation rule.
Let $N_{1} : f(p \ct q) = f(p) \ctD f(q)$ and $N_{2} : f(q \ct p) = f(q) \ctD
f(p)$ be two instances of the naturality proof just given.  Then we have
%\[
  (\alpha \ctdD \beta)^{-1} \ct N^{-1}_{1} 
  \ct \apdtwo{f}{t}
  \ct (\transtwo{t}{b'} \leftwhisker N_{2})
  \ct (\transtwo{t}{b'} \leftwhisker (\beta \ctdD \alpha))
  :
  \dpath{P}{t}{p' \ctD q'}{q' \ctD p'}
\]%
which is the type of $t'$.
*)

Module Torus_ex.

Private Inductive T2 : Type :=
| Tb : T2.

Axiom Tp : Tb = Tb.
Axiom Tq : Tb = Tb.
Axiom Tt : Tp @ Tq = Tq @ Tp.

Definition T2_rect (P : T2 -> Type) 
           (b' : P Tb) (p' : Tp # b' = b') (q' : Tq # b' = b')
           (t' : p' @D q' = (transport2 P Tt b') @ (q' @D p'))
  : forall (x : T2), P x :=
  fun x => match x with Tb => fun _ _ _ => b' end p' q' t'.

Axiom T2_rect_beta_Tp :
  forall (P : T2 -> Type)
         (b' : P Tb) (p' : Tp # b' = b') (q' : Tq # b' = b')
         (t' : p' @D q' = (transport2 P Tt b') @ (q' @D p')),
    apD (T2_rect P b' p' q' t') Tp = p'.

Axiom T2_rect_beta_Tq :
  forall (P : T2 -> Type)
         (b' : P Tb) (p' : Tp # b' = b') (q' : Tq # b' = b')
         (t' : p' @D q' = (transport2 P Tt b') @ (q' @D p')),
    apD (T2_rect P b' p' q' t') Tq = q'.

Axiom T2_rect_beta_Tt :
  forall (P : T2 -> Type)
         (b' : P Tb) (p' : Tp # b' = b') (q' : Tq # b' = b')
         (t' : p' @D q' = (transport2 P Tt b') @ (q' @D p')),
    (T2_rect_beta_Tp P b' p' q' t' @@D T2_rect_beta_Tq P b' p' q' t')^
    @ (apD_pp (T2_rect P b' p' q' t') Tp Tq)^ 
    @ (apD02 (T2_rect P b' p' q' t') Tt)
    @ (whiskerL (transport2 P Tt (T2_rect P b' p' q' t' Tb))
                (apD_pp (T2_rect P b' p' q' t') Tq Tp))
    @ (whiskerL (transport2 P Tt (T2_rect P b' p' q' t' Tb))
                (T2_rect_beta_Tq P b' p' q' t' @@D T2_rect_beta_Tp P b' p' q' t'))
    = t'.

End Torus_ex.
  



(** %\exerdone{6.2}{217}% 
Prove that $\susp\Sn^{1} \eqvsym \Sn^{2}$, using the explicit definition of
$\Sn^{2}$ in terms of $\base$ and $\surf$ given in %\S6.4%.
*)

(** %\soln%
$\Sn^{2}$ is generated by
 - $\base_{2} : \Sn^{2}$
 - $\surf : \refl{\base_{2}} = \refl{\base_{2}}$
and $\susp\Sn^{1}$ is generated by
 - $\north : \susp\Sn^{1}$
 - $\south : \susp\Sn^{1}$
 - $\merid : \Sn^{1} \to (\north = \south)$.
To define a map $f : \susp\Sn^{1} \to \Sn^{2}$, we need a map $m : \Sn^{1} \to
(\base_{2} = \base_{2})$, which we define by circle recursion such that
$m(\base_{1}) \equiv \refl{\base_{2}}$ and $m(\lloop) = \surf$.  Then recursion
on $\susp\Sn^{1}$ gives us our $f$, and we have $f(\north) \equiv \base_{2}$;
$f(\south) \equiv \base_{2}$; and for all $x : \Sn^{1}$, $f(\merid(x)) = m(x)$.

To go the other way, we use the recursion principle for the 2-sphere to obtain
a function $g : \Sn^{2} \to \susp\Sn^{1}$ such that $g(\base_{2}) \equiv
\north$ and $\aptwo{g}{\surf} = \merid(\lloop) \rightwhisker \merid(\base_{1})^{-1}$,
conjugated with proofs that $\merid(\base_{1}) \ct \merid(\base_{1})^{-1} =
\refl{\north}$.

Now, to show that this is an equivalence, we must show that the second map is a
quasi-inverse to the first.  First we show $g \circ f \sim
\idfunc{\susp\Sn^{1}}$.  For the poles we have
%\begin{align*}
  g(f(\north)) &\equiv g(\base_{2}) \equiv \north \\
  g(f(\south)) &\equiv g(\base_{2}) \equiv \north
\end{align*}%
and concatenating the latter with $\merid(\base_{1})$ gives $g(f(\south)) =
\south$.  Now we must show that for all $y : \Sn^{1}$, these equalities hold as
$x$ varies along $\merid(y)$.  That is, we must produce a path
%\[
  \transfib{x \mapsto g(f(x)) = x}{\merid(y)}{\refl{\north}} = \merid(\base_{1})
\]%
or, by Theorem 2.11.3 and a bit of path algebra,
%\[
  g(m(y))
  =
  \merid(y) \ct \merid(\base_{1})^{-1}
\]%
We do this by induction on $\Sn^{1}$.  When $y \equiv \base_{1}$, we have
%\[
  g(m(\base_{1})) 
  = 
  g(\refl{\base_{2}}) 
  =
  \refl{\base_{2}}
  =
  \merid(\base_{1}) \ct \merid(\base_{1})^{-1}
\]%
When $y$ varies along $\lloop$, we have to show that this proof continues to
hold.  By Theorem 2.11.3 and some path algebra, this in fact
reduces to
%\[
  \mapfunc{y \mapsto g(m(y))} \lloop
  =
  \merid(\lloop) \rightwhisker \merid(\base_{1})^{-1}
\]%
modulo the proofs of $\merid(\base_{1}) \ct \merid(\base_{1})^{-1} =
\refl{\north}$.  And this is essentially the computation rule for $g$.  Since
the computation rules are propositional some extra proofs have to be carried
around, though; see the second part of [isequiv_SS1_to_S2] for the gory details.

To show that $f \circ g \sim \idfunc{\Sn^{2}}$, note that
%\[
  f(g(\base_{2})) \equiv f(\north) \equiv \base_{2}
\]%
so we only need to show that as $x$ varies over the surface,
%\[
  \dpath{x \mapsto f(g(x)) =
  x}{\surf}{\refl{\refl{\base_{2}}}}{\refl{\refl{\base_{2}}}}
\]%
which means
%\[
 \refl{\refl{\base_{2}}} = \transtwo{\surf}{\refl{\base_{2}}}
  \equiv
  \mapfunc{p \mapsto p_{*} \refl{\base_{2}}}\surf
\]%
So we need to show that
%\[
  \refl{\refl{\base_{2}}} = \mapfunc{p \mapsto f(g(p^{-1})) \ct p} \surf
\]%
which by naturality of $\mapfunc{}$ and the computation rule for $\Sn^{1}$ is
%\[
  \refl{\refl{\base_{2}}} 
  =
  \left(\aptwo{f}{\aptwo{g}{\surf}}\right)^{-1}
  \ct
  \surf
\]%
Naturality and the computation rules then give
%\[
  \aptwo{f}{\aptwo{g}{\surf}} 
  = \aptwo{f}{\merid(\lloop)} 
  = m(\lloop)
  = \surf
\]%
and we're done.  The computation in Coq is long, since all of the homotopic
corrections have to be done by hand.  I also spend a lot of moves on making the
interactive version of the proof clear, and those could probably be eliminated.
*)



Lemma ap_ap__ap02_ap {A B C : Type} {a : A} {b : B} 
      (p : a = a) (f : B -> C) (m : A -> (b = b)) :
  ap (fun x : A => ap f (m x)) p = ap02 f (ap m p).
Proof. by path_induction. Defined.

Lemma whiskerR_ap {A B : Type} {a : A} {b b' : B} 
      (f : A -> (b = b')) (p : a = a) (q : b' = b) :
  whiskerR (ap f p) q = ap (fun x => f x @ q) p.
Proof. by path_induction. Defined.

Definition SS1_to_S2 := Susp_rect_nd base base (S1_rectnd (base = base) 1 surf).

Definition S2_to_SS1 := 
  S2_rectnd (Susp S1) North
            ((concat_pV (merid Circle.base))^
             @ (whiskerR (ap merid loop) (merid Circle.base)^)
             @ (concat_pV (merid Circle.base)))^.

Lemma ap_concat (A B : Type) (a : A) (b b' b'' : B) (p : a = a) 
      (f : A -> (b = b')) (g : A -> (b' = b'')) :
  ap (fun x => f x @ g x) p = (ap f p) @@ (ap g p).
Proof. by path_induction. Defined.

Definition concat2_V2p {A : Type} {x y : A} {p q : x = y} (r : p = q) :
  (concat_Vp _)^ @ (inverse2 r @@ r) @ (concat_Vp _) = 1.
Proof. by path_induction. Defined.

Definition ap_inv {A B : Type} {a : A} {b : B} (p : a = a) (m : A -> (b = b)):
  ap (fun x : A => (m x)^) p = inverse2 (ap m p).
Proof. by path_induction. Defined.

Lemma bar (A B C : Type) (b b' : B) (m : A -> (b = b')) (f : B -> C) 
      (a : A) (p : a = a) :
  ap (fun x : A => ap f (m x)) p = ap02 f (ap m p).
Proof.
  by path_induction.
Defined.

Definition ap03 {A B : Type} (f : A -> B) {x y : A} 
           {p q : x = y} {r s : p = q} (t : r = s) :
  ap02 f r = ap02 f s
  := match t with idpath => 1 end.

Definition ap_pp_pV {A B : Type} (f : A -> B) 
           {x y : A} (p : x = y) :
  ap_pp f p p^ 
  = (ap02 f (concat_pV p)^)^ @ (concat_pV (ap f p))^ @ (1 @@ (ap_V f p))^.
Proof.
  by path_induction.
Defined.

Definition ap02_V {A B : Type} (f : A -> B)
           {x y : A} {p q : x = y} (r : p = q) :
  ap02 f r^ = (ap02 f r)^.
Proof. by path_induction. Defined.

Definition inv_p2p {A : Type} {x y z : A} 
           {p p' : x = y} {q q' : y = z} (r : p = p') (s : q = q') :
  (r @@ s)^ = r^ @@ s^.
Proof. by path_induction. Defined.

Definition baz {A : Type} {x y : A} {p q : x = y} (r : p = q) : 
  concat_pV p = (r @@ inverse2 r) @ concat_pV q.
Proof. by path_induction. Defined.

Theorem isequiv_SS1_to_S2 : IsEquiv (SS1_to_S2).
Proof.
  apply isequiv_adjointify with S2_to_SS1.
  
  (* SS1_to_S2 o S2_to_SS1 == id *)
  refine (S2_rect (fun x => SS1_to_S2 (S2_to_SS1 x) = x) 1 _).
  unfold transport2.
  transparent assert (H : (forall p : base = base,
      (fun p' : base = base => transport (fun x => SS1_to_S2 (S2_to_SS1 x) = x) p' 1) p
      =
      (fun p' : base = base => ap SS1_to_S2 (ap S2_to_SS1 p'^) @ p') p
  )).
  intros. refine ((transport_paths_FFlr _ _) @ _).
  apply whiskerR. refine ((concat_p1 _) @ _). 
  refine ((ap_V SS1_to_S2 (ap S2_to_SS1 p))^ @ _). f_ap.
  apply (ap_V _ _)^.
  transitivity ((H 1) 
                @ ap (fun p : base = base => ap SS1_to_S2 (ap S2_to_SS1 p^) @ p) surf
                @ (H 1)^).
  apply moveL_pV. 
  apply (@concat_Ap _ _ _ _ H _ _ _).
  hott_simpl. clear H.
  transitivity (ap (fun p : base = base => ap SS1_to_S2 (ap S2_to_SS1 p^) @ p) 
                   (ap (S1_rectnd (base = base) 1 surf) loop)).
  f_ap. apply (S1_rectnd_beta_loop _ _ _)^.
  refine ((ap_compose _ _ _)^ @ _). unfold compose.
  refine ((ap_concat S1 _ _ _ _ _ _ _ _) @ _).
  transitivity (ap (fun x : S1 => 
                      ap SS1_to_S2 (ap S2_to_SS1 (S1_rectnd (base = base) 1 surf x)^)) loop 
                   @@ surf).
  f_ap. apply S1_rectnd_beta_loop.
  refine (_ @ (concat2_V2p surf)). hott_simpl. f_ap.


  (* invert the equation *)
  transparent assert (H : (
    forall x : S1, 
      ap SS1_to_S2 (ap S2_to_SS1 (S1_rectnd (base = base) 1 surf x)^)
      =
      (ap SS1_to_S2 (ap S2_to_SS1 (S1_rectnd (base = base) 1 surf x)))^
  )).
  intro x.
  refine (_ @ (ap_V _ _)). f_ap.
  refine (_ @ (ap_V _ _)). reflexivity.
  transitivity (
      (H Circle.base)
      @ ap (fun x : S1 => (ap SS1_to_S2 (ap S2_to_SS1 (S1_rectnd (base = base) 1 surf x)))^) 
        loop
      @ (H Circle.base)^
  ).
  apply moveL_pV. apply (concat_Ap H loop).
  simpl. hott_simpl. clear H.
  refine ((ap_inv loop 
                  (fun x => ap SS1_to_S2 (ap S2_to_SS1 (S1_rectnd (base = base) 1 surf x)))
                  ) @ _). 
  f_ap.

  (* reduce to SS1_to_S2 (S2_to_SS1 surf) = surf *)
  refine ((bar _ _ _ _ _ _ _ _ loop) @ _).
  refine ((ap03 _ (bar _ _ _ _ _ _ _ _ loop)) @ _).
  refine ((ap03 _ (ap03 _ (S1_rectnd_beta_loop _ _ _))) @ _).

  (* compute the action of S2_to_SS1 *)
  refine ((ap03 _ (S2_rectnd_beta_surf _ _ _)) @ _).
  hott_simpl.
  refine ((ap02_pp _ _ _) @ _). apply moveR_pM.
  refine ((ap02_pp _ _ _) @ _). apply moveR_Mp.
  refine ((ap03 _ (whiskerR_ap _ _ _)) @ _).
  refine ((ap03 _ (ap_concat _ _ _ _ _ _ _ merid _)) @ _).
  hott_simpl.
  refine ((ap02_p2p _ _ _) @ _). hott_simpl. apply moveR_pV. apply moveR_pM.

  (* eliminate [ap_pp]s *)
  refine ((ap_pp_pV _ _) @ _). apply moveL_pV. apply moveL_Mp.
  refine (_ @ (ap_pp_pV _ _)^). repeat (apply moveR_pM).
  refine ((inv_pp _ _) @ _). apply moveR_Vp.
  refine ((inv_pp _ _) @ _). apply moveR_pV. hott_simpl.
  repeat (apply moveL_pM). apply moveR_pM. hott_simpl. 
  apply moveL_Mp. refine (_ @ (ap02_V _ _)).
  refine (_ @ (ap03 _ (inv_V _)^)). apply moveR_Vp. hott_simpl.
  apply moveR_pM. hott_simpl.
  repeat (refine ((concat_pp_p _ _ _) @ _)). apply moveR_Vp. apply moveR_Vp.
  apply moveR_Vp. refine ((concat_concat2 _ _ _ _) @ _).
  apply moveL_Mp. apply moveR_pM. refine ((inv_p2p _ _) @ _). apply moveL_pV.
  refine ((concat_concat2 _ _ _ _) @ _). hott_simpl.
  
  (* eliminate the [concat_pV]s *)
  transparent assert (r : (
    ap SS1_to_S2 (merid Circle.base) = 1
  )).
  change 1 with (S1_rectnd (base = base) 1 surf Circle.base). 
  apply (Susp_comp_nd_merid Circle.base).
  apply moveL_pV. apply moveL_pM.
  refine (_ @ (baz r)^). hott_simpl.
  apply moveR_pV. apply moveR_Mp.
  refine ((baz r) @ _). apply moveL_Vp. hott_simpl.
  refine ((concat_concat2 _ r 1 (inverse2 r)) @ _). simpl. hott_simpl.
  apply moveL_Mp. apply moveR_pM.
  refine ((inv_p2p r (inverse2 r)) @ _).
  apply moveL_pV.
  refine ((concat_concat2 r^ (ap02 SS1_to_S2 (ap merid loop) @ r) (inverse2 r)^ (inverse2 r)) @ _).
  hott_simpl.

  (* de-whisker *)
  refine ((concat2_p1 _) @ _).
  transitivity ((concat_p1 _) 
                @ ((r^ @ ap02 SS1_to_S2 (ap merid loop)) @ r) 
                @ (concat_p1 _)^).
  apply moveL_pV. apply moveL_Mp. 
  refine ((concat_p_pp _ _ _) @ _). 
  apply whiskerR_p1. simpl. hott_simpl.
  apply moveR_pM. apply moveR_Vp.
  unfold r. clear r.

  (* compute the action of SS1_to_S2 *)
  refine ((bar _ _ _ _ _ merid _ _ _)^ @ _).
  transparent assert (H : (
    forall x : S1, ap SS1_to_S2 (merid x) = S1_rectnd _ 1 surf x                        
  )).
  apply Susp_comp_nd_merid.
  change (Susp_comp_nd_merid Circle.base) with (H Circle.base).
  refine (_ @ (concat_pp_p _ _ _)). apply moveL_pV.
  refine ((concat_Ap H loop) @ _). f_ap.
  apply S1_rectnd_beta_loop.
  

  (* S2_to_SS2 o SS1_to_S2 == id *)
  unfold Sect.
  refine (Susp_rect (fun x => S2_to_SS1 (SS1_to_S2 x) = x) 1 (merid Circle.base) _).

  (* make the goal g(m(y)) = merid(y) @ merid(Circle.base)^ *)
  intro x.
    refine ((transport_paths_FFlr _ _) @ _). hott_simpl.
    transitivity (ap S2_to_SS1 (S1_rectnd (base = base) 1 surf x)^ @ merid x).
    repeat f_ap.
    transitivity (ap SS1_to_S2 (merid x))^. hott_simpl.
    apply inverse2.
    apply Susp_comp_nd_merid.
    apply moveR_pM.
    transitivity (ap S2_to_SS1 (S1_rectnd (base = base) 1 surf x))^. hott_simpl.
    symmetry. transitivity (merid x @ (merid Circle.base)^)^.
    symmetry. apply inv_pV. apply inverse2. symmetry.
  generalize dependent x.

  (* now compute *)
  refine (S1_rect _ _ _).
  refine (_ @ (concat_pV _)^). reflexivity.
  refine ((@transport_paths_FlFr S1 _ _ _ _ _ loop _) @ _).
  hott_simpl. 
  apply moveR_pM. apply moveR_pM. hott_simpl. refine (_ @ (inv_V _)). 
  apply inverse2.
  transitivity ((concat_pV (merid Circle.base))^
                @ (whiskerR (ap merid loop) (merid Circle.base)^)
                @ (concat_pV (merid Circle.base))).
  refine (_ @ (inv_V _)).
  refine (_ @ (S2_rectnd_beta_surf _ _ _)).
  refine ((ap_ap__ap02_ap _ _ _) @ _).
  f_ap. apply S1_rectnd_beta_loop.
  refine (_ @ (inv_pp _ _)^). refine ((concat_pp_p _ _ _) @ _). apply whiskerL.
  refine (_ @ (inv_pp _ _)^). hott_simpl. apply whiskerR.
  apply whiskerR_ap.
Defined.
    

(** %\exer{6.3}{217}% 
Prove that the torus $T^{2}$ as defined in %\S6.6% 
is equivalent to $\Sn^{1} \times \Sn^{1}$.
*) 

(** %\exer{6.4}{217}% 
Define dependent $n$-loops and the action of dependent functions on $n$-loops,
and write down the induction principle for the $n$-spheres as defined at the
end of %\S6.4%.
*)

(** %\exer{6.5}{217}%
Prove that $\susp\Sn^{n} \eqvsym \Sn^{n+1}$, using the definition of $\Sn^{n}$
in terms of $\Omega^{n}$ from %\S6.4%.
*)

(** %\exer{6.6}{217}% 
Prove that if the type $\Sn^{2}$ belongs to some universe $\UU$, then $\UU$ is
not a 2-type.
*)

(** %\exer{6.7}{217}% 
Prove that if $G$ is a monoid and $x : G$, then $\sm{y:G}((x \cdot y = e)
\times (y \cdot x = e))$ is a mere proposition.  Conclude, using the principle
of unique choice, that it would be equivalent to define a group to be a monoid
such that for every $x : G$, there merely exists a $y : G$ such that $x \cdot y
= e$ and $y \cdot x = e$.
*)

(** %\exer{6.8}{217}% 
Prove that if $A$ is a set, then $\lst{A}$ is a monoid.  Then complete the
proof of Lemma 6.11.5.
*)

(** %\exer{6.9}{217}% 
Assuming $\LEM{}$, construct a family $f : \prd{X : \UU} (X \to X)$ such that
$f_{\bool} : \bool \to \bool$ is the nonidentity automorphism.
*)

(** %\exer{6.10}{218}% 
Show that the map constructed in Lemma 6.3.2 is in fact a quasi-inverse to
$\happly$, so that the interval type implies the full function extensionality
axiom.
*)

(** %\exer{6.11}{218}% 
Prove the universal property of suspension:
%\[
  \left(\susp A \to B \right)
  \eqvsym
  \left(\sm{b_{n} : B}\sm{b_{s} : B} (A \to (b_{n} = b_{s}))\right)
\]%
*)

(** %\exer{6.12}{218}% 
Show that $\Z \eqvsym \N + \unit + \N$.  Show that if we were to define $\Z$ as
$\N + \unit + \N$, then we could obtain Lemma 6.10.12 with judgmental
computation rules.
*)
