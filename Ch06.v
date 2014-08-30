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

Module Export Torus.

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

End Torus.
  



(** %\exer{6.2}{217}% 
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
\north$ and $g(\surf) = \merid(\lloop) \ct \merid(\base_{1})^{-1}$,
conjugated with proofs that $\merid(\base) \ct \merid(\lloop)^{-1} =
\refl{\north}$.
*)

Definition SS1_to_S2 := Susp_rect_nd base base (S1_rectnd (base = base) 1 surf).

Definition S2_to_SS1 := 
  S2_rectnd (Susp S1) North
            ((concat_pV (merid Circle.base))^
             @ ((ap merid loop) @@ inverse2 (ap merid loop))
             @ (concat_pV (merid Circle.base))).

Lemma apD02_const {A B : Type} {x y : A} {p q : x = y} 
      (f : A -> B) (r : p = q) :
  apD02 f r = 
  (apD_const f p 
    @ (transport2_const r (f x) @@ ap02 f r))
    @ ((concat_pp_p (transport2 (fun _ : A => B) r (f x)) 
                   (transport_const q (f x))
                   (ap f q))
    @ (whiskerL (transport2 (fun _ : A => B) r (f x)) (apD_const f q)^)).
Proof.
  by path_induction.
Defined.

Definition cancelL2 {A : Type} {x y z : A} {p p' : x = y} {q q' : y = z}
  (a : p = p') (b c : q = q') :
  (a @@ b) = (a @@ c) -> b = c.
Proof.
  intros.
  induction a.
  induction b.
  induction p.
  induction q.
  transitivity ((concat_1p 1)^ @ whiskerL 1 c @ concat_1p 1).
  hott_simpl.
  apply whiskerL_1p.
Defined.
  
Lemma concat_p1_1 {A : Type} {x y : A} (p : x = y) : 
  concat_pp_p p 1 1 = (concat_p1 (p @ 1)) @ (whiskerL p (concat_p1 1)).
Proof.
  by path_induction.
Defined.
  

Definition S2_rectnd_beta_loop (P : Type) (b : P) (s : idpath b = idpath b)
  : ap02 (S2_rectnd P b s) surf = s^.
  change (concat_p1 1) with (idpath (idpath b)).
  unfold S2_rectnd.
  set (f := (S2_rect (fun _ : S2 => P) b
                         (((concat_p1 (transport2 (fun _ : S2 => P) surf b))^ 
                           @ (transport2_const surf b)^) @ s))).
  change (S2_rect (fun _ : S2 => P) b
                         (((concat_p1 (transport2 (fun _ : S2 => P) surf b))^ 
                           @ (transport2_const surf b)^) @ s)) with f.
  refine (cancelL2 (transport2_const surf (f base)) _ _ _).
  refine (cancelL (apD_const f 1) _ _ _).
  refine (cancelR _ _ 
                  ((concat_pp_p (transport2 (fun _ : S2 => P) surf (f base))
          (transport_const 1 (f base)) (ap f 1)) @
       whiskerL (transport2 (fun _ : S2 => P) surf (f base)) (apD_const f 1)^)
                  _).
  transitivity (apD02 f surf).
  symmetry. 
  apply (apD02_const f surf).
  unfold transport_const, apD_const. hott_simpl.
  transitivity ((transport2_const surf (f base) @@ s^) @
   concat_pp_p (transport2 (fun _ : S2 => P) surf (f base)) 1 (ap f 1)).
  change (apD02 f surf) with (apD02 (S2_rect (fun _ : S2 => P) b
         (((concat_p1 (transport2 (fun _ : S2 => P) surf b))^ @
           (transport2_const surf b)^) @ s)) surf).
  refine ((S2_rect_beta_loop _ _ _) @ _).
  apply moveR_pV.
  transitivity (s^ @ ((concat_p1 (transport2 (fun _ : S2 => P) surf b))^ @
     (transport2_const surf b)^)^). hott_simpl.
  apply moveR_pV. hott_simpl.
  transitivity (((transport2_const surf (f base) @@ s^) @
    concat_pp_p (transport2 (fun _ : S2 => P) surf (f base)) 1 1) @
   (transport2_const surf b)^).
  apply moveL_pV. apply moveL_pM.
  transitivity (transport2_const surf b @@ s^).
  apply moveR_Mp.
  transitivity ((concat_pp_p (transport2 (fun _ : S2 => P) surf b) 1 1)^).
  hott_simpl.
  transitivity ((transport2_const surf b)^ 
                @ (s @ (transport2_const surf b @@ s^))).
  apply moveL_Vp.
  transitivity ((1 @@ s) @ (transport2_const surf b @@ s^)).
  transitivity (transport2_const surf b @@ (s @ s^)).
  transitivity (transport2_const surf b @@ (idpath (idpath b))).
  transitivity (whiskerR (transport2_const surf b) 1).
  transitivity ((concat_p1 (transport_const 1 b))
                @ (transport2_const surf b)
                @ (concat_p1 (transport2 _ surf b @ transport_const 1 b))^).
  apply concat2. hott_simpl.
  apply inverse2. unfold transport_const.
  refine ((concat_p1_1 _) @ _).
  refine (_ @ (concat_p1 _)).
  apply concat2. hott_simpl. hott_simpl.
  apply moveR_pV. apply moveR_Mp. 
  transitivity (((concat_p1 (transport_const 1 b))^ @
   whiskerR (transport2_const surf b) 1) @
    concat_p1 (transport2 (fun _ : S2 => P) surf b @ transport_const 1 b)).
  apply (whiskerR_p1 _)^.
  hott_simpl. hott_simpl. hott_simpl. hott_simpl.
  transitivity ((1 @ transport2_const surf b) @@ (s @ s^)).
  hott_simpl. symmetry. 
  apply (concat_concat2 1 (transport2_const surf b) s s^).
  refine (whiskerR _ (transport2_const surf b @@ s^)).
  etransitivity (whiskerL 1 s). apply (concat2_1p s).
  etransitivity ((concat_1p 1)^ @ whiskerL 1 s @ (concat_1p 1)).
  hott_simpl. apply whiskerL_1p.
  transitivity (((transport2_const surf b)^ @ s) @ (transport2_const surf b @@ s^)).
  hott_simpl.
  refine (whiskerR _ _).
  transitivity ((transport2_const surf b)^ @ s^^).
  hott_simpl. symmetry. apply inv_pp.
  reflexivity. hott_simpl.
  refine (_ @ (concat_p_pp _ _ _)).
  symmetry. hott_simpl.
Defined.
  
Lemma trans_paths2 : forall (A B : Type) (f g : A -> B) (x y : A) 
         (p q : x = y) (r : p = q) (s : f = g),
  transport2 (fun a : A => f a = g a) r (ap10 s x) 
  =
  trans_paths A B f g x y p (ap10 s x)
  @ (whiskerR (inverse2 (ap02 f r)) (ap10 s x) @@ ap02 g r)
  @ (trans_paths A B f g x y q (ap10 s x))^.
Proof.
  intros.
  induction s. induction r. induction p. hott_simpl.
Defined.
  
Theorem isequiv_SS1_to_S2 : IsEquiv (SS1_to_S2).
Proof.
  apply isequiv_adjointify with S2_to_SS1.
    refine (S2_rect _ 1 _).
    assert ((fun x => SS1_to_S2 (S2_to_SS1 x)) = idmap) as X.
    apply path_forall; intro x.
    unfold SS1_to_S2. 
Admitted.
    

    
    
    
  
  
  
  





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
