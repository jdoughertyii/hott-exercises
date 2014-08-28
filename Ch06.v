(* begin hide *)
Require Export HoTT Ch05.
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
  (\alpha \ctdD \beta)^{-1} \ct N_{1} 
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
  : forall (x : T2), P x.
  intro x. destruct x. apply b'.
Defined.

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
