(** * Homotopy type theory *)


(** %\exer{2.1}{103}%  
Show that the three obvious proofs of Lemma 2.1.2 are pairwise equal.
*)

(** %\soln%
Lemma 2.1.2 states that for every type $A$ and every $x, y, z : A$, there is a
function
%\[
  (x = y) \to (y = z) \to (x = z)
\]%
written $p \mapsto q \mapsto p \ct q$ such that $\refl{x} \ct \refl{x} =
\refl{x}$ for all $x : A$.  Each proof is an object $\ct_{i}$ of type
%\[
  \ct_{i} : \prd{x,y,z:A} (x=y)\to(y=z)\to(x=z)
\]%
So we need to show that $\ctu = \ctd = \ctt$.

The first proof is induction over $p$.  Consider the family
%\[
  C_{1}(x, y, p) \defeq 
  \prd{z:A} (y=x) (x=z)
\]%
we have
%\[
\lam{z}{q}q :
\left(\prd{z:A} (x=z) \to (x=z)\right)
  \equiv
  C_{1}(x, x, \refl{x})
\]%
So by path induction, there is a function
%\[
  p \ctu q : (x=z)
\]%
such that $\refl{x} \ctu q \equiv q$.

For the second, consider the family
%\[
  C_{2}(y, z, q) \defeq 
  \prd{z:A} (x=y) \to (x=z)
\]%
and element
%\[
  \lam{z}{p}p
  :
  \left(
    \prd{z:A} (x=z)\to (x=z)
  \right)
  \equiv
  C_{2}(z,z,\refl{z})
\]%
Induction gives us a function
%\[
  p \ctd q : (x = z)
\]%
such that
%\[
  p \ctd \refl{z} = \refl{z}
\]%

Finally, for $\ctt$, we have the construction from the text.  Take the type
families
%\[
  D(x,y,p) \defeq 
  \prd{z:A}(y=z) \to  (x=z)
\]%
and
%\[
  E(x, z, q) \defeq (x = z)
\]%
Since $E(x,x,\refl{x}) \equiv (x=x)$, we have $e(x) \defeq \refl{x} :
E(x,x,\refl{x})$, and induction gives us a function
%\[
  d : \left(\prd{x,z:A}\prd{q:x=z}(x=z)\right) 
  \equiv
  \prd{x:A}D(x, x, \refl{x})
\]%
So path induction again gives us a function
%\[
  f : \prd{x,y,z:A}(x=y) \to(y=z) \to (x=z)
\]%
Which we can write $p \ctt q : (x=z)$.  By the definitional equality of $f$, we
have that $\refl{x} \ct q \equiv d(x)$, and by the definitional equality of
$d$, we have $\refl{x} \ct \refl{x} \equiv \refl{x}$.

Now, to show that $p \ctu q = p \ctd q = p \ctt q$.




*)
