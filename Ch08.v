(* begin hide *)
Require Export HoTT Ch07.
(* end hide *)
(** printing <~> %\ensuremath{\eqvsym}% **)
(** printing == %\ensuremath{\sim}% **)
(** printing ^-1 %\ensuremath{^{-1}}% **)
(** %\part{Mathematics}% *)
(** * Homotopy theory *)

(** %\exer{8.1}{301}%
Prove that homotopy groups respect products: $\pi_{n}(A \times B) \eqvsym
\pi_{n}(A) \times \pi_{n}(B)$.
*)

(** %\soln%
*)

Definition homotopy_group (n : nat) (A : Type) `{H : IsPointed A}
  := match n with
       | O => Trunc 0 A
       | S n => Trunc 0 (iteratedLoopSpace (S n) A).1
     end.

Lemma equiv_functor_Trunc (n : trunc_index) (A B : Type) 
  : (A <~> B) -> (Trunc n A) <~> (Trunc n B).
Proof.
  intro e.
  refine (equiv_adjointify _ _ _ _).
  apply Trunc_rect_nondep. intro a. apply (tr (e a)).
  apply Trunc_rect_nondep. intro b. apply (tr (e^-1 b)).
  refine (Trunc_rect _ _).
  intro b. simpl. apply (ap tr). apply eisretr.
  refine (Trunc_rect _ _).
  intro a. simpl. apply (ap tr). apply eissect.
Defined.
  
Lemma equiv_functor_iLS (n : nat) (A B : Type) `{IsPointed A} `{IsPointed B}
  : A <~> B -> (iteratedLoopSpace n A).1 <~> (iteratedLoopSpace n B).1.
Proof.
  generalize dependent B. generalize dependent A.
  induction n.
  - intros A HA B HB. simpl. apply idmap.
  - intros A HA B HB. intros e.
    set (a := point A). set (b := point B).
    simpl. apply equiv_idmap.
Defined.


Lemma hg_prod `{Funext} (n : nat) (A B : Type) `{IsPointed A} `{IsPointed B}
  : homotopy_group n (A * B) <~> (homotopy_group n A) * (homotopy_group n B).
Proof.
  generalize dependent B. generalize dependent A. 
  induction n. 
  - intros A HA B HB. simpl.
    apply equiv_Trunc_prod_cmp. apply H. 
  - intros A HA B HB. set (a := point A). set (b := point B).
    simpl.
    equiv_via (Trunc 0 (iteratedLoopSpace n ((a = a) * (b = b))).1).
    apply equiv_functor_Trunc.
Admitted.
    
    
  

(** %\exer{8.2}{301}% *)
(** %\exer{8.3}{301}% *)
(** %\exer{8.4}{301}% *)
(** %\exer{8.5}{301}% *)
(** %\exer{8.6}{301}% *)
(** %\exer{8.7}{301}% *)
(** %\exer{8.8}{302}% *)
(** %\exer{8.9}{302}% *)
(** %\exer{8.10}{302}% *)
(** %\exer{8.11}{302}% *)
