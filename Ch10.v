(* begin hide *)
Require Export HoTT Ch09.
(* end hide *)
(** printing <~> %\ensuremath{\eqvsym}% **)
(** printing <~=~> %\ensuremath{\cong}% **)
(** printing == %\ensuremath{\sim}% **)
(** printing ^-1 %\ensuremath{^{-1}}% **)
(** * Set theory *)

(** %\exer{10.1}{364}% *)

(** %\exer{10.2}{364}% 
Show that if every surjection has a section in the category $\uset$, then the
axiom of choice holds.
*)

(** %\exer{10.3}{364}% *)

(** %\exerdone{10.4}{365}% 
Prove that if $(A, <_{A})$ and $(B, <_{B})$ are well-founded, extensional,
or ordinals, then so is $A + B$, with $<$ defined by
%\begin{alignat*}{3}
  (a < a') &\defeq (a <_{A} a') &\qquad\qquad \text{for $a, a' : A$} \\
  (b < b') &\defeq (b <_{B} b') &\qquad\qquad \text{for $b, b' : B$} \\
  (a < b) &\defeq \unit &\qquad\qquad \text{for $a: A$, $b : B$} \\
  (b < a) &\defeq \emptyt &\qquad\qquad \text{for $a : A$, $b : B$}
\end{alignat*}%
*)

(** %\soln%
(i)
Suppose that $(A, <_{A})$ and $(B, <_{B})$ are well-founded.  To show that $(A
+ B, <)$ is well-founded, we need to show that $\acc(z)$ for all $z : A+B$.

Note first that for any $a : A$, $\acc(\inl(a))$, which we show by well-founded
induction on $A$.  For $a : A$ the inductive hypothesis says that for any $a'
<_{A} a$ we have $\acc(\inl(a'))$. So we must show that $\acc(\inl(a))$.  It
suffices to show that for all $z' < \inl(a)$, $\acc(z')$.  There are two cases:
if $z' \equiv \inl(a')$, then the induction hypothesis gives $\acc(z')$; if $z'
\equiv \inr(b')$, then $z' < \inl(a)$ is a contradiction.

Likewise, well-founded induction on $B$ shows that for all $b : B$,
$\acc(\inr(b))$.  The induction hypothesis says that for any $b' <_{B} b$ we
have $\acc(\inr(b'))$, and we must show $\acc(\inr(b))$.  It suffices to show
that for all $z' < \inr(b)$ we have $\acc(z')$.  Again, there are two cases.
If $z' \equiv \inl(a')$ then we have $\acc(z')$ by the argument of the previous
paragraph.  If $z' \equiv \inr(b')$, then we have $\acc(z')$ by the induction
hypothesis.

Now, to show that $(A + B, <)$ is a well-founded, suppose that $z : A + B$;
then $\acc(z)$.  For if $z \equiv \inl(a)$, then the first argument above gives
$\acc(z)$; if instead $z \equiv \inr(b)$, then the second argument gives
$\acc(z)$.

%\vspace{.1in}
\noindent%
(ii) Suppose that $(A, <_{A})$ and $(B, <_{B})$ are extensional, and $z, z' : A
+ B$.  To show that $(A + B, <)$ is extensional, suppose that $\fall{z'' : A +
B}(z'' < z) \Leftrightarrow (z'' < z')$.  We must show that $z = z'$.  There
are four cases.
 - $z \equiv \inl(a)$, $z' \equiv \inl(a')$.  Then $z = z'$ is equivalent to $a
   = a'$, and the hypothesis reduces to $\fall{a'' : A}(a'' <_{A} a)
   \Leftrightarrow (a'' <_{A} a')$.  By the extensionality of $<_{A}$ it
   follows that $a = a'$.
 - $z \equiv \inl(a)$, $z' \equiv \inr(b')$.  Then by the hypothesis we have
   $(a <_{A} a) \Leftrightarrow \unit$, which is equivalent to $(a <_{A} a)$.
   But $<_{A}$ is well-founded, hence irreflexive, so this is a contradiction.
 - $z \equiv \inr(b)$, $z' \equiv \inl(a')$.  This case goes as the previous
   one.
 - $z \equiv \inr(b)$, $z' \equiv \inr(b')$.  This case goes as the first.
So $<$ is extensional.

%\vspace{.1in}
\noindent%
(iii)
Suppose that $A$ and $B$ are ordinals.  We must show that $<$ is transitive, so
suppose that $z, z', z'' : A + B$.  There are 8 cases, in which $(z, z', z'')$
are
 - $(\inl(a), \inl(a'), \inl(a''))$.  Then the statement reduces to
   transitivity of $<_{A}$.
 - $(\inl(a), \inl(a'), \inr(b''))$.  Then the statement reduces to $a <_{A}
   a' \to a <_{A} a'$, which is trivial.
 - $(\inl(a), \inr(b'), \inl(a''))$.  Then the second hypothesis is a
    contradiction.
 - $(\inl(a), \inr(b'), \inr(b''))$.  Then the statement reduces to $b' <_{B}
   b'' \to b' <_{B} b''$, again trivial.
 - $(\inr(b), \inl(a'), \inl(a''))$.  Then the first hypothesis is a
     contradiction.
 - $(\inr(b), \inl(a'), \inr(b''))$.  Then the first hypothesis is a
     contradiction.
 - $(\inr(b), \inr(b'), \inl(a''))$.  Then the second hypothesis is a
     contradiction.
 - $(\inr(b), \inr(b'), \inr(b''))$.  Then the statement reduces to
     transitivity of $<_{B}$.
So $A + B$ is an ordinal.
*)  

Inductive acc {A : hSet} {L : A -> A -> hProp} : A -> Type :=
  | accL : forall a : A, (forall b : A, (L b a) -> acc b) -> acc a.

Lemma hprop_acc `{Funext} {A : hSet} {L : A -> A -> hProp} 
  : forall a, IsHProp (@acc _ L a).
Proof.
  intro a. apply hprop_allpath. intros s1 s2.
  induction s1 as [a1 h1 k1]. 
  induction s2 as [a2 h2 k2]. apply (ap (accL a2)).
  apply path_forall; intro b. apply path_forall; intro l.
  apply k1.
Defined.

Definition well_founded {A : hSet} (L : A -> A -> hProp) := 
  forall a : A, @acc A L a.

Lemma hprop_wf `{Funext} {A : hSet} (L : A -> A -> hProp) 
  : IsHProp (well_founded L).
Proof.
  apply hprop_dependent. apply hprop_acc.
Defined.

Lemma wf_irreflexive {A : hSet} (L : A -> A -> hProp) (HL : well_founded L)
  : forall a : A, ~ (L a a).
Proof.
  intro a. induction (HL a) as [a f g].
  intro H. contradiction (g a H).
Defined.


Definition set_sum (A B : hSet) := @BuildhSet (A + B) hset_sum.

(* This is misdefined in HoTT/HoTT *)
Definition False_hp : hProp := (BuildhProp Empty).

Definition sum_order {A B : hSet} (LA : A -> A -> hProp) 
           (LB : B -> B -> hProp) (z z' : set_sum A B)
  : hProp
  := match z with
       | inl a => match z' with
                    | inl a' => LA a a'
                    | inr b' => Unit_hp
                  end
       | inr b => match z' with
                    | inl a' => False_hp
                    | inr b' => LB b b'
                  end
     end.

Lemma sum_order_wf {A B : hSet} (LA : A -> A -> hProp) (LB : B -> B -> hProp)
  : (well_founded LA) -> (well_founded LB) -> well_founded (sum_order LA LB).
Proof.
  intros HLA HLB.
  transparent assert (HA : (
    forall a : A, @acc A LA a -> @acc _ (sum_order LA LB) (inl a)
  )).
  intros a s. induction s as [a f g]. constructor.
  intros z' L. destruct z' as [a' | b']; simpl in *.
  apply g. apply L.
  contradiction.

  transparent assert (HB : (
    forall b : B, @acc B LB b -> @acc _ (sum_order LA LB) (inr b)
  )).
  intros b s. induction s as [b f g]. constructor.
  intros z' L. destruct z' as [a' | b']; simpl in *.
  apply HA. apply HLA.
  apply g. apply L.

  intro z. destruct z as [a | b].
  apply HA. apply HLA.
  apply HB. apply HLB.
Defined.
  

Definition extensional {A : hSet} (L : A -> A -> hProp) {HL : well_founded L}
  := forall a a', (forall c, (L c a) <-> (L c a')) -> (a = a').

Lemma hprop_extensional `{Funext} (A : hSet) (L : A -> A -> hProp) 
      (HL : well_founded L)
  : IsHProp (@extensional A L HL).
Proof.
  apply hprop_dependent; intro a.
  apply hprop_dependent; intro b.
  apply hprop_dependent. intro f. apply hprop_allpath. apply set_path2.
Defined.

Lemma sum_order_ext {A B : hSet} (LA : A -> A -> hProp) (LB : B -> B -> hProp)
      (HwfA : well_founded LA) (HwfB : well_founded LB)
  : (@extensional A LA HwfA) 
    -> (@extensional B LB HwfB) 
    -> @extensional _ (sum_order LA LB) (sum_order_wf LA LB HwfA HwfB).
Proof.
  intros HeA HeB.
  intros z z' Heq. destruct z as [a | b], z' as [a' | b']; apply path_sum.
  apply HeA. intro a''. apply (Heq (inl a'')).
  apply (wf_irreflexive LA HwfA a), ((snd (Heq (inl a))) tt).
  apply (wf_irreflexive LA HwfA a'), ((fst (Heq (inl a'))) tt).
  apply HeB. intro b''. apply (Heq (inr b'')).
Defined.

Class Ord 
  := BuildOrd {
       o_set :> hSet ;
       o_rel :> o_set -> o_set -> hProp ;
       o_wf :> @well_founded o_set o_rel ;
       o_ext :> @extensional o_set o_rel o_wf ;
       o_trans : forall a b c : o_set, (o_rel a b) -> (o_rel b c) -> (o_rel a c)
     }.

Definition ord_sum (A B : Ord) : Ord.
Proof.
  destruct A as [A LA LAw LAe LAt], B as [B LB LBw LBe LBt].
  refine (BuildOrd (set_sum A B) 
                   (sum_order LA LB)
                   (sum_order_wf LA LB LAw LBw)
                   (sum_order_ext LA LB LAw LBw LAe LBe)
                   _).
  intros z z' z'' Hzz' Hz'z''.
  destruct z as [a | b], z' as [a' | b'], z'' as [a'' | b'']; simpl in *.
  apply (LAt a a' a'' Hzz' Hz'z''). 
  apply Hz'z''. contradiction. apply Hzz'.
  contradiction. contradiction. contradiction.
  apply (LBt b b' b'' Hzz' Hz'z'').
Defined.


(** %\exer{10.5}{365}% 
Prove that if $(A, <_{A})$ and $(B, <_{B})$ are well-founded, extensional, or
ordinals, then so is $A \times B$, with $<$ defined by
%\[
  ((a, b) < (a', b')) \defeq (a <_{A} a') \lor ((a = a') \land (b <_{B} b')).
\]%
*)

(** %\soln%
(i)
Suppose that $<_{A}$ and $<_{B}$ are well-founded.  As in the previous
exercise, we do nested well-founded induction.  First let $a:A$; we show that
$b < b'$ implies $(a, b) < (a, b')$ for all $b, b' : B$ by double well-founded
induction on $B$.  So suppose that $b, b' : B$ and $s : \acc(b)$ and $s' :
\acc(b')$.
*)

Definition set_prod (A B : hSet) := @BuildhSet (A * B) (hset_prod A _ B _).

Definition lexical_order {A B : hSet} (LA : A -> A -> hProp) 
           (LB : B -> B -> hProp) (z z' : set_prod A B)
  : hProp
  := match z with 
       | (a, b) => match z' with
                     | (a', b') => BuildhProp (Brck ((LA a a') 
                                             + 
                                             ((a = a') * (LB b b'))))
                   end
     end.


Lemma lexical_order_wf `{Funext} {A B : hSet} 
      (LA : A -> A -> hProp) (LB : B -> B -> hProp)
  : (well_founded LA) -> (well_founded LB) -> well_founded (lexical_order LA LB).
Proof.
  transparent assert (HB : (
    forall b, @acc _ LB b -> forall b', @acc _ LB b' -> forall a, 
    @acc _ (lexical_order LA LB) (a, b) -> @acc _ (lexical_order LA LB) (a, b')
  )).
  intros b s b' s' a Ha.
  induction s as [b f g], s' as [b' f' g'], Ha as [z F G].
  destruct z as [a'' b'']. simpl in *.
Admitted.
  
    

(** %\exer{10.6}{365}% 
Define the usul algebraic operations on ordinals, and prove that they
satisfy the usual properties.
*)


(** %\exer{10.7}{365}% 
Note that $\bool$ is an ordinal, under the obvious relation $<$ such that
$0_{\bool} < 1_{\bool}$ only.
%\begin{enumerate}
  \item Define a relation $<$ on $\prop$ which makes it into an ordinal.
  \item Show that $\bool =_{\ord} \prop$ if and only if $\LEM{}$ holds.
\end{enumerate}%
*)

(** %\soln%
For $P, Q : \prop$, define $(P < Q) \defeq ((P \to Q) = \unit)$.  We
must show that this $<$ is well-founded, extensional, and transitive.
To show that it's well-founded, suppose that $Q : \prop$; we show that
$P$ is accessible for all $P < Q$.  That is,
*)

Definition heyting_ord `{Funext} (P Q : hProp) 
  : hProp
  := BuildhProp ((P -> Q) * (Q <> P)).
  



(** %\exer{10.8}{365}% *)
(** %\exer{10.9}{365}% *)
(** %\exer{10.10}{365}% *)
(** %\exer{10.11}{365}% *)
(** %\exer{10.12}{366}% *)
(** %\exer{10.13}{366}% *)
