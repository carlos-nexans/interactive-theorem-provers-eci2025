Unset Universe Checking.
Require Export UniMath.Foundations.All.

(* Instructions: there are 10 exercises. Succesfully completing x exercises will earn you a grade of x. (No partial credit will be given.) Please alter the following comment to tell me which exercises you completed below.*)

(* I completed 3 exercises: Exercise 1, 3, 4.*)

(* Exercise 1 *)

Theorem comp_app { P Q R : UU } (f : P -> Q) (g : Q -> R) (p : P) : R.
Proof.
  exact (g (f p)).
Defined.

(* Exercise 2 *)

(*
Locate "@".
*)

Lemma path_combination {A : UU} {a a' b : A} (p : a = b) (q: a' = b) : a = a'.
(* Another way to combine paths. *)
Proof.
  symmetry in p.
  symmetry.
  apply ( pathscomp0 q p).
Defined.

(* About idpath. *)

(* Exercise 3 *)

Lemma path_combination_fact {A : UU} {a b : A} (p : a = b) : idpath a = path_combination p p.
(* Check that the above way of combining paths does the `right thing'. *)
Proof.
  induction p.
  - apply paths_refl.
Defined.

(* Exercise 4 *)

Theorem exp : nat -> nat -> nat.
Proof.
  intros n m.
  induction m.
  - exact 1.
  - exact (n * IHm).
Defined.

Compute (exp 0 1).

Compute (exp 1 1).

Compute (exp 5 1).

Compute (exp 3 2).

(* Exercise 5 *)

Theorem curried_proj {P Q R : UU} : (P -> (Q /\ R)) -> (P -> Q).
Proof.
  intros H p.
  apply (H p).
Defined.

(* Exercise 6 *)

(*
Search (forall X Y : UU, forall f : X -> Y, forall x y : X, x = y -> (f x) = (f y)).
*)
(* This command searches the library for functions of this kind. You should see in the output that ~maponpaths~ is of this kind. You can then print ~maponpaths~ (i.e. write "Print maponpaths.") to see the definition.

You can use this to find other lemmas from the library. You can use any facts without proof from the library about addition and multiplication as well as ~maponpaths~.*)

Theorem exp_hom {l m n : nat} : exp l (m + n) = (exp l m) * (exp l n).
(* `exp l` takes addition to multiplication.*)
Proof.
  induction m.
  - simpl.
    reflexivity.
  - simpl.
    apply (maponpaths (fun n: nat => l * n)) in IHm.
    rewrite IHm.
    rewrite natmultassoc.
    reflexivity.
Defined.

(* Exercise 7 *)

(* isaprop is defined differently in UniMath than we defined in lectures. Show that these two definitions are the the same. *)

(* Note that this is the hardest exercise, but the ones following depend on it. Feel free to leave it admitted and use the result without proof in the following exercises. *)

Lemma prop_thm_left {P : UU} : isaprop P -> (forall x y : P, x = y).
Proof.
  unfold isaprop.
  unfold isofhlevel.
  unfold iscontr.
  intro pred_con.
  intros x y.
  set ( c := pred_con x y).
  induction c.
  exact pr1.
Defined.

Lemma prop_thm_right {P : UU} : (forall x y : P, x = y) -> isaprop P.
Proof.
  intros pred_con.
  (* Search (_ -> isaprop _). *)
  (* Search (_ -> iscontr _). *)
  assert (P -> iscontr P).
  (* Can use iscontraprop1inv: ∏ {X : UU}, (X → iscontr X) → isaprop X *)
  intro t.
  exact (make_iscontr t (λ p : P, pred_con p t)).
  apply iscontraprop1inv.
  assumption.
Defined.

Theorem prop_thm {P : UU} : isaprop P <-> (forall x y : P, x = y).
(* The different definitions of isaprop are logically equivalent. *)
Proof.
  split.
  - apply prop_thm_left. 
  - apply prop_thm_right.
Defined.

(* Exercise 8 *)

(* Show that the dependent product type former commutes with `isaprop`.*)

(*
Print isaprop.
Print isofhlevel.
Print iscontr.
Print funextfun.
Print funextsec.
Locate "~".
*)

Theorem prop_commutes_Π {A : UU} {B : A -> UU} (p : forall x : A, isaprop (B x)) : isaprop (forall x : A, (B x)).
Proof.
  apply prop_thm.
  
  intros f g.
  
  assert (H : forall x : A, f x = g x).
  
  - intro x.
    apply prop_thm.
    exact (p x).
  - apply funextsec.
    exact H.
  (* there might be a way to prove this in a simpler way, I might try to prove it later *)
Defined.

(* Exercise 9 *)

(* Show that isweq f is a proposition. *)

(* Use ~isapropisofhlevel~ from the library.
Compute isofhlevel 0.

About isapropisofhlevel.
Print isapropisweq.
Print isapropiscontr.
About impred.
About hfiber.
*)

(*

Search isaprop (isweq _).

isapropisofhlevel : \u220f (n : nat) (X : UU), isaprop (isofhlevel n X)

Compute (isofhlevel 1 (isweq _)).
*)

Theorem isweq_is_prop {A B : UU} (f : A -> B) : isaprop (isweq f).
Proof.
  unfold isweq.
  apply prop_commutes_Π.
  (* adds the arbitrary type *)
  intro t.
  apply isapropiscontr.
Defined.

(* Exercise 10 *)

(* You are allowed to use isweq_iso from the library in this proof: it says if f is a quasiequivalence, then f is an equivalence in that sense.*)

(* 
About isweq_iso.
About hProp.
About invmap.
*)


Lemma prop_weq_impl_prop_equiv (P Q : hProp) : (weq P Q) -> (P <-> Q).
  intro eq.
  unfold weq in eq.
  induction eq as [f pred].
  split.
  - exact f.
  - intros q.
    (* Search (isweq _). *)
    (* Search make_weq *)
    set (neweq := make_weq f pred).
    (* Search weq. *)
    (* About invweq. *)
    set ( newinveq := invweq neweq ).
    exact (newinveq q).
Defined.

Lemma prop_weq_consequence_prop_equiv (P Q : hProp) : (P <-> Q) -> (weq P Q).
  intros H.

  (* try to advance manipulating terms *)
  set (p := pr1 P).
  set (q := pr1 Q).
  set (pf := pr2 P).
  set (qf := pr2 Q).

  destruct H as [pq qp].

  exact (weqimplimpl pq qp pf qf).
Defined.

Theorem prop_equiv_to_log_equiv (P Q : hProp) : (weq P Q) <-> (P <-> Q).
(* An equivalence between propositions is (logically equivalent to) a logical equivalence. *)
Proof.
  split.
  - apply prop_weq_impl_prop_equiv.
  - apply prop_weq_consequence_prop_equiv.
Defined.