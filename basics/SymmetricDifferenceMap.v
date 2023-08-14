Require Import Setoid.

From Basics Require Import Sets Logic Functions.

Definition U := Type.

(*
  f_sym is a map that takes two sets and
  returns their symmetric difference.
*)
Definition f_sym (A X : set U) := A △ X.

(* identity function with domain `set U` *)
Definition id_X (X : set U) := X.

Global Hint Unfold f_sym id_X : core.

Theorem exists_f_id:
  exists A, f_sym A = id_X.
Proof.
  exists ∅.
  apply functional_extensionality; intros X.
  apply set_extensionality.
  unfold f_sym, id_X.
  rewrite symmetric_difference_comm.
  rewrite symmetric_difference_id.
  reflexivity.
Qed.

Lemma symd_same:
  forall (A B : set U), (exists X, A △ X == B △ X) -> A == B.
Proof.
  intros. destruct H as [X H].
  rewrite <- (symmetric_difference_id A).
  rewrite <- (symmetric_difference_id B).
  rewrite <- (symmetric_difference_self X).
  rewrite ! symmetric_difference_assoc.
  rewrite H. reflexivity.
Qed.

Theorem symd_extension:
  forall (A B : set U), (exists X, A △ X == B △ X) -> f_sym A = f_sym B.
Proof.
  intros. apply symd_same, set_extensionality in H.
  rewrite H. auto.
Qed.

Lemma f_sym_surjective:
  forall (A : set U), surjective (f_sym A).
Proof.
  unfold surjective.
  intros A Y. exists (A △ Y).
  unfold f_sym. apply set_extensionality.
  rewrite symmetric_difference_assoc.
  rewrite symmetric_difference_self.
  rewrite symmetric_difference_comm.
  rewrite symmetric_difference_id.
  auto.
Qed.

Lemma f_sym_injective:
  forall (A : set U), injective (f_sym A).
Proof.
  intros. apply injective_contrapositive.
  intros X1 X2 H. unfold f_sym in H.
  apply set_extensionality, symd_same.
  exists A.
  rewrite symmetric_difference_comm.
  rewrite H.
  rewrite symmetric_difference_comm.
  auto.
Qed.

Theorem f_sym_bijective : forall A, bijective (f_sym A).
Proof.
  unfold bijective; split.
  - apply f_sym_surjective.
  - apply f_sym_injective.
Qed.
