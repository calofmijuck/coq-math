From Coq Require Import Logic.FunctionalExtensionality.

From Basics Require Import Logic.

Definition surjective {X Y : Type} (f : X -> Y) :=
  forall y : Y, (exists x : X, y = f x).

Definition injective {X Y : Type} (f : X -> Y) :=
  forall x1 x2 : X, x1 <> x2 -> f x1 <> f x2.

Lemma injective_contrapositive : forall {X Y : Type} (f : X -> Y),
  (forall x1 x2 : X, f x1 = f x2 -> x1 = x2) -> injective f.
Proof.
  intros X Y f Hinj x1 x2.
  specialize Hinj with x1 x2.
  apply modus_tollens, Hinj.
Qed.

Definition bijective {X Y : Type} (f : X -> Y) :=
  surjective f /\ injective f.

Lemma functional_extensionality:
  forall {X Y : Type} (f g : X -> Y),
    f = g <-> (forall x : X, f x = g x).
Proof.
  split; intros.
  - rewrite H. auto.
  - apply functional_extensionality. auto.
Qed.
