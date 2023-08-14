Require Import Morphisms Setoid.

Set Implicit Arguments.

Ltac inv H := inversion H; subst.

Section Sets.

  Variable U : Type.

  Definition set : Type := U -> Prop.

  Definition element (x : U) (A : set) : Prop := A x.
  Infix "∈" := element (no associativity, at level 50).

  Inductive empty_set : set :=.
  Notation "∅" := empty_set.

  Inductive full_set : set :=
  | full_set_intro : forall (x : U), x ∈ full_set.

  Axiom element_decidable : forall x X, (x ∈ X) \/ ~ (x ∈ X).

  Definition subset (A B : set) :=
    forall x : U, x ∈ A -> x ∈ B.

  Infix "⊆" := subset (left associativity, at level 50).

  Inductive intersection (A B : set) : set :=
  | intersection_intro : forall x : U,
      x ∈ A -> x ∈ B -> x ∈ (intersection A B).

  Inductive union (A B : set) : set :=
    | union_introl : forall x : U,
        x ∈ A -> x ∈ (union A B)
    | union_intror : forall x : U,
        x ∈ B -> x ∈ (union A B).

  Inductive difference (A B : set) : set :=
    | difference_intro : forall x : U,
        x ∈ A /\ ~ (x ∈ B) -> x ∈ (difference A B).

  Inductive complement (A : set) : set :=
    | complement_intro : forall x : U,
        ~ (x ∈ A) -> x ∈ (complement A).

  Infix "⋂" := intersection (left associativity, at level 40).

  Infix "⋃" := union (left associativity, at level 45).

  Infix "\" := difference (left associativity, at level 43).

  Definition symmetric_difference (A B : set) := (A \ B) ⋃ (B \ A).

End Sets.

Arguments element {U}.
Arguments empty_set {U}.
Arguments subset {U}.
Arguments intersection {U}.
Arguments union {U}.
Arguments difference {U}.
Arguments complement {U}.
Arguments symmetric_difference {U}.

Infix "∈" := element (no associativity, at level 50).
Notation "∅" := empty_set.
Infix "⊆" := subset (left associativity, at level 50).
Infix "⋂" := intersection (left associativity, at level 40).
Infix "⋃" := union (left associativity, at level 45).
Infix "\" := difference (left associativity, at level 43).
Infix "△" := symmetric_difference (at level 45, left associativity).

Global Hint Constructors intersection : core.
Global Hint Constructors union : core.
Global Hint Constructors difference : core.
Global Hint Constructors complement : core.

Global Hint Unfold subset : core.
Global Hint Unfold symmetric_difference : core.

Section SubsetLemmas.

  Variable U : Type.

  Lemma subset_empty_set:
    forall (A : set U), ∅ ⊆ A.
  Proof.
    autounfold. contradiction.
  Qed.

  Global Instance subset_preorder: PreOrder (@subset U).
  Proof. constructor; auto. Qed.

End SubsetLemmas.

Section SetEquality.

  Variable U : Type.

  Definition eq (A B : set U) := A ⊆ B /\ B ⊆ A.

  Infix "==" := eq (at level 70).

  Hint Unfold eq : core.

  Lemma eq_reflexive:
    forall (A : set U), A == A.
  Proof. auto. Qed.

  Lemma eq_symmetric:
    forall (A B : set U), A == B -> B == A.
  Proof.
    autounfold. intros. intuition.
  Qed.

  Lemma eq_transitive:
    forall (A B C : set U), A == B -> B == C -> A == C.
  Proof.
    autounfold. intros; split;
    destruct H as [HAB HBA];
    destruct H0 as [HBC HCB]; auto.
  Qed.

  Global Instance Equivalence_eq : Equivalence eq.
  Proof.
    split; autounfold.
    - apply eq_reflexive.
    - apply eq_symmetric.
    - apply eq_transitive.
  Qed.

  Axiom set_extensionality: forall (A B : set U), A == B -> A = B.

End SetEquality.

Infix "==" := eq (at level 70).

Global Hint Unfold eq : core.

Section Basics.

  Variable U : Type.

  Lemma intersection_comm:
    forall (A B : set U), A ⋂ B == B ⋂ A.
  Proof.
    split; autounfold; intros; inv H; auto.
  Qed.

  Lemma intersection_assoc:
    forall (A B C : set U), (A ⋂ B) ⋂ C == A ⋂ (B ⋂ C).
  Proof.
    autounfold; split; intros; inv H.
    - inv H0; auto.
    - inv H1; auto.
  Qed.

  Lemma union_comm:
    forall (A B : set U), A ⋃ B == B ⋃ A.
  Proof.
    autounfold; split; intros; inv H; auto.
  Qed.

  Lemma union_assoc:
    forall (A B C : set U), (A ⋃ B) ⋃ C == A ⋃ (B ⋃ C).
  Proof.
    autounfold; split; intros; inv H; auto; inv H0; auto.
  Qed.

  Lemma intersection_dist:
    forall (A B C : set U), A ⋂ (B ⋃ C) == (A ⋂ B) ⋃ (A ⋂ C).
  Proof.
    autounfold; split; intros; inv H.
    - inv H1; auto.
    - inv H0; auto.
    - inv H0; auto.
  Qed.

  Lemma union_dist:
    forall (A B C : set U), A ⋃ (B ⋂ C) == (A ⋃ B) ⋂ (A ⋃ C).
  Proof.
    autounfold; split; intros; inv H; auto.
    - inv H0; auto.
    - inv H0; auto. inv H1; auto.
  Qed.

  Lemma de_morgan_union : forall (A B : set U),
    complement (A ⋃ B) == (complement A) ⋂ (complement B).
  Proof.
    autounfold; split; intros; inv H; clear H.
    - auto 6.
    - inv H0. inv H1.
      apply complement_intro. intros contra. inv contra; auto.
  Qed.

  Lemma de_morgan_intersection:
    forall (A B : set U),
    complement (A ⋂ B) == (complement A) ⋃ (complement B).
  Proof.
    autounfold; split; intros; inv H; clear H.
    - destruct (element_decidable x A), (element_decidable x B); auto.
      exfalso. eauto.
    - apply complement_intro. intros contra.
      inv contra. inv H0. contradiction.
    - apply complement_intro. intros contra.
      inv contra. inv H0. contradiction.
  Qed.

End Basics.

Section SymmetricDifference.

  Variable U : Type.

  Lemma symmetric_difference_id:
    forall (A : set U), A △ ∅ == A.
  Proof.
    autounfold; split; intros.
    - inv H; inv H0; intuition. inv H2.
    - apply union_introl.
      apply difference_intro; split; auto.
      intros contra. inv contra.
  Qed.

  Lemma symmetric_difference_self:
    forall (A : set U), A △ A == ∅.
  Proof.
    autounfold; split; intros.
    - inv H; destruct H0; destruct H0; contradiction.
    - inv H.
  Qed.

  Lemma symmetric_difference_comm:
    forall (A B : set U), A △ B == B △ A.
  Proof.
    autounfold; split; intros; inv H; auto.
  Qed.

  Lemma symmetric_difference_assoc:
    forall (A B C : set U), A △ (B △ C) == (A △ B) △ C.
  Proof.
    autounfold; split; intros;
    inv H; clear H; destruct H0; inv H; clear H.
    - destruct (element_decidable x B).
      + apply union_intror, difference_intro; split.
        destruct (element_decidable x C); auto.
        * exfalso. auto.
        * intros contra. inv contra; inv H2; destruct H3; contradiction.
      + apply union_introl, difference_intro; split.
        destruct (element_decidable x C); auto. intros Hc. auto.
    - inv H0; clear H0; inv H; clear H; destruct H0.
      + apply union_introl, difference_intro; split; auto.
      + apply union_intror,difference_intro; split; auto.
        intros contra; inv contra; inv H2; destruct H3; contradiction.
    - inv H0; inv H; destruct H2; clear H H0.
      + apply union_introl, difference_intro; split; auto.
        intros contra. inv contra; inv H; destruct H0; contradiction.
      + apply union_intror, difference_intro; split; auto.
    - destruct (element_decidable x B).
      + apply union_introl, difference_intro; split.
        destruct (element_decidable x A); auto.
        * exfalso. auto.
        * intros contra. inv contra; inv H2; destruct H3; contradiction.
      + apply union_intror, difference_intro; split.
        destruct (element_decidable x A); auto. intros contra. auto.
  Qed.

End SymmetricDifference.

Section Rewriting.

  Variable U : Type.

  Let eq := @eq U.

  Global Instance intersection_compat:
    Proper (eq ==> eq ==> eq) intersection.
  Proof.
    intros X Y H X' Y' H'. inv H; inv H'.
    split; split; intros; destruct H4; eauto.
  Qed.

  Global Instance union_compat:
    Proper (eq ==> eq ==> eq) union.
  Proof.
    intros X Y H X' Y' H'. inv H; inv H'.
    split; intros x Hx; destruct Hx; eauto.
  Qed.

  Global Instance difference_compat:
    Proper (eq ==> eq ==> eq) difference.
  Proof.
    intros X Y H X' Y' H'. inv H; inv H'.
    split; intros x Hx; destruct Hx, H4;
    apply difference_intro; split; eauto.
  Qed.

  Global Instance complement_compat:
    Proper (eq ==> eq) complement.
  Proof.
    intros X Y H. inv H; split; intros x Hx; inv Hx; eauto.
  Qed.

  Global Instance symmetric_difference_compat:
    Proper (eq ==> eq ==> eq) symmetric_difference.
  Proof.
    intros X Y H X' Y' H'. autounfold.
    rewrite H, H'. reflexivity.
  Qed.

End Rewriting.

Section PowerSet.

  Variable U : Type.

  Inductive power_set (A : set U) : set (set U) :=
  | power_set_intro : forall (X : set U),
      X ⊆ A -> X ∈ (power_set A).

  Notation "'P(' A ')'" := (power_set A) (at level 45).

  Lemma empty_set_in_power_set:
    forall (A : set U), ∅ ∈ P(A).
  Proof.
    intros. apply power_set_intro, subset_empty_set.
  Qed.

  Lemma self_in_power_set:
    forall (A : set U), A ∈ P(A).
  Proof.
    intros. apply power_set_intro; auto.
  Qed.

  Lemma power_set_monotonic:
    forall (A B : set U), A ⊆ B -> P(A) ⊆ P(B).
  Proof.
    autounfold. intros. inv H0.
    apply power_set_intro. eauto.
  Qed.

End PowerSet.
