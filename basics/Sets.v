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
Arguments full_set {U}.
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

Global Hint Constructors full_set : core.
Global Hint Constructors intersection : core.
Global Hint Constructors union : core.
Global Hint Constructors difference : core.
Global Hint Constructors complement : core.

Global Hint Unfold subset : core.
Global Hint Unfold symmetric_difference : core.

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

Section Basics.

  Variable U : Type.

  (* Intersection Lemmas *)
  Lemma intersection_empty:
    forall (A : set U), A ⋂ ∅ == ∅.
  Proof.
    autounfold. split; intros.
    - inv H. inv H1.
    - inv H.
  Qed.

  Lemma intersection_full_set:
    forall (A : set U), A ⋂ full_set == A.
  Proof.
    autounfold; split; intros; auto.
    inv H; auto.
  Qed.

  Lemma intersection_self:
    forall (A : set U), A ⋂ A == A.
  Proof.
    autounfold; split; intros; eauto.
    inv H; eauto.
  Qed.

  Lemma intersection_complement:
    forall (A : set U), A ⋂ (complement A) == ∅.
  Proof.
    autounfold; split; intros; inv H; inv H1; contradiction.
  Qed.

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

  (* Union Lemmas *)
  Lemma union_empty:
    forall (A : set U), A ⋃ ∅ == A.
  Proof.
    autounfold; split; intros; auto.
    inv H; auto. inv H0.
  Qed.

  Lemma union_full_set:
    forall (A : set U), A ⋃ full_set == full_set.
  Proof. auto. Qed.

  Lemma union_self:
    forall (A : set U), A ⋃ A == A.
  Proof.
    autounfold; split; intros; auto. inv H; auto.
  Qed.

  Lemma union_complement:
    forall (A : set U), A ⋃ (complement A) == full_set.
  Proof.
    autounfold; split; intros; auto.
    destruct (element_decidable x A); eauto.
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

  (* Distributive Laws *)
  Lemma intersection_dist_left:
    forall (A B C : set U), A ⋂ (B ⋃ C) == (A ⋂ B) ⋃ (A ⋂ C).
  Proof.
    autounfold; split; intros; inv H.
    - inv H1; auto.
    - inv H0; auto.
    - inv H0; auto.
  Qed.

  Lemma intersection_dist_right:
    forall (A B C : set U), (A ⋃ B) ⋂ C  == (A ⋂ C) ⋃ (B ⋂ C).
  Proof.
    intros.
    rewrite intersection_comm.
    rewrite intersection_dist_left.
    rewrite (intersection_comm C A).
    rewrite (intersection_comm C B).
    auto.
  Qed.

  Lemma union_dist_left:
    forall (A B C : set U), A ⋃ (B ⋂ C) == (A ⋃ B) ⋂ (A ⋃ C).
  Proof.
    autounfold; split; intros; inv H; auto.
    - inv H0; auto.
    - inv H0; auto. inv H1; auto.
  Qed.

  Lemma union_dist_right:
    forall (A B C : set U), (A ⋂ B) ⋃ C == (A ⋃ C) ⋂ (B ⋃ C).
  Proof.
    intros.
    rewrite union_comm.
    rewrite union_dist_left.
    rewrite (union_comm C A).
    rewrite (union_comm C B).
    auto.
  Qed.

  (* De Morgan Laws *)
  Lemma de_morgan_union:
    forall (A B : set U),
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

  (* Complement Laws *)
  Lemma complement_empty:
    (@complement U ∅) == full_set.
  Proof.
    autounfold; split; intros; auto.
    apply complement_intro. intros contra. inv contra.
  Qed.

  Lemma complement_full_set:
    (@complement U full_set) == ∅.
  Proof.
    autounfold; split; intros.
    - inv H. exfalso. apply H0. auto.
    - inv H.
  Qed.

  Lemma complement_complement:
    forall (A : set U), complement (complement A) == A.
  Proof.
    autounfold; split; intros.
    - destruct (element_decidable x A); auto.
      inv H. exfalso. auto.
    - apply complement_intro. intros contra.
      inv contra. contradiction.
  Qed.

  (* Difference Laws *)
  Lemma difference_as_intersection:
    forall (A B : set U), A \ B == A ⋂ (complement B).
  Proof.
    autounfold; split; intros.
    - split; inv H; destruct H0; eauto.
    - inv H. inv H1. eauto.
  Qed.

  Corollary difference_empty:
    forall (A : set U), A \ ∅ == A.
  Proof.
    intros.
    rewrite difference_as_intersection.
    rewrite complement_empty.
    rewrite intersection_full_set.
    reflexivity.
  Qed.

  Corollary difference_from_empty:
    forall (A : set U), ∅ \ A == ∅.
  Proof.
    intros.
    rewrite difference_as_intersection.
    rewrite intersection_comm.
    rewrite intersection_empty.
    reflexivity.
  Qed.

  Corollary difference_self:
    forall (A : set U), A \ A == ∅.
  Proof.
    intros.
    rewrite difference_as_intersection.
    rewrite intersection_complement.
    reflexivity.
  Qed.

End Basics.

Section SubsetLemmas.

  Variable U : Type.

  Global Instance subset_preorder: PreOrder (@subset U).
  Proof. constructor; auto. Qed.

  Lemma subset_empty_set:
    forall (A : set U), ∅ ⊆ A.
  Proof.
    autounfold. contradiction.
  Qed.

  Lemma subset_intersection:
    forall (A B : set U), A ⊆ B <-> A ⋂ B == A.
  Proof.
    autounfold; split; intros.
    - split; intros; auto. inv H0. auto.
    - destruct H. apply H1 in H0. destruct H0. auto.
  Qed.

  Lemma subset_union:
    forall (A B : set U), A ⊆ B <-> A ⋃ B == B.
  Proof.
    autounfold; split; intros.
    - split; intros; auto. inv H0; auto.
    - destruct H. auto.
  Qed.

  Lemma subset_difference:
    forall (A B : set U), A ⊆ B <-> A \ B == ∅.
  Proof.
    autounfold; split; intros.
    - split; intros; try inv H0.
      destruct H1 as [H1 H2]. exfalso. auto.
    - destruct H, (element_decidable x B); auto.
      assert (x ∈ ∅) by auto. inv H3.
  Qed.

  Corollary subset_intersection_complement:
    forall (A B : set U), A ⊆ B <-> A ⋂ (complement B) == ∅.
  Proof.
    intros. rewrite <- difference_as_intersection.
    apply subset_difference.
  Qed.

  Lemma subset_complement_subset:
    forall (A B : set U),
      A ⊆ B <-> (complement B) ⊆ (complement A).
  Proof.
    autounfold; split; intros.
    - inv H0. auto.
    - destruct (element_decidable x B); auto.
      assert (x ∈ complement B) by auto.
      apply H in H2. inv H2. contradiction.
  Qed.

  Corollary subset_complement_difference:
    forall (A B : set U),
      A ⊆ B <-> (complement B) \ (complement A) == ∅.
  Proof.
    etransitivity.
    apply subset_complement_subset.
    apply subset_difference.
  Qed.

End SubsetLemmas.

Section SymmetricDifference.

  Variable U : Type.

  Lemma symmetric_difference_id:
    forall (A : set U), A △ ∅ == A.
  Proof.
    intros. unfold symmetric_difference.
    rewrite difference_empty.
    rewrite difference_from_empty.
    apply union_empty.
  Qed.

  Lemma symmetric_difference_self:
    forall (A : set U), A △ A == ∅.
  Proof.
    intros. unfold symmetric_difference.
    rewrite difference_self.
    rewrite union_empty.
    reflexivity.
  Qed.

  Lemma symmetric_difference_comm:
    forall (A B : set U), A △ B == B △ A.
  Proof.
    intros. unfold symmetric_difference.
    rewrite union_comm.
    reflexivity.
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
