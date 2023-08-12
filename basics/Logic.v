(* Rules of Inference *)

(* Rules for negation *)
Lemma reductio_ad_absurdum : forall P Q : Prop,
  (P -> Q) -> (P -> ~Q) -> ~P.
Proof.
  intros. intros HP.
  apply H0 in HP as HNQ.
  apply H in HP as HQ.
  contradiction.
Qed.

Lemma ex_contradictione_quodlibet : forall P Q : Prop,
  P -> ~P -> Q.
Proof. intros. contradiction. Qed.

Lemma double_negation_introduction : forall P : Prop,
  P -> ~~P.
Proof. auto. Qed.

(* Rules for conditionals *)
Lemma modus_ponens : forall P Q : Prop,
  (P -> Q) -> P -> Q.
Proof. auto. Qed.

Lemma modus_tollens : forall P Q : Prop,
  (P -> Q) -> ~Q -> ~P.
Proof. auto. Qed.

(* Rules for conjunctions *)
Lemma conjuction_introduction : forall P Q : Prop,
  P -> Q -> P /\ Q.
Proof. auto. Qed.

Lemma conjunction_elimination_left : forall P Q : Prop,
  P /\ Q -> P.
Proof. intros P Q [HP HQ]; auto. Qed.

Lemma conjunction_elimination_right : forall P Q : Prop,
  P /\ Q -> Q.
Proof. intros P Q [HP HQ]; auto. Qed.

Lemma conjunction_commutative : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros. destruct H; split; auto.
Qed.

Lemma conjunction_associative : forall P Q R : Prop,
  (P /\ Q) /\ R -> P /\ (Q /\ R).
Proof.
  intros. destruct H as [H H1]; destruct H; split; auto.
Qed.

(* Rules for disjunctions *)
Lemma disjunction_introduction_left : forall P Q : Prop,
  P -> P \/ Q.
Proof. auto. Qed.

Lemma disjunction_introduction_right : forall P Q : Prop,
  Q -> P \/ Q.
Proof. auto. Qed.

Lemma disjunction_elimination : forall P Q R : Prop,
  (P -> R) -> (Q -> R) -> (P \/ Q) -> R.
Proof.
  intros. destruct H1; auto.
Qed.

Lemma disjunctive_syllogism_left : forall P Q : Prop,
  (P \/ Q) -> ~P -> Q.
Proof.
  intros. destruct H; auto. contradiction.
Qed.

Lemma disjunctive_syllogism_right : forall P Q : Prop,
  (P \/ Q) -> ~Q -> P.
Proof.
  intros. destruct H; auto. contradiction.
Qed.

Lemma constructive_dilemma : forall P Q R S : Prop,
  (P -> R) -> (Q -> S) -> (P \/ Q) -> (R \/ S).
Proof.
  intros. destruct H1; auto.
Qed.

Lemma disjunction_commutative : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof. intros. destruct H; auto. Qed.

Lemma disunction_associative : forall P Q R : Prop,
  (P \/ Q) \/ R -> P \/ (Q \/ R).
Proof.
  intros. destruct H as [H | H]; auto.
  destruct H; auto.
Qed.

(* Rules for biconditionals *)
Lemma biconditional_introduction : forall P Q : Prop,
  (P -> Q) -> (Q -> P) -> (P <-> Q).
Proof. split; auto. Qed.

Lemma biconditional_elimination_left_mp : forall P Q : Prop,
  (P <-> Q) -> P -> Q.
Proof.
  intros. destruct H; auto.
Qed.

Lemma biconditional_elimination_right_mp : forall P Q : Prop,
  (P <-> Q) -> Q -> P.
Proof.
  intros. destruct H; auto.
Qed.

Lemma biconditional_elimination_left_mt : forall P Q : Prop,
  (P <-> Q) -> ~P -> ~Q.
Proof.
  intros. destruct H; auto.
Qed.

Lemma biconditional_elimination_right_mt : forall P Q : Prop,
  (P <-> Q) -> ~Q -> ~P.
Proof.
  intros. destruct H; auto.
Qed.

Lemma biconditional_elimination_disjunction : forall P Q : Prop,
  (P <-> Q) -> (P \/ Q) -> (P /\ Q).
Proof.
  intros. destruct H, H0; auto.
Qed.

Lemma biconditional_elimination_disjunction_not : forall P Q : Prop,
  (P <-> Q) -> (~P \/ ~Q) -> (~P /\ ~Q).
Proof.
  intros. destruct H, H0; auto.
Qed.

(* etc *)
Lemma exportation : forall P Q R : Prop,
  (P /\ Q) -> R <-> (P -> Q -> R).
Proof.
  split; auto.
  destruct H; auto.
Qed.

Lemma distributive_disjunction : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  split; intros.
  - destruct H as [H | [H1 H2]]; split; auto.
  - destruct H as [H1 H2]; destruct H1, H2; auto.
Qed.

Lemma distributive_conjunction : forall P Q R : Prop,
  P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof.
  split; intros.
  - destruct H as [H [H1 | H1]]; auto.
  - destruct H as [[H1 H2] | [H1 H2]]; auto.
Qed.

Lemma material_implication_converse : forall P Q : Prop,
  (~P \/ Q) -> (P -> Q).
Proof.
  intros. destruct H; auto. contradiction.
Qed.

Lemma resolution : forall P Q R : Prop,
  (P \/ Q) -> (~P \/ R) -> (Q \/ R).
Proof.
  intros. destruct H, H0; auto. contradiction.
Qed.

(* rules that need excluded_middle *)
Axiom excluded_middle : forall P : Prop, P \/ ~P.

Lemma double_negation_elimination : forall P : Prop,
  ~~P -> P.
Proof.
  intros. destruct (excluded_middle P); auto. contradiction.
Qed.

Lemma material_implication : forall P Q : Prop,
  (P -> Q) -> (~P \/ Q).
Proof.
  intros. destruct (excluded_middle P); auto.
Qed.

Lemma reductio_ad_absurdum_neg : forall P Q : Prop,
  (~P -> Q) -> (~P -> ~Q) -> P.
Proof.
  intros. destruct (excluded_middle P); auto.
  apply H in H1 as HQ.
  apply H0 in H1 as HNQ.
  contradiction.
Qed.

Lemma contraposition_converse : forall P Q : Prop,
  (~Q -> ~P) -> (P -> Q).
Proof.
  intros. destruct (excluded_middle Q); auto.
  apply H in H1. contradiction.
Qed.
