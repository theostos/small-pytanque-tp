Theorem Modus_ponens : forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
  intros.
  apply H0.
  exact H.
Qed.

Theorem Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P.
Proof.
  unfold not.
  intros.
  inversion H.
  apply H1.
  apply H2.
  exact H0.
Qed.

Theorem Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q.
Proof.
  unfold not.
  intros.
  inversion H.
  contradiction.

  exact H1.
Qed.


Theorem DeMorgan1 : forall P Q : Prop, ~P \/ ~Q -> ~(P /\ Q).
Proof.
  unfold not.
  intros.
  inversion H0.
  inversion H.
  apply H3.
  exact H1.

  apply H3.
  apply H2.
Qed.

Theorem DeMorgan2 : forall P Q : Prop, ~P /\ ~Q -> ~(P \/ Q).
Proof.
  unfold not.
  intros.
  inversion H.
  inversion H0.
  apply H1.
  apply H3.

  apply H2.
  apply H3.
Qed.

Theorem DeMorgan3 : forall P Q : Prop, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not.
  intros.
  split.
  intros.
  apply H.
  left.
  exact H0.

  intros.
  apply H.
  right.
  exact H0.
Qed.

Theorem NotNot_LEM : forall P : Prop, ~ ~(P \/ ~P).
Proof.
  unfold not.
  intros.
  apply H.
  right.
  intros.
  apply H.
  left.
  exact H0.
Qed.
