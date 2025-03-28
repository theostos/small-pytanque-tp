Require Import Reals.
Require Import Psatz.
Require Import Lra.
Require Import Classical.
Require Import ClassicalChoice.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.

Open Scope R_scope.

(*
  In Coq we view a “set of real numbers” as a predicate A : R -> Prop.
*)

(* --- Upper bounds and maximum --- *)

(* The set of upper bounds of a set of real numbers *)
Definition up_bounds (A : R -> Prop) : R -> Prop :=
  fun x => forall a, A a -> a <= x.

(* The predicate "is_maximum a A" means that a is a maximum of A. *)
Definition is_maximum (a : R) (A : R -> Prop) : Prop :=
  A a /\ up_bounds A a.

Notation "a 'is_a_max_of' A" := (is_maximum a A) (at level 70).

(* A set of real numbers has at most one maximum. *)
Lemma unique_max (A : R -> Prop) (x y : R) :
  x is_a_max_of A -> y is_a_max_of A -> x = y.
Proof.
  intros [HxA Hx] [HyA Hy].
  apply Rle_antisym.
  - apply Hy; assumption.
  - apply Hx; assumption.
Qed.

(* --- Lower bounds and infimum --- *)

(* The set of lower bounds of a set of real numbers *)
Definition low_bounds (A : R -> Prop) : R -> Prop :=
  fun x => forall a, A a -> x <= a.

(* We define that x is an infimum of A if x is a maximum of the lower bounds of A. *)
Definition is_inf (x : R) (A : R -> Prop) : Prop :=
  x is_a_max_of (low_bounds A).

Notation "x 'is_an_inf_of' A" := (is_inf x A) (at level 70).

(* Any number greater than the infimum of A is greater than some element of A. *)
Lemma inf_lt (A : R -> Prop) (x : R) :
  x is_an_inf_of A -> forall y, x < y -> exists a, A a /\ a < y.
Proof.
  intros [Hlb Hmax] y Hxy.
  destruct (classic (exists a, A a /\ a < y)) as [Hex|Hnex].
  - exact Hex.
  - assert (Hy_lb: forall a, A a -> y <= a).
    { intros a Ha.
      destruct (Rtotal_order a y) as [Hlt | Hrest].
      - exfalso. 
        apply Hnex.
        exists a.
        split; assumption.
      - destruct Hrest as [Heq|Hgt].
        + lra.
        + apply Rlt_le. exact Hgt.
    }
    specialize (Hmax y Hy_lb).
    lra.
Qed.

(* --- A useful inequality --- *)

(* If y <= x + eps for all 0 < eps then y <= x. *)
Lemma le_of_le_add_eps (x y : R) :
  (forall eps, eps > 0 -> y <= x + eps) -> y <= x.
Proof.
  intros H.
  destruct (Rtotal_order y x) as [Hgt | [Heq | Hlt]].
  - lra.
  - lra.
  - set (eps := (y - x) / 2).
    assert (eps_pos: 0 < eps) by (apply Rdiv_lt_0_compat; lra).
    specialize (H eps eps_pos).
    assert (x_add_eps_lt_y: x + eps < y) by (unfold eps; lra).
    lra.
Qed.

(* --- Limits of sequences --- *)

(* A sequence u converges to l if for every 0 < eps there exists an N such that for all N <= n,
   |u n - l| <= eps. *)
Definition limit (u : nat -> R) (l : R) : Prop :=
  forall eps, eps > 0 -> exists N, forall n, (n >= N)%nat -> Rabs (u n - l) <= eps.

(* If y <= u n for all n and u tends to x then y <= x. *)
Lemma le_lim (x y : R) (u : nat -> R) :
  limit u x -> (forall n, y <= u n) -> y <= x.
Proof.
  intros Hlim Hall.
  apply le_of_le_add_eps.
  intros eps Heps.
  destruct (Hlim eps Heps) as [N HN].
  assert (Hyn: y <= u N) by (apply Hall).
  assert (Hcalc: u N - x <= Rabs (u N - x)) by apply Rle_abs.
  assert (Hsum: x + Rabs (u N - x) <= x + eps) by (apply Rplus_le_compat_l; apply HN; lia).
  lra.
Qed.


(* --- Some elementary real number facts --- *)

(* The reciprocal of (n+1) (with the natural number coerced via INR) is positive. *)
Lemma inv_succ_pos : forall n : nat, 0 < / (INR (n + 1)).
Proof.
  intro n.
  apply Rinv_0_lt_compat.
  apply (lt_INR 0 (n+1)).
  lia.
Qed.

(* For every 0 < eps, there exists N such that for all N <= n, 1/(n+1) <= eps. *)
Lemma limit_inv_succ (eps : R) (Heps : eps > 0) :
  exists N : nat, forall n, (n >= N)%nat -> / (INR (n + 1)) <= eps.
Proof.
Admitted.

(* --- Characterization of the infimum via sequences --- *)
Lemma inf_seq (A : R -> Prop) (x : R) :
  (x is_an_inf_of A) <->
  ((forall a, A a -> x <= a) /\ exists u : nat -> R, limit u x /\ forall n, A (u n)).
Proof.
Admitted.
