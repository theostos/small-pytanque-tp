Section InvolutionInjective.
  Variable A : Type.
  Variable f : A -> A.

  (* Hypothesis: f is an involution *)
  Hypothesis Hinv : forall x, f (f x) = x.

  (* Goal: f is injective *)
  Theorem involution_injective : forall x y, f x = f y -> x = y.
  Proof.
    intros x y H.
    (* Apply f to both sides *)
    rewrite <- Hinv with (x := x).
    rewrite <- Hinv with (x := y).
    rewrite H.
    reflexivity.
  Qed.

End InvolutionInjective.