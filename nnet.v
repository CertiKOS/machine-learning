Require Import Bool.
Require Import List.
Require Import ZArith.
Require Import Psatz.

Open Scope Z.

(** Network definition *)
(* Corresponds to
  z0 = x
  ẑi = zi-1 Wi + bi
  zi = max(ẑi, 0)

  Really x, Wi should be matrices/vectors, but currently are integers.
  Assumes n = length W = length B = number of layers - 1
*)
Fixpoint network_loop x n W B :=
  match n, W, B with
  | O, nil, nil => x
  | S n', w :: W', b :: B' =>
      let z := network_loop x n' W' B' in
      let zhat := z * w + b in
      Z.max zhat 0
  | _, _, _ => 0
  end.

Definition network x W B :=
  network_loop x (length W) W B.

Class NetworkParams := {
  label : Set;
  label_eq : label -> label -> bool;
  classify : Z -> label;

  label_eq_sound l1 l2 : label_eq l1 l2 = true -> l1 = l2
}.

Section Robustness.

  Context `{NetworkParams}.

  (** Robustness definition *)
  Definition local_robust x0 W B delta :=
    forall x,
      Z.abs (x - x0) <= Z.of_nat delta ->
      classify (network x W B) = classify (network x0 W B).

  (** Robustness checker *)
  (* Collect all points within delta of x0 in a list *)
  Fixpoint nearby_points x0 delta :=
    match delta with
    | O => x0 :: nil
    | S delta' =>
        x0 + Z.of_nat delta :: x0 - Z.of_nat delta :: nearby_points x0 delta'
    end.

  (* Compare the network at x0 against all points in X *)
  Fixpoint is_robust_aux x0 X W B :=
    match X with
    | nil => true
    | x :: X' =>
        label_eq (classify (network x W B)) (classify (network x0 W B)) &&
        is_robust_aux x0 X' W B
    end.

  (* Compare the network at x0 against all points within delta *)
  Definition is_robust x0 W B delta :=
    is_robust_aux x0 (nearby_points x0 delta) W B.

  Arguments is_robust _ _ _ _ /.

  (** Soundness proof *)
  (* If the checker returns true then it is actually robust *)
  Lemma is_robust_sound : forall x0 W B delta,
    is_robust x0 W B delta = true ->
    local_robust x0 W B delta.
  Proof.
    induction delta; cbn; intros * Hrobust.
    - (* delta = 0, trivial *)
      hnf; cbn; intros.
      assert (x = x0) by lia; subst; auto.
    - (* induction case *)
      hnf; cbn; intros * Hdelta.
      rewrite Zpos_P_of_succ_nat in *.
      rewrite !andb_true_iff in Hrobust.
      destruct Hrobust as (Heq_plus & Heq_minus & Hrobust).
      apply label_eq_sound in Heq_plus.
      apply label_eq_sound in Heq_minus.
      assert (Hcase: Z.abs (x - x0) <= Z.of_nat delta \/
                     Z.abs (x - x0) = Z.succ (Z.of_nat delta)) by lia.
      destruct Hcase as [Hdelta' | Hdelta'].
      + (* By induction *)
        apply IHdelta; auto.
      + (* By Heq_plus/minus *)
        assert (Hcase: x = x0 + Z.succ (Z.of_nat delta) \/
                       x = x0 - Z.succ (Z.of_nat delta)) by lia.
        destruct Hcase; subst; auto.
  Qed.

End Robustness.

Section Example.

  (* A and B labels. Values less than 7 are in A, all else in B *)
  Inductive ex_label := A | B.
  Definition ex_classify x :=
    if x <? 10 then A else B.
  Definition ex_label_eq l1 l2 :=
    match l1, l2 with
    | A, A | B, B => true
    | _, _ => false
    end.

  Instance : NetworkParams := {
    label := ex_label;
    classify := ex_classify;
    label_eq := ex_label_eq;
  }.
  Proof. now destruct l1, l2. Defined.

  Let B := (-3 :: -2 :: 3 :: nil).
  Let W := (3 :: 2 :: 1 :: nil).
  Let delta := 3%nat.

  Let x := 9.
  Compute (network x W B). (* 63 *)
  Compute (network (x - Z.of_nat delta) W B). (* 45 *)
  Compute (is_robust x W B delta). (* true *)
  Goal local_robust x W B delta.
  Proof.
    apply is_robust_sound.
    auto.
  Qed.

  Let y := 3.
  Compute (network y W B). (* 27 *)
  Compute (network (y - Z.of_nat delta) W B). (* 9 *)
  Compute (is_robust y W B delta). (* false *)
  Goal ~local_robust x W B delta.
  Proof.
    (* Can't show the opposite direction. Need completeness for that. *)
    Fail apply is_robust_sound.
  Abort.

End Example.
