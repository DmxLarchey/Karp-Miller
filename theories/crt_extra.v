(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Relations Utf8.

From KruskalTrees
  Require Import notations.

Set Implicit Arguments.

#[global] Notation "x '-[' T ']*>' y" := (clos_refl_trans _ T x y) (at level 70, no associativity, format "x  -[ T ]*>  y").
#[global] Notation "x '-[' T ']+>' y" := (clos_trans _ T x y) (at level 70, no associativity, format "x  -[ T ]+>  y").
#[global] Notation "R '⁻¹'" := (λ u v, R v u) (at level 1, format "R ⁻¹").

Section crt_extra.

  Variables (X : Type) (R : X → X → Prop).

  Hint Constructors clos_refl_trans clos_trans : core.

  Fact clos_refl_trans_rev x y : x -[R]*> y ↔ y -[R⁻¹]*> x.
  Proof. split; induction 1; eauto. Qed.

  Fact clos_trans_rev x y : x -[R]+> y ↔ y -[R⁻¹]+> x.
  Proof. split; induction 1; eauto. Qed.

  Fact clos_trans_refl_trans : clos_trans X R ⊆₂ clos_refl_trans X R.
  Proof. induction 1; eauto. Qed.

  Hint Resolve clos_trans_refl_trans : core.

  Fact clos_trans_inv x y : x -[R]+> y ↔ ∃z, x -[R]*> z ∧ R z y.
  Proof. 
    split. 
    + induction 1 as [ | ? ? ? ? _ _ (? & ? & ?) ]; eauto.
    + intros (? & H & ?); apply clos_rt_t with (1 := H); eauto.
  Qed.

  Fact crt_head_equiv x y : x -[R]*> y ↔ x = y ∨ ∃ z, z -[R]*> y ∧ R x z.
  Proof.
    split.
    + intros [ | y' ]%clos_rt_rt1n_iff; eauto.
      right; exists y'; rewrite clos_rt_rt1n_iff; auto.
    + intros [ <- | (? & ? & ?) ]; eauto.
  Qed.

End crt_extra.
