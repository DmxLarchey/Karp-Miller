(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Arith Utf8.

From KruskalTrees
  Require Import notations idx vec.

Import idx_notations vec_notations.

Set Implicit Arguments.

Section vec_extra.

  Variables (X Y Z : Type) (f : X → Y → Z).

  Definition vec_scal {n} (u : vec _ n) v :=
    vec_set (fun i => f u⦃i⦄ v⦃i⦄).

  Fact vec_scal_prj n u v (i : idx n) : (vec_scal u v)⦃i⦄ = f u⦃i⦄ v⦃i⦄.
  Proof. now unfold vec_scal; vec rew. Qed.

  Variables (P Q : X → Y → Prop).

  Fact vec_fall2_choice n v w :
       (∀i, { P v⦃i⦄ w⦃i⦄ } + { Q v⦃i⦄ w⦃i⦄ })
     → ( vec_fall2 P v w ) + { i : idx n | Q v⦃i⦄ w⦃i⦄ }.
  Proof.
    revert w.
    induction v as [ | x n u IHv ]; intros w HPQ.
    + left; vec invert w; apply vec_fall2_nil.
    + vec invert w as y w.
      destruct (HPQ idx_fst) as [ H1 | H1 ].
      * destruct (IHv w) as [ H2 | (i & Hi) ].
        - intro; apply (HPQ (idx_nxt _)).
        - left; now apply vec_fall2_cons.
        - right; exists (idx_nxt i); now simpl.
      * right; exists idx_fst; now simpl.
  Qed.

  Fact vec_fall2_mono n : P ⊆₂ Q → @vec_fall2 _ _ P n ⊆₂ @vec_fall2 _ _ Q n.
  Proof. induction 2 using vec_fall2_rect; eauto with vec_db. Qed.

End vec_extra.

#[global] Hint Rewrite vec_scal_prj : vec_db.
