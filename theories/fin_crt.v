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

From KruskalFinite
  Require Import finite.

Require Import crt_extra.

Set Implicit Arguments.

Section fin_clos_refl_trans.

  Variables (X : Type) (R : X → X → Prop) (Rfin : ∀x, fin (R x)).

  Theorem fin_clos_refl_trans : ∀x, Acc R⁻¹ x → fin (clos_refl_trans _ R x).
  Proof. induction 1 using Fix_F; finite eq (crt_head_equiv _ _). Qed.

End fin_clos_refl_trans.
