(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Relations Utf8.

From KruskalTrees
  Require Import list_utils.

From KruskalFinite
  Require Import finite.

Require Import crt_extra.

Import ListNotations.

Set Implicit Arguments.

(* Via a reversed notations:
          ε     <~>   []
        l ∹ x   <~>   x::l
        l ∺ m   <~>   m++l
   we see lists in reverse order for better human readability *)

Module iseq_notations.

  Notation ε := (@nil _).
  Notation "l '∹' x" := (cons x l) (at level 61, left associativity, format "l  ∹  x").
  Notation "l '∺' m" := (app m l)  (at level 61, left associativity, format "l  ∺  m").

End iseq_notations.

Import iseq_notations.

Section iseq.

  (* iseq stands for indexed sequences (Prop bounded)
     These iseq can be used to represent:
      - regular/nat based
      - over approximated/Ω based
      - and accelerated 
     Petri net transition sequences in a generic way 

     Notice that the list used to record the sequence
     of transitions is in the reverse order, hence the
     reversed notations _ ∹ _ and _ ∺ _ *)
 
  Variables (I X : Type) (R : I → X → X → Prop).

  Unset Elimination Schemes.

  Inductive iseq : list I → X → X → Prop :=
    | iseq_start x₀ :        iseq ε x₀ x₀
    | iseq_next l x₀ x i y : iseq l x₀ x → R i x y → iseq (l ∹ i) x₀ y.

  Set Elimination Schemes.

  Section iseq_ind.

    (* We favor an induction principle where x₀ is fixed *)

    Variables (x₀ : X) (P : list I → X → Prop)
              (P_start : P ε x₀)
              (P_next : ∀ l x i y, iseq l x₀ x → P l x → R i x y → P (l ∹ i) y).

    Definition iseq_ind l x : iseq l x₀ x → P l x.
    Proof.
      intros s; revert l x₀ x s P_start P_next.
      refine (fix loop l x0 x s { struct s } := _ ).
      destruct s as [ x0 | l x0 x t y hs hx ]; intros ps pn.
      + apply ps.
      + apply pn with (1 := hs) (3 := hx),
            loop with (3 := pn); trivial.
    Qed. 

  End iseq_ind.

  Hint Constructors iseq : core.

  Fact iseq_inv l x₀ x : 
        iseq l x₀ x 
      → match l with
        | ε     => x = x₀
        | l ∹ i => ∃ u, iseq l x₀ u ∧ R i u x
        end.
  Proof. intros []; eauto; split; auto; right; eauto. Qed.

End iseq.

#[local] Hint Constructors iseq : core.

(* The regular tactic "induction ... using iseq_ind" does 
   not work with the scheme iseq_ind unfortunately,
   so we implement a tailored induction tactic *)

Tactic Notation "induction" "iseq" "on" hyp(H) "as" 
     simple_intropattern(l) 
     simple_intropattern(x)
     simple_intropattern(i) 
     simple_intropattern(y)
     simple_intropattern(H1) 
     simple_intropattern(IH1)
     simple_intropattern(H2) :=
  match type of H with
  | iseq _ ?lt _ ?z => pattern lt, z; revert lt z H; apply iseq_ind; [ | intros l x i y H1 IH1 H2 ]
  end.

Tactic Notation "induction" "iseq" "on" hyp(H) := induction iseq on H as ? ? ? ? ? ? ?.

Fact iseq_mono I X (R T : I → X → X → Prop) :
        (∀ i x y, R i x y → T i x y)
       → ∀ l x y, iseq R l x y → iseq T l x y.
Proof. intros ? ? ? ? H; induction iseq on H; eauto. Qed.

Section iseq_extra.

  Variables (I X : Type) (R : I → X → X → Prop).

  Fact iseq_app x l y r z : iseq R l x y → iseq R r y z → iseq R (l ∺ r) x z.
  Proof. intros H1 H2; revert H1; induction iseq on H2; simpl; eauto. Qed.

  Local Fact iseq_app_inv_rec x ll z : 
           iseq R ll x z 
         → ∀ r l, ll = l ∺ r 
                → ∃y, iseq R l x y
                    ∧ iseq R r y z.
  Proof.
    intros H; induction iseq on H as l1 y i z H1 IH1 H2.
    + intros [] []; try easy; eauto.
    + intros [ | t' r ] l; simpl.
      * intros <-; eauto.
      * inversion 1; subst t' l1.
        destruct (IH1 r l) as (? & []); eauto.
  Qed.

  Fact iseq_app_inv r x l z : iseq R (l ∺ r) x z → ∃y, iseq R l x y ∧ iseq R r y z.
  Proof. now intro; apply iseq_app_inv_rec with (2 := eq_refl). Qed.

  Fact iseq_middle_inv x r i l z :
         iseq R (l ∹ i ∺ r) x z
       → ∃ y₁ y₂, iseq R l x y₁ ∧ R i y₁ y₂ ∧ iseq R r y₂ z.
  Proof. intros (? & (? & [])%iseq_inv & ?)%iseq_app_inv; eauto. Qed.

  Section iseq_rind.

    Variables (P : list I → X → X → Prop)
              (P_end : ∀x, P ε x x)
              (P_prev : ∀ i x y l z, R i x y → iseq R l y z → P l y z → P ([i] ∺ l) x z).

    Theorem iseq_rind l : ∀ x y, iseq R l x y → P l x y.
    Proof.
      induction l using list_snoc_rect; intros ? ?.
      + intros <-%iseq_inv; auto.
      + intros (? & (? & <-%iseq_inv & ?)%iseq_inv & ?)%iseq_app_inv; eauto.
    Qed.

  End iseq_rind.

  Hint Resolve iseq_app : core.

  Fact iseq_rinv l x y : iseq R l x y ↔ l = ε ∧ x = y ∨ ∃ i z l', l = [i] ∺ l' ∧ R i x z ∧ iseq R l' z y.
  Proof.
    split.
    + revert l x y; apply iseq_rind; eauto.
      right; eexists _, _, _; eauto.
    + intros [ (-> & ->) | (? & ? & ? & -> & ? & ?) ]; eauto.
  Qed.

  Fact iseq_head_equiv x y : (∃l, iseq R l x y) ↔ x = y ∨ ∃ z, (∃l, iseq R l z y) ∧ ∃i, R i x z.
  Proof.
    split.
    + intros (? & [ (_ & <-) | (? & ? & ? & -> & ? & ?) ]%iseq_rinv); [ left | right ]; eauto.
    + intros [ <- | (? & (? & ?) & (? & ?)) ]; eauto.
  Qed.

  Let eR x y := ∃i, R i x y.

  Fact crt_iseq_iff x y : x -[eR]*> y ↔ ∃l, iseq R l x y.
  Proof.
    split.
    + induction 1 as [ ? ? [] | | ? ? ? _ [] _ [] ].
      * eexists [_]; eauto.
      * exists []; auto.
      * eexists (_ ∺ _); eauto.
    + intros (l & Hl).
      induction iseq on Hl.
      * constructor 2.
      * econstructor 3; eauto.
        constructor 1; red; eauto.
  Qed.

End iseq_extra.

Section fin_iseq.

  Variables (I X : Type) (R : I → X → X → Prop).

  Let eR x y := ∃i, R i x y.
  Let eiR x y := ∃l, iseq R l x y.

  Local Fact eiR_eR x y : eiR x y ↔ x = y ∨ ∃ z, eiR z y ∧ eR x z.
  Proof. apply iseq_head_equiv. Qed.

  Theorem fin_iseq : (∀x, fin (eR x)) → ∀x, Acc eR⁻¹ x → fin (eiR x).
  Proof. induction 2 using Fix_F; finite eq (@eiR_eR _). Qed.

End fin_iseq.
