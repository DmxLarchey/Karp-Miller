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
  Require Import notations tactics vec.

From KruskalFinite
  Require Import decide.

Require Import vec_extra.

Import vec_notations.

Set Implicit Arguments.

(* Ω := ω+1 *)
Definition nat_omega := option nat.
#[global] Notation Ω := nat_omega.

#[global] Notation ω := (None).
#[global] Notation "⌞ n ⌟" := (Some n) (at level 1, format "⌞ n ⌟").

(* Natural strict order on Ω: 0 < 1 < ... < n < ... < ω *)
Definition lt_Ω (x y : Ω) :=
  match x, y with
  | ⌞n⌟, ⌞m⌟ => n < m
  | ⌞n⌟,  ω  => True
  |  _ ,  _  => False
  end.

(* The one compares finite values but the limit ω is single *)
Definition re_Ω (x y : Ω) :=
  match x, y with
  | ⌞n⌟, ⌞m⌟ => n <= m
  |  ω  , ω  => True
  |  _  , _  => False
  end.

(* This the ordinal order on Ω := ω+1 *)
Definition le_Ω (x y : Ω) :=
  match x, y with
  | ⌞n⌟, ⌞m⌟ => n <= m
  |  _  , ω  => True
  |  _  , _  => False
  end.

(* Once at ω, we must stay there *)
Definition top_Ω (x y : Ω) :=
  match y with 
  | ω => True 
  | _ => 
    match x with 
    | ω => False
    | _ => True
    end
  end.

Definition eq_Ω (x y : Ω) :=
  match x, y with 
  |  ω,   ω  => True 
  | ⌞_⌟, ⌞_⌟ => True 
  |  _ ,  _  => False
  end.

Definition Ωplus (x y : Ω) : Ω :=
  match x, y with
  | ⌞a⌟, ⌞b⌟ => ⌞a+b⌟
  |  _ ,  _  => ω
  end.

Definition Ωminus (c x : Ω) :=
  match c, x with
  | ⌞c⌟, ⌞x⌟ => ⌞c-x⌟
  |  _ ,  _  => ω
  end.

Definition Ωscal n (x : Ω) :=
  match x with
  | ⌞x⌟ => ⌞n*x⌟
  |  ω  => match n with 0 => ⌞0⌟ | _ => ω end
  end.

Arguments Ωplus _ _ /.
Arguments Ωminus _ _ /.

#[global] Infix "<Ω" := lt_Ω (at level 70).
#[global] Infix "≤Ω" := re_Ω (at level 70).
#[global] Infix "≦Ω" := le_Ω (at level 70).
#[global] Infix "⊑Ω" := top_Ω (at level 70).
#[global] Infix "~Ω" := eq_Ω (at level 70).

Fact Ω_discrete : discrete Ω.
Proof. do 2 decide equality. Qed.

#[local] Tactic Notation "solve" "Ω" :=
  intros;
  repeat match goal with
  | x : Ω |- _ => destruct x
  end;
  simpl in * |- *;
  f_equal; auto; tlia.

Fact re_Ω_refl :  ∀x, x ≤Ω x.  Proof. solve Ω. Qed.
Fact le_Ω_refl :  ∀x, x ≦Ω x.  Proof. solve Ω. Qed.
Fact top_Ω_refl : ∀x, x ⊑Ω x.  Proof. solve Ω. Qed.
Fact eq_Ω_refl :  ∀x, x ~Ω x.  Proof. solve Ω. Qed.

Fact lt_le_Ω_trans x y z : x <Ω y → y ≦Ω z → x <Ω z.   Proof. solve Ω. Qed.
Fact le_lt_Ω_trans x y z : x ≦Ω y → y <Ω z → x <Ω z.   Proof. solve Ω. Qed.
Fact re_Ω_trans x y z :    x ≤Ω y → y ≤Ω z → x ≤Ω z.   Proof. solve Ω. Qed.
Fact le_Ω_trans x y z :    x ≦Ω y → y ≦Ω z → x ≦Ω z.   Proof. solve Ω. Qed.
Fact top_Ω_trans x y z :   x ⊑Ω y → y ⊑Ω z → x ⊑Ω z.   Proof. solve Ω. Qed.
Fact eq_Ω_trans x y z :    x ~Ω y → y ~Ω z → x ~Ω z.   Proof. solve Ω. Qed.

Fact re_le_Ω :  re_Ω ⊆₂ le_Ω.   Proof. solve Ω. Qed.
Fact le_top_Ω : le_Ω ⊆₂ top_Ω.  Proof. solve Ω. Qed.
Fact eq_top_Ω : eq_Ω ⊆₂ top_Ω.  Proof. solve Ω. Qed.

Fact re_Ω_ω_rinv x : x ≤Ω ω → x = ω.   Proof. solve Ω. Qed.
Fact top_Ω_left n x : ⌞n⌟ ⊑Ω x.        Proof. solve Ω. Qed.
Fact top_Ω_ω_linv x : ω ⊑Ω x → x = ω.  Proof. solve Ω. Qed.

Fact plus_le_Ω_left : ∀ x y, x ≦Ω Ωplus x y.   Proof. solve Ω. Qed.
Fact plus_le_Ω_right : ∀ x y, y ≦Ω Ωplus x y.  Proof. solve Ω. Qed.

Fact plus_le_Ω_compat : ∀ x y x' y', x ≦Ω x' → y ≦Ω y' → Ωplus x y ≦Ω Ωplus x' y'.
Proof. solve Ω. Qed.

Fact re_Ω_lt_or_eq : ∀ x y, x ≤Ω y → { x = y } + { x <Ω y }.
Proof. 
  intros [x|] [y|]; simpl; auto.
  destruct (le_lt_dec y x); [ left | right ]; auto; f_equal; tlia.
Qed.

Fact le_Ω_dec : ∀ x y, decider (x ≦Ω y).
Proof. intros [] []; simpl; auto; apply le_dec. Qed.

Fact lt_Ω_dec : ∀ x y, decider (x <Ω y).
Proof. intros [] []; simpl; auto; apply le_dec. Qed.

Fact lt_Ω_inv x y : 
        x <Ω y 
      → match y with
        | ⌞m⌟ => match x with 
                 | ⌞n⌟ => n < m
                 | _   => False
                 end
        |  ω  => match x with
                 | ⌞_⌟ => True
                 | _   => False
                 end
        end.
Proof. solve Ω. Qed.

Fact top_Ω_choose : ∀ x y, { n | x = ω ∧ y = ⌞n⌟ } + { x ⊑Ω y }.
Proof. intros [] []; simpl; auto; left; eauto. Qed. 

Fact Ωplus_0 : ∀ x, Ωplus ⌞0⌟ x = x.
Proof. solve Ω. Qed.

Fact Ωplus_comm : ∀ x y, Ωplus x y = Ωplus y x.
Proof. solve Ω. Qed.

Fact Ωplus_assoc : ∀ x y z, Ωplus (Ωplus x y) z = Ωplus x (Ωplus y z).
Proof. solve Ω. Qed.

Fact Ωminus_0 : ∀ x, Ωminus x ⌞0⌟ = x.
Proof. solve Ω. Qed.

Fact Ωminus_Ωplus : ∀ x n, Ωminus (Ωplus x ⌞n⌟) ⌞n⌟ = x.
Proof. solve Ω. Qed.

Fact Ωplus_Ωminus : ∀ x y, x ≦Ω y → Ωplus x (Ωminus y x) = y.
Proof. solve Ω. Qed.

Fact Ωscal_0 : ∀ x, Ωscal 0 x = ⌞0⌟.
Proof. solve Ω. Qed.

Fact Ωscal_S : ∀ n x, Ωscal (S n) x = Ωplus x (Ωscal n x).
Proof. solve Ω. Qed.

#[global] Infix "≦⁺"  := (vec_fall2 le) (at level 70).
#[global] Infix "≤Ω⁺" := (vec_fall2 re_Ω) (at level 70).
#[global] Infix "≦Ω⁺" := (vec_fall2 le_Ω) (at level 70).
#[global] Infix "⊑Ω⁺" := (vec_fall2 top_Ω) (at level 70).
#[global] Infix "~Ω⁺" := (vec_fall2 eq_Ω) (at level 70).

#[global] Hint Resolve Nat.le_refl re_Ω_refl le_Ω_refl top_Ω_refl eq_Ω_refl : core.
#[global] Hint Resolve Nat.le_trans re_Ω_trans le_Ω_trans top_Ω_trans eq_Ω_trans : core.

Section vec_relations.

  Tactic Notation "refl" := intro; auto.

  Tactic Notation "trans" :=
    let H1 := fresh in let H2 := fresh in let i := fresh in
    intros H1 H2 i; generalize (H1 i) (H2 i); eauto.

  Variables (n : nat)
            (a b c : vec nat n) 
            (x y z : vec Ω n).

  Fact le_vec_refl : a ≦⁺ a.  Proof. refl. Qed.
  Fact le_vec_trans : a ≦⁺ b → b ≦⁺ c → a ≦⁺ c.  Proof. trans. Qed.

  Fact re_Ωvec_refl :   x ≤Ω⁺ x.  Proof. refl. Qed.
  Fact le_Ωvec_refl :   x ≦Ω⁺ x.  Proof. refl. Qed.
  Fact top_Ωvec_refl :  x ⊑Ω⁺ x.  Proof. refl. Qed.
  Fact eq_Ωvec_refl :   x ~Ω⁺ x.  Proof. refl. Qed.

  Fact re_Ωvec_trans :  x ≤Ω⁺ y → y ≤Ω⁺ z → x ≤Ω⁺ z.  Proof. trans. Qed.
  Fact le_Ωvec_trans :  x ≦Ω⁺ y → y ≦Ω⁺ z → x ≦Ω⁺ z.  Proof. trans. Qed.
  Fact top_Ωvec_trans : x ⊑Ω⁺ y → y ⊑Ω⁺ z → x ⊑Ω⁺ z.  Proof. trans. Qed.
  Fact eq_Ωvec_trans :  x ~Ω⁺ y → y ~Ω⁺ z → x ~Ω⁺ z.  Proof. trans. Qed.

  Fact le_top_Ωvec : x ≦Ω⁺ y → x ⊑Ω⁺ y.
  Proof. apply vec_fall2_mono, le_top_Ω. Qed.

  Fact eq_top_Ωvec : x ~Ω⁺ y → x ⊑Ω⁺ y.
  Proof. apply vec_fall2_mono, eq_top_Ω. Qed.

End vec_relations.

#[global] Hint Resolve 
               le_vec_refl le_vec_trans 
               re_Ωvec_refl re_Ωvec_trans
               le_Ωvec_refl le_Ωvec_trans
               top_Ωvec_refl top_Ωvec_trans
               eq_Ωvec_refl eq_Ωvec_trans
               le_top_Ωvec eq_top_Ωvec
             : core.

