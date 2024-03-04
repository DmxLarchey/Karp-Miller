(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Arith List Relations Utf8 Wellfounded.

From KruskalTrees
  Require Import tactics idx vec list_utils.

From KruskalFinite
  Require Import finite choice decide.

(* One can select either KruskalAfProp or KruskalAfType *)
From KruskalAfProp
  Require Import base notations almost_full.

Require Import crt_extra vec_extra nat_omega iseq itree.

Import ListNotations idx_notations vec_notations af_notations iseq_notations.

Set Implicit Arguments.

(** The proof here is loosely adapted from the SSreflect based
    proof of 
        https://bitbucket.org/mituharu/karpmiller/src/master/ *)

(* Via a reversed notations:
          ε     <~>   []
        l ∹ x   <~>   x::l
        l ∺ m   <~>   m++l
   we see lists in reverse order for better human readability *)

#[local] Hint Constructors iseq : core.

Definition simulation {X} (C R T : rel₂ X) :=
  ∀ x x' y, R x y → C x x' → ∃y', T x' y' ∧ C y y'.

(** 
  Here is a description of the different transition sequences we use 

  We will consider several kinds of markings:
    a) marking: regular Petri nets markings, vector of nat indexed by places
    b) Ωmarking: augmented PN markings, vector of Ωnat indexed by places
    c) Δmarking: pair of (list Ωmarking) and Ωmarking for computing the acceleration

  We consider several kinds of PN transitions sequences :

    a) seq  := iseq pn_trans,  denoted _ =[_]=> _, regular PN transition sequences between markings
    b) Ωseq := iseq pn_Ωtrans, denoted _ =[_]Ω> _, augmented PN transition sequences between Ωmarkings
    c) Δseq := iseq pn_Δtrans, denoted _ =[_]Δ> _, accelerated PN sequences between Δmarkings
    d) iseq Δnext, redundancy free  accelerated PN sequences between Δmarkings *) 

#[local] Reserved Notation "x '-[' t ']->' y" (at level 70, format "x  -[ t ]->  y").
#[local] Reserved Notation "x '-[' t ']Ω>' y" (at level 70, format "x  -[ t ]Ω>  y").

#[local] Reserved Notation "x '=[' l ']=>' y" (at level 70, format "x  =[ l ]=>  y").
#[local] Reserved Notation "x '=[' l ']Ω>' y" (at level 70, format "x  =[ l ]Ω>  y").
#[local] Reserved Notation "x '=[' l ']Δ>' y" (at level 70, format "x  =[ l ]Δ>  y").

#[local] Reserved Notation "u '<' i ']Ω' v" (at level 70, format "u  < i ]Ω  v").

Section Petri_Net.

  (* In Kruskal.finite.finite

       finite (X : Type) := { l : list X | ∀x, x ∈ l }
       fin {X} (P : X → Prop) := { l | ∀x, P x ↔ x ∈ l } *)

  Variables (NbPlaces : nat)             (* a number of places *)
            (TrIdx : Type)               (* a type of indices of transitions *)
            (TrIdx_fin : finite TrIdx)   (* listably/finitely many transitions *)
            .

  Notation place := (idx NbPlaces).

  Notation marking := (vec nat NbPlaces).
  Notation Ωmarking := (vec Ω NbPlaces).

  Implicit Types (lt mt : list TrIdx)
                 (t : TrIdx) 
                 (a b c : marking) 
                 (x y z : Ωmarking).

  (* A decider for P : Prop is a term computationally discriminating 
     between P and ¬P. A type is discrete when there is a decider for
     equality 

     In Kruskal.finite.decide

       decider P := { P } + { ¬ P }.
       discrete X := ∀ x y : X, decider (x = y). *)

  Section discreteness.

    Hint Resolve vec_eq_dec_ext eq_nat_dec Ω_discrete : core.

    Fact marking_discrete : discrete marking.   Proof. eauto. Qed.
    Fact Ωmarking_discrete : discrete Ωmarking. Proof. eauto. Qed.

  End discreteness.

  Hint Resolve marking_discrete Ωmarking_discrete : core.

  Fact le_Ωmarking_dec x y : decider (x ≦Ω⁺ y).
  Proof. decide auto; fin auto; intros; apply le_Ω_dec. Qed.

  Notation "↥ a" := (vec_map (λ n, ⌞n⌟) a) (at level 1, no associativity, format "↥ a").
  Notation "u '+ₘ' v" := (vec_scal plus u v) (at level 50, left associativity).
  Notation "u '-ₘ' v" := (vec_scal minus u v) (at level 50, left associativity).
  Notation "u '+Ω' v" := (vec_scal Ωplus u v) (at level 50, left associativity).
  Notation "u '-Ω' v" := (vec_scal Ωminus u v) (at level 50, left associativity).
  Notation "n '*Ω' v" := (vec_map (Ωscal n) v) (at level 49, right associativity).

  Fact le_marking_inv a b : a ≦⁺ b → { u | b = a +ₘ u }.
  Proof.
    intros H.
    exists (b -ₘ a); vec ext with i.
    generalize (H i); vec rew; tlia.
  Qed.

  Fact le_Ωmarking_inv x y : x ≦Ω⁺ y → { u | y = x +Ω u }.
  Proof.
    intros H.
    exists (y -Ω x); vec ext with i; vec rew.
    rewrite Ωplus_Ωminus; auto.
  Qed.

  Fact le_marking_plus a u : a ≦⁺ a +ₘ u.
  Proof. intro; vec rew; tlia. Qed.

  Fact le_Ωmarking_Ωplus_left x u : x ≦Ω⁺ x +Ω u.
  Proof. intro; vec rew; destruct x⦃i⦄; destruct u⦃i⦄; simpl; auto; tlia. Qed.

  Fact le_Ωmarking_Ωplus_right x u : u ≦Ω⁺ x +Ω u.
  Proof. intro; vec rew; destruct x⦃i⦄; destruct u⦃i⦄; simpl; auto; tlia. Qed.

  Hint Resolve le_marking_plus le_Ωmarking_Ωplus_left le_Ωmarking_Ωplus_right : core.

  (* Description of a Petri net via its pre/post transitions *)
  Variables (pre post : TrIdx → marking).

  (* A generic nat/Ω Petri net transition *)
  Inductive pn_trans_gen {X} (ψ : X → marking → X) (t : TrIdx) : X → X → Prop :=
    | pn_tg_cons u : pn_trans_gen ψ t (ψ u (pre t)) (ψ u (post t)).

  Fact pn_trans_intro X ψ t u s d : 
     s = ψ u (pre t) → d = ψ u (post t) → @pn_trans_gen X ψ t s d.
  Proof. intros -> ->; constructor. Qed.

  Fact pn_trans_inv X ψ t s d : 
     @pn_trans_gen X ψ t s d → ∃u, s = ψ u (pre t) ∧ d = ψ u (post t).
  Proof. intros []; eauto. Qed.

  Definition pn_trans  := pn_trans_gen (λ u v, u +ₘ v).
  Definition pn_Ωtrans := pn_trans_gen (λ u v, u +Ω ↥v).

  Notation "x -[ t ]-> y" := (pn_trans t x y).
  Notation "x -[ t ]Ω> y" := (pn_Ωtrans t x y).

  Fact pn_trans_Ωtrans a t b : a -[t]-> b → ↥a -[t]Ω> ↥b.
  Proof. intros [ u ]; apply pn_trans_intro with ↥u; vec ext; vec rew; auto. Qed.

  Fact pn_Ωtrans_trans a t y : ↥a -[t]Ω> y → ∃b, a -[t]-> b ∧ y = ↥b.
  Proof.
    intros (u & H1 & H2)%pn_trans_inv.
    exists (vec_set (fun i => a⦃i⦄-(pre t)⦃i⦄+(post t)⦃i⦄)); split.
    + apply pn_trans_intro with (vec_set (fun i => a⦃i⦄-(pre t)⦃i⦄)).
      * vec ext with i.
        apply f_equal with (f := fun v => v⦃i⦄) in H1.
        revert H1; vec rew.
        destruct u⦃i⦄; simpl; try easy.
        inversion 1; tlia.
      * now vec ext; vec rew.
    + rewrite H2.
      vec ext with i; vec rew.
      apply f_equal with (f := fun v => v⦃i⦄) in H1.
      revert H1; vec rew.
      destruct u⦃i⦄; simpl; try easy.
      inversion 1; f_equal; tlia.
  Qed.

  Fact pn_trans_plus a t b u : a -[t]-> b → a +ₘ u -[t]-> b +ₘ u.
  Proof. intros [ v ]; apply pn_trans_intro with (v +ₘ u); vec ext with i; vec rew; tlia. Qed.

  Fact pn_Ωtrans_Ωplus x t y u : x -[t]Ω> y → x +Ω u -[t]Ω> y +Ω u.
  Proof.
    intros [ v ]; apply pn_trans_intro with (v +Ω u); vec ext with i; vec rew;
      rewrite !Ωplus_assoc; f_equal; apply Ωplus_comm.
  Qed.

  Hint Resolve pn_trans_plus pn_Ωtrans_Ωplus : core.

  Fact pn_trans_simul t : simulation (λ u v, u ≦⁺ v) (pn_trans t) (pn_trans t).
  Proof. intros ? ? ? ? (? & ->)%le_marking_inv; eauto. Qed.

  Fact pn_Ωtrans_simul t : simulation (λ u v, u ≦Ω⁺ v) (pn_Ωtrans t) (pn_Ωtrans t).
  Proof. intros ? ? ? ? (? & ->)%le_Ωmarking_inv; eauto. Qed.

  Fact pn_Ωtrans_eq x t y : x -[t]Ω> y → x ~Ω⁺ y.
  Proof. intros [ c ] i; simpl; vec rew; now destruct c⦃i⦄. Qed.

  Fact pn_Ωtrans_top x t y : x -[t]Ω> y → x ⊑Ω⁺ y.
  Proof. now intros ?%pn_Ωtrans_eq ?; apply eq_top_Ω. Qed.

  (* But we can get MORE (cf nextmc_seq_ucompat_strict) *)
  Corollary pn_Ωtrans_simul_strict x x' t y : 
           x -[t]Ω> y
         → x ≦Ω⁺ x' 
         → ∃y', x' -[t]Ω> y'
              ∧ y ≦Ω⁺ y' 
              ∧ ∀i, x⦃i⦄ <Ω x'⦃i⦄ → y⦃i⦄ <Ω y'⦃i⦄.
  Proof.
    intros H (u & ->)%le_Ωmarking_inv.
    exists (y +Ω u); rsplit 2; auto.
    apply pn_Ωtrans_eq in H.
    intro i; generalize (H i); vec rew. 
    destruct y⦃i⦄; destruct u⦃i⦄; destruct x⦃i⦄; simpl; auto; tlia.
  Qed.

  (* the PN transition x -[t]Ω> _ has finite direct image:
       - singleton if ↥(pre t) ≦Ω⁺ x
       - empty otherwise *)
  Lemma fin_pn_Ωtrans x t : fin (λ y, x -[t]Ω> y).
  Proof.
    destruct (le_Ωmarking_dec ↥(pre t) x) as [ H | H ].
    + exists [x -Ω ↥(pre t) +Ω ↥(post t)].
      intros z; split. 
      * intros [ u ]; left.
        vec ext with i; vec rew.
        now rewrite  Ωminus_Ωplus.
      * intros [ <- | [] ].
        apply pn_trans_intro with (x -Ω ↥(pre t)); auto.
        vec ext with i; generalize (H i); vec rew.
        intro; now rewrite Ωplus_comm, Ωplus_Ωminus.
    + exists ε; split; simpl; try tauto.
      intros (u & ? & ?)%pn_trans_inv; apply H; subst; auto.
  Qed.

  Definition seq : list TrIdx → marking → marking → Prop :=
    iseq pn_trans.

  Notation "x =[ lt ]=> y" := (seq lt x y).

  Tactic Notation "induction" "seq" "on" hyp(H) "as"
      simple_intropattern(l) 
      simple_intropattern(x)
      simple_intropattern(t) 
      simple_intropattern(y)
      simple_intropattern(H1) 
      simple_intropattern(IH1)
      simple_intropattern(H2) :=
    unfold seq in H |- *; induction iseq on H as l x t y H1 IH1 H2.

  Tactic Notation "induction" "seq" "on" hyp(H) := 
    induction seq on H as ? ? ? ? ? ? ?. 

  Definition pn_reacheable a b := ∃ lt, a =[lt]=> b.
  Definition pn_coverable s a := ∃b, pn_reacheable s b ∧ a ≦⁺ b.

  Hint Resolve pn_trans_plus : core.

  Fact seq_plus a lt b u : a =[lt]=> b → a +ₘ u =[lt]=> b +ₘ u.
  Proof. intros H; induction seq on H; eauto. Qed.

  Fact seq_simul lt : simulation (λ a b, a ≦⁺ b) (seq lt) (seq lt).
  Proof.
    intros a a' b H (u & ->)%le_marking_inv.
    exists (b +ₘ u); split.
    + now apply seq_plus.
    + auto.
  Qed.

  Definition Ωseq : list TrIdx → Ωmarking → Ωmarking → Prop :=
    iseq pn_Ωtrans.

  Notation "x =[ lt ]Ω> y" := (Ωseq lt x y).

  Tactic Notation "induction" "Ωseq" "on" hyp(H) "as"
      simple_intropattern(l) 
      simple_intropattern(x)
      simple_intropattern(t) 
      simple_intropattern(y)
      simple_intropattern(H1) 
      simple_intropattern(IH1)
      simple_intropattern(H2) :=
    unfold Ωseq in H |- *; induction iseq on H as l x t y H1 IH1 H2.

  Tactic Notation "induction" "Ωseq" "on" hyp(H) := 
    induction Ωseq on H as ? ? ? ? ? ? ?. 

  Fact seq_Ωseq a lt b : a =[lt]=> b → ↥a =[lt]Ω> ↥b.
  Proof. unfold Ωseq; intros H; induction seq on H as ? ? ? ? _ ? ?%pn_trans_Ωtrans; eauto. Qed. 

  Fact Ωseq_seq a lt y : ↥a =[lt]Ω> y → ∃b, a =[lt]=> b ∧ y = ↥b.
  Proof.
    unfold seq; intros H; induction Ωseq on H
      as lt y t z H1 (d & H2 & ->) (e & H3 & ->)%pn_Ωtrans_trans;
      [ exists a | exists e ]; split; eauto.
  Qed.

  Fact Ωseq_concat x lt y mt z : x =[lt]Ω> y → y =[mt]Ω> z → x =[lt ∺ mt]Ω> z.
  Proof. apply iseq_app. Qed.

  Hint Resolve pn_Ωtrans_Ωplus : core.

  Lemma Ωseq_Ωplus x lt y u : x =[lt]Ω> y → x +Ω u =[lt]Ω> y +Ω u.
  Proof. intros H; induction Ωseq on H; eauto. Qed.

  Fact Ωseq_eq x lt y : x =[lt]Ω> y → x ~Ω⁺ y.
  Proof.
    intros H; induction Ωseq on H as l y t z H1 IH1 H2.
    + intro; apply eq_Ω_refl.
    + intros i; apply eq_Ω_trans with (1 := IH1 i).
      now apply pn_Ωtrans_eq in H2.
  Qed.

  Fact Ωseq_top x lt y : x =[lt]Ω> y → x ⊑Ω⁺ y.
  Proof. now intros ?%Ωseq_eq; auto. Qed.

  (* Simulation of PN on Ωmarkings *) 
  Fact Ωseq_simul lt : simulation (λ x y, x ≦Ω⁺ y) (Ωseq lt) (Ωseq lt).
  Proof.
    intros x x' y H (u & ->)%le_Ωmarking_inv.
    exists (y +Ω u); split.
    + now apply Ωseq_Ωplus.
    + auto.
  Qed.

  (* But we can get MORE: nextmc_seq_ucompat_strict *)
  Corollary Ωseq_simul_strict lt x x' y : 
           x =[lt]Ω> y
         → x ≦Ω⁺ x' 
         → ∃y', x' =[lt]Ω> y'
              ∧ y ≦Ω⁺ y' 
              ∧ ∀i, x⦃i⦄ <Ω x'⦃i⦄ → y⦃i⦄ <Ω y'⦃i⦄.
  Proof.
    intros H (u & ->)%le_Ωmarking_inv.
    exists (y +Ω u); rsplit 2.
    + now apply Ωseq_Ωplus.
    + intro; vec rew.
      destruct y⦃i⦄; destruct u⦃i⦄; simpl; auto; tlia.
    + intros i; generalize (Ωseq_eq H i); vec rew.
      destruct x⦃i⦄; destruct y⦃i⦄; destruct u⦃i⦄; simpl; auto; tlia.
  Qed.

  (* nextmc_seq_loop_ucompat *)
  Corollary Ωseq_loop x x' lt y :
           x =[lt]Ω> y
         → x ≦Ω⁺ x'
         → x ≦Ω⁺ y
         → ∃y', x' =[lt]Ω> y'
              ∧ x' ≦Ω⁺ y'
              ∧ y  ≦Ω⁺ y'.
  Proof.
    intros H1 (u & ->)%le_Ωmarking_inv H2.
    exists (y +Ω u); rsplit 2.
    + now apply Ωseq_Ωplus.
    + intros i; generalize (H2 i); vec rew.
      destruct y⦃i⦄; destruct u⦃i⦄; destruct x⦃i⦄; simpl; auto; tlia.
    + intro; vec rew.
      destruct y⦃i⦄; destruct u⦃i⦄; simpl; auto; tlia.
  Qed.

  (* Below mt = lt ∺ ... ∺ lt where l is repeated n times *)
  Lemma Ωseq_repeat x lt u : x =[lt]Ω> x +Ω u → ∀n, ∃mt, x =[mt]Ω> x +Ω n *Ω u.
  Proof.
    intros H1 n; revert x lt u H1.
    induction n as [ | n IHn ]; intros s l u H1.
    + exists ε.
      replace (s +Ω 0 *Ω u) with s.
      * constructor.
      * vec ext with i; vec rew.
        now rewrite Ωscal_0, Ωplus_comm, Ωplus_0.
    + generalize (Ωseq_Ωplus u H1); intros (m & Hm)%IHn.
      exists (l ∺ m).
      generalize (Ωseq_concat H1 Hm); intros G. 
      eq goal G; f_equal.
      vec ext with i; vec rew.
      now rewrite Ωplus_assoc, Ωscal_S.
  Qed.

  (* If there is a Ωseq from x to y and y is an upper bound of x,
     then there is an Ωseq from x to another upper bound of y which
     is moreover arbitrary large on every component
     where y exceeds x strictly. *)
  Corollary Ωseq_uniform_unbounded x lt y : 
           x =[lt]Ω> y
         → x ≦Ω⁺ y 
         → ∀n, ∃mt y', x =[mt]Ω> y'
                     ∧ x ≦Ω⁺ y' 
                     ∧ ∀i, x⦃i⦄ <Ω y⦃i⦄ → ⌞n⌟ ≦Ω y'⦃i⦄.
  Proof.
    intros H1 (u & ->)%le_Ωmarking_inv n.
    destruct Ωseq_repeat with (1 := H1) (n := n) as (mt & Hmt).
    exists mt, (x +Ω n *Ω u); rsplit 2; auto.
    intros i; vec rew.
    generalize x⦃i⦄ u⦃i⦄; intros [] [ui|]; simpl; try easy.
    + intro; replace ui with (S (ui-1)) by tlia.
      rewrite Nat.mul_comm; simpl.
      generalize ((ui-1)*n); tlia.
    + destruct n; tlia.
  Qed.

  Definition Ωmarking_cover_at i x y := x ≦Ω⁺ y ∧ x⦃i⦄ <Ω y⦃i⦄.

  Notation "u < i ]Ω v" := (Ωmarking_cover_at i u v).

  Local Fact Ωmarking_cover_at_dec i x y : decider (x <i]Ω y).
  Proof.
    decide auto; fin auto.
    + intros; apply le_Ω_dec.
    + apply lt_Ω_dec.
  Qed.

  (* If there is a Ωseq from x to y and y is a strict upper bound of x at i
     then one can reach some upper bound of x arbitrary large at i *)
  Corollary Ωseq_unbounded x lt y i : 
          x =[lt]Ω> y
        → x <i]Ω y 
        → ∀n, ∃mt y', x =[mt]Ω> y'
                    ∧   x ≦Ω⁺ y' 
                    ∧ ⌞n⌟ ≦Ω y'⦃i⦄.
  Proof.
    intros H1 (H2 & H3) n.
    destruct (Ωseq_uniform_unbounded H1 H2 n) as (mt & d' & ? & ? & ?).
    exists mt, d'; auto.
  Qed.

  Hint Resolve Ωseq_concat : core.

  Section consolidate.

    (* We proceed inductivelly on a list of places, knowing
       that the list (idx_list NbPlaces) collects them all *)

    Variables (x s : Ωmarking) (Hxs : ∀i, ∃ lt y, s =[lt]Ω> y ∧ s ≦Ω⁺ y ∧ x⦃i⦄ ≦Ω y⦃i⦄).

    Local Lemma Ωseq_loop_consolidate_rec lidx :
      ∃ lt y, s =[lt]Ω> y ∧ s ≦Ω⁺ y ∧ Forall (λ i, x⦃i⦄ ≦Ω y⦃i⦄) lidx.
    Proof.
      induction lidx as [ | i lidx (l & d & H1 & H2 & H3) ].
      + exists ε, s; rsplit 2.
        * constructor.
        * intro; apply le_Ω_refl.
        * constructor.
      + destruct (Hxs i) as (l' & d' & F1 & F2 & F3).
        destruct Ωseq_loop with (1 := F1) (2 := H2) (3 := F2)
          as (d'' & U1 & U2 & U3).
        exists (l ∺ l'), d''; rsplit 2; eauto.
        constructor.
        - apply le_Ω_trans with (1 := F3), U3.
        - revert H3; apply Forall_impl.
          intros z H; apply le_Ω_trans with (1 := H), U2.
    Qed.

    (* nextmc_seq_loop_consolidate *)
    Theorem Ωseq_loop_consolidate : ∃ lt y, s =[lt]Ω> y ∧ s ≦Ω⁺ y ∧ x ≦Ω⁺ y.
    Proof.
      destruct Ωseq_loop_consolidate_rec 
        with (lidx := idx_list NbPlaces)
        as (l & d & H1 & H2 & H3).
      exists l, d; rsplit 2; auto.
      rewrite Forall_forall in H3.
      intro; apply H3, idx_list_In.
    Qed.

  End consolidate.

  (* The Δccel(eration) at place/index i *)

  Definition Δccel_at (l : list Ωmarking) x i u :=
        (u = ω    ∧  ∃z, z ∈ l ∧ z <i]Ω x)
      ∨ (u = x⦃i⦄ ∧ ~ ∃z, z ∈ l ∧ z <i]Ω x).

  Section Δccel_at_ind.

    (* A more convenient eliminator for "Δccel_at l s i a" 
       used in the proof of Δseq_trans_cover_sound *)

    Variables (l : list Ωmarking) (x : Ωmarking) (i : place) 
              (P : rel₁ Ω)
              (HP1 : ∀n, (∀z, z ∈ l → z <i]Ω x → False) → x⦃i⦄ = ⌞n⌟ → P ⌞n⌟)
              (HP2 : ∀ n z, z ∈ l → z <i]Ω x → x⦃i⦄ = ⌞n⌟ → P ω)
              (HP3 : x⦃i⦄ = ω → P ω).

    Theorem Δccel_at_ind u : Δccel_at l x i u → P u.
    Proof. intros [ (-> & ? & ? & ?) | (-> & ?) ]; case_eq x⦃i⦄; eauto. Qed.

  End Δccel_at_ind.

  Local Fact Δccel_cond_dec l x i : decider (∃m, m ∈ l ∧ m <i]Ω x).
  Proof. 
    destruct fin_choice_t 
      with (F := fun z => z ∈ l) 
           (Q := fun z => z <i]Ω x) 
           (P := fun z => ~ z <i]Ω x) 
      as [ | (m & Hm) ]; fin eauto.
    + intros m _; generalize (Ωmarking_cover_at_dec i m x); intros []; auto.
    + right; firstorder.
  Qed.

  Fact Δccel_at_exists l x i : { r | Δccel_at l x i r }.
  Proof.
    destruct (Δccel_cond_dec l x i).
    + exists ω; left; auto.
    + exists x⦃i⦄; right; auto.
  Qed.

  Fact Δccel_at_uniq l x i r₁ r₂ : Δccel_at l x i r₁ → Δccel_at l x i r₂ → r₁ = r₂.
  Proof. intros [ (-> & ?) | (-> & ?) ] [ (-> & ?) | (-> & ?) ]; tauto. Qed.

  (* Δccel(eration) at every place *)
  Definition Δccel l x y := ∀i, Δccel_at l x i y⦃i⦄.

  (* Δccel is a total computable (functional) relation 
     hence with finite (singleton) direct image) *)

  Fact Δccel_exists l x : { y | Δccel l x y }.
  Proof. apply vec_reif_t, Δccel_at_exists. Qed.

  Fact Δccel_uniq l x y₁ y₂ : Δccel l x y₁ → Δccel l x y₂ → y₁ = y₂.
  Proof.
    intros E1 E2; vec ext with i.
    eapply Δccel_at_uniq; eauto.
  Qed.

  Fact fin_Δccel l x : fin (Δccel l x).
  Proof. 
    apply fin_function_rel.
    + apply Δccel_exists.
    + apply Δccel_uniq.
  Qed.

  Fact Δccel_le l x y : Δccel l x y → x ≦Ω⁺ y.
  Proof.
    intros H i.
    destruct (H i) as [ (-> & _) | (-> & _) ];
      destruct x⦃i⦄; simpl; auto.
  Qed.

  Fact Δccel_top l x y : Δccel l x y → x ⊑Ω⁺ y.
  Proof. intros H%Δccel_le; eauto. Qed.

  Definition Δmarking := (list Ωmarking * Ωmarking)%type.

  Fact Δmarking_discrete : discrete Δmarking.
  Proof. decide equality; apply list_eq_dec; auto. Qed.

  (* An Δccel(lerated) transition is a PN transition followed by an Δccel(eration) *)
  Definition pn_Δtrans t '(l,x) '(m,a) :=
    m = l ∹ x ∧ ∃y, x -[t]Ω> y ∧ Δccel m y a.

  Fact fin_pn_Δtrans t : ∀lx, fin (pn_Δtrans t lx).
  Proof.
    intros (l,x).
    finite as (fun p => l ∹ x= fst p ∧ ∃y, Δccel (l ∹ x) y (snd p) ∧ x -[t]Ω> y).
    1: intros []; unfold pn_Δtrans; simpl; split; intros (? & ? & ? & ?); subst; eauto.
    apply fin_product with (P := fun u => _ = u) (Q := fun v => ∃_, _ _ v ∧ _); fin auto.
    finite compose.
    + intros; apply fin_Δccel.
    + apply fin_pn_Ωtrans.
  Qed. 

  Fact Δseq_trans_top_Ω t l x m y : pn_Δtrans t (l,x) (m,y) → m = l ∹ x ∧ x ⊑Ω⁺ y.
  Proof. intros (? & ? & ?%pn_Ωtrans_top & ?%Δccel_top); eauto. Qed.

  (* The next element of a sequence is added after one PN transition from
     the last element, followed by an acceleration of using the elements of the sequence *) 
  Definition Δseq : list TrIdx → Δmarking → Δmarking → Prop :=
    iseq pn_Δtrans.

  Notation "lx =[ lt ]Δ> ly" := (Δseq lt lx ly).

  Fact Δseq_app lx lt ly mt lz : lx =[lt]Δ> ly → ly =[mt]Δ> lz → lx =[lt ∺ mt]Δ> lz.
  Proof. apply iseq_app. Qed.

  Hint Resolve Δseq_app : core.

  Section Δseq_ind.

    (* An alternate eliminator for Δseq s₀ _ (_,_),
       ie where the third argument is already decomposed *)

    Variables (s₀ : Δmarking)
              (P : list TrIdx → list Ωmarking → Ωmarking → Prop)
              (HP1 : P ε (fst s₀) (snd s₀))
              (HP2 : ∀ lt ax x t y z, s₀ =[lt]Δ> (ax,x) 
                                    → P lt ax x 
                                    → x -[t]Ω> y 
                                    → Δccel (ax ∹ x) y z 
                                    → P (lt ∹ t) (ax ∹ x) z).

    Theorem Δseq_ind lt ax x : s₀ =[lt]Δ> (ax,x) → P lt ax x.
    Proof.
      set (p := (ax,x)); change (s₀ =[lt]Δ> p → P lt (fst p) (snd p)).
      generalize p; clear p; intros p.
      unfold Δseq; intros H; induction iseq on H 
        as ? [] ? [] ? ? (-> & ? & ? & ?); simpl; eauto.
    Qed.

  End Δseq_ind.

  (* The regular tactic "induction ... using Δseq_ind" does 
     not work with the scheme Δseq_ind unfortunately,
     so we implement a tailored induction tactic *)

  Tactic Notation "induction" "Δseq" "on" hyp(H) :=
    match type of H with
    | _ =[?lt]Δ> (?m,?y) => pattern lt, m, y; revert lt m y H; apply Δseq_ind; [ | intros lt m y ]
    end.

  Fact Δseq_app_inv l x lt m y : (l,x) =[lt]Δ> (m,y) → ∃l', m ∹ y = l ∹ x ∺ l'.
  Proof.
    intros H; induction Δseq on H.
    + exists ε; auto.
    + intros t z k H1 (r & H2) _ _.
      exists (r ∹ k); simpl; f_equal; auto.
  Qed.

  Lemma Δseq_split x lt l y z :
        (ε,x) =[lt]Δ> (l,y) 
      → z ∈ l ∹ y
      → ∃ lt₁ lt₂ m, lt = lt₁ ∺ lt₂
                   ∧ (ε,x) =[lt₁]Δ> (m,z)
                   ∧ (m,z) =[lt₂]Δ> (l,y).
  Proof.
    intros H [ <- | Hz ].
    + exists lt, ε, l; rsplit 2; eauto; red; eauto.
    + revert Hz; induction Δseq on H; simpl; try easy.
      intros t v a H1 IH1 H2 H3 [ <- | Hl ].
      * exists lt, [t], l; rsplit 2; auto.
        constructor 2 with (l,y); try red; eauto.
      * destruct (IH1 Hl) as (lt1 & lt2 & m & -> & H4 & H5).
        exists lt1, (lt2 ∹ t), m; rsplit 2; eauto.
        constructor 2 with (1 := H5); red; eauto.
  Qed.

  (* Δseq are ⊑Ω⁺-increasing *)
  Fact Δseq_top_Ω x lt m y : (ε,x) =[lt]Δ> (m,y) → ∀z, z ∈ m → z ⊑Ω⁺ y.
  Proof.
    intros H; apply Forall_forall.
    induction Δseq on H; simpl; auto.
    intros t z a H1 IH1 H2%pn_Ωtrans_top H3%Δccel_top.
    constructor; eauto.
    revert IH1; apply Forall_impl; eauto.
  Qed.

  Hint Resolve in_eq in_cons : core.

  (* nextma_seq_simulatable but with more information about the increase *)
  Lemma Δseq_Ωseq_Ωplus lx lt ly u :
    lx =[lt]Δ> ly → snd ly ⊑Ω⁺ snd lx +Ω u → ∃ mt, snd lx +Ω u =[mt]Ω> (snd ly +Ω u).
  Proof.
    unfold Δseq.
    intros H; induction iseq on H 
      as lt (m,y) t (k,z) H1 IH1 (-> & q & H0 & H2); intros Hy.
    + exists ε; constructor.
    + destruct IH1 as (mt & Gmt).
      * intro; simpl.
        now apply top_Ω_trans with (1 := pn_Ωtrans_top H0 _),
                  top_Ω_trans with (1 := Δccel_top H2 _).
      * apply pn_Ωtrans_Ωplus with (u := u) in H0.
        exists (mt ∹ t).
        constructor 2 with (1 := Gmt).
        eq goal H0; f_equal; simpl.
        vec ext with j; vec rew.
        destruct (H2 j) as [ (Hi & s & F1 & F2 & F3) | (-> & _) ]; auto.
        apply Ωseq_top in Gmt. 
        apply pn_Ωtrans_top in H0.
        destruct lx as (l,x).
        simpl snd in *.
        generalize (Hy j) (Gmt j) (H0 j); vec rew.
        rewrite Hi.
        do 3 intros ->%top_Ω_ω_linv; auto.
  Qed.

  (* nextma_seq_simulatable as an easy corollary *)
  Corollary Δseq_Ωseq_simul l x lt m y x' :
          (l,x) =[lt]Δ> (m,y)
        → x ≦Ω⁺ x'
        → y ⊑Ω⁺ x'
        → ∃ mt y', x' =[mt]Ω> y' 
                 ∧ y ≦Ω⁺ y'.
  Proof.
    intros H1 (u & ->)%le_Ωmarking_inv H2.
    destruct Δseq_Ωseq_Ωplus 
      with (1 := H1) (2 := H2); eauto.
  Qed.

  (* nextma_seq_loop_simulatable *)
  Lemma Δseq_Ωseq_loop_simul l x lt m y t z x' i :
          (l,x) =[lt]Δ> (m,y)
        → y -[t]Ω> z
        → x <i]Ω z
        → x ≦Ω⁺ x'
        → y ⊑Ω⁺ x'
        → x'⦃i⦄ = ω
        ∨ ∃ mt z', x' =[mt]Ω> z'
                 ∧ x' <i]Ω z'.
  Proof.
    intros H1 H2 (H3 & H4) (u & ->)%le_Ωmarking_inv H5.
    destruct Δseq_Ωseq_Ωplus 
      with (1 := H1) (2 := H5)
      as (mt & Hmt).
    apply pn_Ωtrans_Ωplus with (u := u) in H2.
    case_eq (x +Ω u)⦃i⦄; auto; intros n Hn; right.
    exists (mt ∹ t), (z +Ω u); rsplit 2; auto.
    + econstructor; eauto.
    + intro j; vec rew; apply plus_le_Ω_compat; auto; apply le_Ω_refl.
    + generalize (H3 i); revert H4 Hn; vec rew.
      destruct x⦃i⦄; destruct z⦃i⦄; destruct u⦃i⦄; simpl; auto; try easy; tlia.
  Qed.

  (* This is quite an important property, looking at PN transitions
     the other way arround *)
  Lemma pn_Ωtrans_cover_sound x t y c :
           x -[t]Ω> y 
         → ↥c ≦Ω⁺ y 
         → ∃ a b, a -[t]-> b 
                ∧ ↥a ≦Ω⁺ x 
                ∧ ↥b ≦Ω⁺ y 
                ∧ ↥c ≦Ω⁺ ↥b.
  Proof.
    intros (u & H1 & H2)%pn_trans_inv H3.
    set (k1 := vec_set (fun i => c⦃i⦄ - (post t)⦃i⦄ + (pre t)⦃i⦄)). 
    set (k2 := vec_set (fun i => k1⦃i⦄ - (pre t)⦃i⦄ + (post t)⦃i⦄)). 
    exists k1, k2; rsplit 3.
    + apply pn_trans_intro with (vec_set (fun i => c⦃i⦄ - (post t)⦃i⦄)).
      * unfold k1; vec ext; vec rew; auto.
      * unfold k2, k1; vec ext with i; vec rew; auto; tlia.
    + revert H3; rewrite H1, H2; unfold k1. 
      intros H3 i; generalize (H3 i); vec rew.
      destruct u⦃i⦄; simpl; auto; tlia.
    + revert H3; rewrite H2; unfold k2, k1. 
      intros H3 i; generalize (H3 i); vec rew.
      destruct u⦃i⦄; simpl; auto; tlia.
    + intros i.
      unfold k2, k1; vec rew; simpl; tlia.
  Qed.

  Fact pn_trans_pn_Ωtrans a t b x y :
         a -[t]-> b
       → x -[t]Ω> y
       → ↥a ≦Ω⁺ x
       → ↥b ≦Ω⁺ y.
  Proof.
    intros [ u ] [ v ] H i.
    generalize (H i); vec rew.
    destruct v⦃i⦄; simpl; auto; tlia.
  Qed.

  Lemma Ωseq_cover_sound x lt y d : 
         x =[lt]Ω> y
       → ↥d ≦Ω⁺ y
       → ∃ a mt b, a =[mt]=> b
                 ∧ ↥a ≦Ω⁺ x 
                 ∧ ↥b ≦Ω⁺ y 
                 ∧ ↥d ≦Ω⁺ ↥b.
  Proof.
    intros H; revert d; induction Ωseq on H as l y t z H1 IH1 H2; intros d Hd.
    + exists d, ε, d; rsplit 3; eauto; red; eauto.
    + destruct (pn_Ωtrans_cover_sound _ H2 Hd) as (b & c & G1 & G2 & G3 & G4).
      destruct (IH1 _ G2) as (a & mt & b' & F1 & F2 & F3 & F4).
      destruct pn_trans_simul with (1 := G1) (x' := b')
        as (c' & D1 & D2).
      * intro i; generalize (F4 i); now vec rew.
      * exists a, (mt ∹ t), c'; rsplit 3; auto.
        - constructor 2 with b'; auto.
        - intro; apply (pn_trans_pn_Ωtrans D1 H2 F3).
        - intro; apply le_Ω_trans with (1 := G4 _); vec rew; simpl; auto.
  Qed.

  Local Lemma Δseq_cover_sound_rec a lt l x t y z₁ z₂ :
         (ε,↥a) =[lt]Δ> (l,x)
       → x -[t]Ω> y
       → Δccel (l ∹ x) y z₂ 
       → z₁ ≦Ω⁺ z₂
       → z₁ ⊑Ω⁺ y
       → ∃ mt z₃, y =[mt]Ω> z₃ 
                ∧ y  ≦Ω⁺ z₃ 
                ∧ z₁ ≦Ω⁺ z₃.
  Proof.
    intros H1 H2 H3 H4 H5.
    apply Ωseq_loop_consolidate; intros i.
    generalize (H4 i).
    induction (H3 i) 
      as [ n G1 G2 | n k G1 G2 Hn | G1 ] 
      using Δccel_at_ind; 
      intros G3.
    + exists ε, y; rsplit 2.
      * constructor.
      * intro; apply le_Ω_refl.
      * now rewrite G2.
    + destruct (Δseq_split H1 G1) as (lt1 & lt2 & m & -> & F1 & F2).
      destruct (Δseq_Ωseq_loop_simul F2 H2 G2 (proj1 G2))
        as [ Hy | (mt & d & U1 & U2 & U3) ].
      * now apply pn_Ωtrans_top in H2.
      * now rewrite Hy in Hn.
      * assert (exists n', z₁⦃i⦄ = ⌞n'⌟) as (n' & Hn').
        1:{ specialize (H5 i).
            rewrite Hn in H5.
            destruct z₁⦃i⦄; now eauto. }
        clear G3.
        destruct (Ωseq_unbounded U1 (conj U2 U3) n')
          as (kt & d' & Q1 & Q2 & Q3).
        exists kt, d'; rsplit 2; auto.
        now rewrite Hn'.
    + exists ε, y; rsplit 2.
      * constructor.
      * intro; apply le_Ω_refl.
      * now rewrite G1.
  Qed.

  Lemma Δseq_cover_sound a lt l x t y z c :
         (ε,↥a) =[lt]Δ> (l,x)
       → x -[t]Ω> y
       → Δccel (l ∹ x) y z
       → ↥c ≦Ω⁺ z
       → ∃ b mt c', b =[mt]=> c' 
                  ∧ ↥b ≦Ω⁺ y 
                  ∧  c ≦⁺ c'.
  Proof.
    intros H1 H2 H3 H4.
    destruct Δseq_cover_sound_rec 
      with (1 := H1) (2 := H2) (3 := H3) (z₁ := ↥c)
      as (m & z' & G1 & G2 & G3); auto.
    + intros i; vec rew; apply top_Ω_left.
    + destruct Ωseq_cover_sound 
        with (1 := G1) (2 := G3)
        as (a' & m' & b' & F1 & F2 & F3 & F4).
      exists a', m', b'; rsplit 2; auto.
      intros i; generalize (F4 i); now vec rew.
  Qed.

  (* This is the main soundness theorem:
     If there is an accelerated sequence
     from ↥a to an upper bound of ↥b then
     b is coverable from a *)
  Theorem Δseq_cover_soundness {a lt l x b} :
         (ε,↥a) =[lt]Δ> (l,x)
       → ↥b ≦Ω⁺ x
       → ∃ mt c, a =[mt]=> c ∧ b ≦⁺ c.
  Proof.
    intros H; revert b; induction Δseq on H; simpl;
      [ | intros t y z H1 IH1 H2 H3 ]; intros e He.
    + exists ε, a; split.
      * constructor 1.
      * intros i; generalize (He i); now vec rew.
    + destruct (Δseq_cover_sound _ _ H1 H2 H3 He)
        as (c & mt & d & G1 & G2 & G3).
      destruct (pn_Ωtrans_cover_sound _ H2 G2)
        as (b & c' & F1 & F2 & F3 & F4).
      destruct (IH1 _ F2) as (mt' & b' & K1 & K2).
      destruct (pn_trans_simul F1 K2) as (c'' & K3 & K4).
      assert (c ≦⁺ c'') as K5.
      1:{ intros i; generalize (F4 i) (K4 i); vec rew; simpl; tlia. }
      destruct (seq_simul G1 K5) as (d' & K6 & K7).
      exists (mt' ∹ t ∺ mt), d'; split; eauto.
      apply iseq_app with c''; eauto.
  Qed.

  (** Completeness *)

  Fact pn_trans_Ωtrans_cover a t b x :
         a -[t]-> b
       → ↥a ≦Ω⁺ x
       → ∃ y, x -[t]Ω> y ∧ ↥b ≦Ω⁺ y.
  Proof.
    intros H1%pn_trans_Ωtrans H2.
    exact (pn_Ωtrans_simul H1 H2).
  Qed.

 (* To terminate, we must avoid redundancies *)
  Definition Δredundant (lx : Δmarking) := good eq (fst lx ∹ snd lx).

  (* The initial Δmarking is not redundant *)
  Fact Δredundant_init_not x : ¬ Δredundant (ε,x).
  Proof. unfold Δredundant; simpl; now rewrite good_sg_inv. Qed.

  Fact Δredundant_cons y l x : Δredundant (l,x) → Δredundant (l∹x,y).
  Proof. constructor 2; auto. Qed. 

  Fact Δredundant_rev y l x : ¬ y ∈ l∹x → Δredundant (l∹x,y) → Δredundant (l,x).
  Proof. 
    unfold Δredundant; simpl fst; simpl snd.
    intros H [ (? & ? & <-) | ]%good_cons_inv; eauto; tauto.
  Qed.

  Fact pn_Δtrans_Δredundant t : ∀ lx ly, pn_Δtrans t lx ly → Δredundant lx → Δredundant ly.
  Proof. intros (l,x) (m,y) (-> & _); constructor 2; auto. Qed.

  Hint Resolve pn_Δtrans_Δredundant : core.
 
  Fact Δseq_Δredundant lt lx ly : lx =[lt]Δ> ly → Δredundant lx → Δredundant ly.
  Proof. unfold Δseq; intros H; induction iseq on H; auto; eauto. Qed.

  Theorem Δseq_cover_completeness_Δredundant a lt b :
         a =[lt]=> b
       → ∃ mt m y, (ε,↥a) =[mt]Δ> (m,y) 
                  ∧ ↥b ≦Ω⁺ y 
                  ∧ ¬ Δredundant (m,y).
  Proof.
    intros H; induction seq on H as lt b t c H1 (mt & m & y & G1 & G2 & G3) H2.
    + exists ε, ε, ↥a; rsplit 2; eauto.
      * red; eauto.
      * apply Δredundant_init_not.
    + destruct (pn_trans_Ωtrans_cover H2 G2)
        as (z & F1 & F2).
      destruct (Δccel_exists (m ∹ y) z)
        as (k & Hk).
      destruct In_dec with (a := k) (l := m ∹ y)
        as [ H | H ]; auto.
      * destruct (Δseq_split G1 H)
          as (lt2 & lt3 & m' & U1 & U2 & U3).
        exists lt2, m', k; rsplit 2; auto.
        - apply Δccel_le in Hk; eauto.
        - contradict G3. 
          revert U3 G3; apply Δseq_Δredundant.
      * exists (mt ∹ t), (m ∹ y), k; rsplit 2; auto.
        - constructor 2 with (m,y); eauto.
          split; eauto.
        - apply Δccel_le in Hk; eauto.
        - contradict G3; revert H G3; apply Δredundant_rev.
  Qed.

  Section Δseq_bound_good.

    (* We want to show that if an Ωseq contains ≤Ω⁺-redundancy (ie re_Ω)
       (which happens to be AF btw) then it contains a duplicated pair.
   
       This is the core reasonning to show that Ωseq are bound to
       contain redundancies *) 

    Lemma pn_Δtrans_re_Ω_eq u l x t y z :
            u ∈ l ∹ x
          → u ⊑Ω⁺ x
          → u ≤Ω⁺ z
          → x -[t]Ω> y
          → Δccel (l ∹ x) y z
          → u = z.
    Proof.
      intros H4 H1 H5 H2 H3.
      vec ext with i.
      assert (u ≤Ω⁺ y) as H7.
      1:{ intros j.
          specialize (H5 j); specialize (H1 j).
          destruct (H3 j) as [ (Ha & _) | (Ha & _) ].
          + apply pn_Ωtrans_top in H2.
            specialize (H2 j).
            rewrite Ha in H5; apply re_Ω_ω_rinv in H5.
            rewrite H5 in H1; apply top_Ω_ω_linv in H1.
            rewrite H1 in H2; apply top_Ω_ω_linv in H2.
            rewrite H5, H2; apply re_Ω_refl.
          + now rewrite <- Ha. }
      destruct (H3 i) as [ (Ha & H) | (Ha & H) ].
      + specialize (H5 i).
        rewrite Ha in H5 |- *.
        now apply re_Ω_ω_rinv in H5 as ->.
      + assert (¬ u⦃i⦄ <Ω y⦃i⦄) as C.
        1:{ contradict H.
            exists u; repeat split; auto.
            intro; apply re_le_Ω, H7. }
        rewrite Ha.
        specialize (H7 i).
        now apply re_Ω_lt_or_eq in H7 as [].
    Qed.

    Variables (x₀ : Ωmarking).

    (* If an accelerated sequence generates a ≤Ω⁺-redundancy
       then it is a duplicate *)
    Theorem Δseq_re_eq lt m y :
      (ε,x₀) =[lt]Δ> (m,y) → ∀z, z ∈ m → z ≤Ω⁺ y → z = y.
    Proof.
      intros H; induction Δseq on H; simpl; try easy.
      intros t z k H1 IH1 H2 H3 u [ <- | Hu ] H4.
      + apply pn_Δtrans_re_Ω_eq with (3 := H4) (4 := H2) (5 := H3); auto.
      + generalize (Δseq_top_Ω H1 _ Hu); intros H5.
        apply pn_Δtrans_re_Ω_eq with (3 := H4) (4 := H2) (5 := H3); auto.
    Qed.

   (* Δseq which are ≤Ω⁺-good contain duplicates *)
    Local Lemma Δseq_good_rec lt lx : 
         good (λ u v, u ≤Ω⁺ v) lx 
       → match lx with 
         | ε     => False
         | l ∹ x => (ε,x₀) =[lt]Δ> (l,x) → Δredundant (l,x)
         end.
    Proof.
      induction 1 as [ y x l H1 H2 | x l H1 IH1 ] in lt |- *; intros H3.
      + generalize (Δseq_re_eq H3 H1 H2); intros; subst y.
        now constructor 1 with x.
      + apply iseq_inv in H3.
        destruct lt as [ | t lt ].
        * now inversion H3; subst.
        * specialize (IH1 lt).
          destruct H3 as ((m,y) & H3 & -> & H4).
          constructor 2; apply IH1; eauto.
    Qed.

    (** And of course, since ≤Ω⁺ is AF, it means redundancies
        are bound to occur in Δseq *)

    (* Termination: Δseq are bound to contain duplicates 
       because they are bound to contain ≤Ω⁺-redundancies *)
    Theorem Δseq_bound_good lt l x : 
          good (λ u v, u ≤Ω⁺ v) (l ∹ x) 
        → (ε,x₀) =[lt]Δ> (l,x) 
        → Δredundant (l,x).
    Proof. apply (@Δseq_good_rec _ (_ ∹ _)). Qed.

  End Δseq_bound_good.

  (* Now we consider iseq Δnext which are non-redundant Δseq *)

  (* The (possible) next Δmarking after a transition, forbidding redundancies *)
  Definition Δnext t '(l,x) '(m,y) := ¬ y ∈ l ∹ x ∧ pn_Δtrans t (l,x) (m,y).

  Hint Resolve fin_pn_Δtrans : core.

  Lemma fin_Δnext t lx : fin (Δnext t lx).
  Proof.
    finite as (fun p => ¬ snd p ∈ fst lx ∹ snd lx ∧ pn_Δtrans t lx p).
    1: revert lx; intros [] []; simpl; tauto.
    finite dec left.
    1: revert lx; intros [] []; simpl fst; simpl snd; decide auto; now apply in_dec.
  Qed.

  (* No new redundancy can be introduced *)
  Fact Δnext_Δredundant_rev t : ∀ lx ly, Δnext t lx ly → Δredundant ly → Δredundant lx.
  Proof. intros (l,x) (m,y) (H1 & -> & _) [ (z & H2 & H3) | H ]%good_cons_inv; auto; simpl in *; subst; tauto. Qed.

  Hint Resolve Δnext_Δredundant_rev : core.

  Fact iseq_Δnext_Δredundant_rev lt lx ly : iseq Δnext lt lx ly → Δredundant ly → Δredundant lx.
  Proof. intros H; induction iseq on H; eauto. Qed.

  (* Comparison between 
       a) iseq Δnext
       b) iseq pn_Δtrans (ie Δseq) 

     They are identical when not redundant *)
  Fact iseq_Δnext_Δseq lt : iseq Δnext lt ⊆₂ Δseq lt.
  Proof. apply iseq_mono; now intros ? [] [] []. Qed.

  Lemma irred_Δseq_iseq_Δnext x lt ly :
    (ε,x) =[lt]Δ> ly → ¬ Δredundant ly → iseq Δnext lt (ε,x) ly.
  Proof.
    destruct ly as (l,y).
    intros H; induction Δseq on H; simpl; eauto.
    intros t m z H1 IH1 H2 H3 H4.
    constructor 2 with (l,y).
    * apply IH1.
      contradict H4; now apply Δredundant_cons.
    * repeat split; eauto.
      contradict H4; constructor 1 with z; auto.
  Qed.

  Local Corollary irred_Δseq_iseq_Δnext_iff x lt ly :
      iseq Δnext lt (ε,x) ly ↔ (ε,x) =[lt]Δ> ly ∧ ¬ Δredundant ly.
  Proof.
     split.
     + intros H; split.
       * revert H; apply iseq_Δnext_Δseq.
       * intros C; apply (@Δredundant_init_not x); revert H C.
         apply iseq_Δnext_Δredundant_rev.
     + intros (H1 & H2); revert H1 H2; apply irred_Δseq_iseq_Δnext.
  Qed.

  (* Soundness and completeness for (iseq Δnext) covering *)

  Theorem iseq_Δnext_cover_soundness a b lt l x :
     iseq Δnext lt (ε,↥a) (l,x) → ↥b ≦Ω⁺ x → ∃ mt c, a =[mt]=> c ∧ b ≦⁺ c.
  Proof. intros H1%iseq_Δnext_Δseq; revert H1; apply Δseq_cover_soundness. Qed.

  Theorem iseq_Δnext_cover_completeness a lt b :
         a =[lt]=> b → ∃ mt l y, iseq Δnext mt (ε,↥a) (l,y) ∧ ↥b ≦Ω⁺ y.
  Proof.
    intros (mt & l & y & H1 & H2 & H3)%Δseq_cover_completeness_Δredundant.
    exists mt, l, y; split; auto.
    apply irred_Δseq_iseq_Δnext; auto.
  Qed.

  Section Δnext_Strongly_Normalizing.

    (* Δnext _ is strongly normalizing *)

    Let Δnext_ lx ly := ∃ t, Δnext t lx ly.

    Fact crt_Δnext__iseq_Δnext lx ly : lx -[Δnext_]*> ly ↔ ∃lt, iseq Δnext lt lx ly.
    Proof. apply crt_iseq_iff. Qed.

    Local Fact Δnext__Δredundant_rev lx ly : Δnext_ lx ly → Δredundant ly → Δredundant lx.
    Proof. intros (t & Ht); revert Ht; apply Δnext_Δredundant_rev. Qed.

    Hint Resolve Δnext__Δredundant_rev : core.

    Local Fact crt_Δnext__Δredundant_rev lx ly : lx -[Δnext_]*> ly → Δredundant ly → Δredundant lx.
    Proof. induction 1; eauto. Qed.

    Local Fact crt_Δnext__Δseq lx ly : lx -[Δnext_]*> ly → ∃ lt, lx =[lt]Δ> ly.
    Proof. 
      intros (lt & H)%crt_Δnext__iseq_Δnext; exists lt; revert H.
      apply iseq_mono; now intros ? [] [] [].
    Qed.

    Fact ct_Δnext__incr l x m y : (l,x) -[Δnext_]+> (m,y) → x ∈ m.
    Proof.
      intros ((k,z) & (lt & (r & E)%Δseq_app_inv)%crt_Δnext__Δseq & _ & t & -> & _)%clos_trans_inv.
      rewrite E; apply in_or_app; auto.
    Qed.

    Local Fact af_re_Ω : af re_Ω.
    Proof. apply af_option, af_le_nat. Qed.

    (** By Dickson's lemma, ≤Ω⁺ is AF on Δmarking *)
    Local Lemma af_re_Δ : af (λ u v : Δmarking, snd u ≤Ω⁺ snd v).
    Proof. 
      generalize (af_vec_fall2 NbPlaces af_re_Ω).
      af rel morph (fun x (y : Δmarking) => x = snd y).
      + eauto.
      + intros ? ? [] []; simpl; intros; subst; auto.
    Qed.

    (* It is enough to show that the initial Δmarking 
       is accessible for Δsucc⁻¹ to be able to compute
       the nodes of the Karp-Miller tree 

       Here we use that ≤Ω⁺ is WQO on Δmarkings *)
    Theorem Δnext_SN x : Acc Δnext_⁻¹ (ε,x).
    Proof.
      apply Acc_from_af with (1 := af_re_Δ).
      intros (l,y) (m,z) H1%clos_trans_rev H2
        H3%clos_refl_trans_rev; simpl in *.
      generalize (clos_trans_refl_trans H1); intros H4.
      generalize (crt_Δnext__Δseq H3) (crt_Δnext__Δredundant_rev H3)
                 (crt_Δnext__Δseq H4) (crt_Δnext__Δredundant_rev H4).
      intros (lt & Hlt) H5 (mt & Hmt) H6.
      eapply Δredundant_init_not, H5, H6.
      apply ct_Δnext__incr in H1.
      apply Δseq_bound_good with x (lt ∺ mt). 
      + now constructor 1 with z.
      + eauto.
    Qed.

  End Δnext_Strongly_Normalizing.

  (* We can conclude with decision procedures of which the 
     termination is ensured by the SN of Δnext *)

  Section deciding_coverability.

    (* The first procedure computes the nodes of the Karp-Miller
       tree but without linking these with accelerated transitions.
       These nodes are enough to decide coverability *)

    Hint Resolve fin_Δnext Δnext_SN : core.

    (* The direct image { (l,y) | (ε,x)) -[Δsucc]*> (l,y) } is finite 
       (and the corresponding list are the nodes of the KM tree) *)
    Lemma km_tree_nodes_fin x : fin (λ ly, ∃lt, iseq Δnext lt (ε,x) ly).
    Proof. apply fin_iseq; fin auto. Qed.

    Variables a b : marking.

    (* We compute the nodes of the KM tree for ↥a *)
    Let KM_nodes := km_tree_nodes_fin ↥a.

    Let lc := proj1_sig KM_nodes.

    (* The nodes of the K tree in lc *)
    Local Fact Hlc ly : (∃lt, iseq Δnext lt (ε,↥a) ly) ↔ ly ∈ lc.
    Proof. apply (proj2_sig KM_nodes). Qed.

    (* b is covered in the KM tree *)
    Let KMcovered := ∃y, y ∈ map snd lc ∧ ↥b ≦Ω⁺ y.

    (* Covering by (some member of the list) lc is decidable *)
    Local Fact KMcovered_dec : decider KMcovered.
    Proof. decide auto; fin auto; intros; apply le_Ωmarking_dec. Qed.

    (* Covering by lc entails coverability *)
    Local Fact KMcovered_coverable : KMcovered → pn_coverable a b.
    Proof.
      intros (c & ((m,d) & H1 & (lt & Hlt)%Hlc)%in_map_iff & H3).
      simpl in *; subst d.
      apply iseq_Δnext_cover_soundness with (2 := H3) in Hlt as (mt & d & G1 & G2).
      exists d; split; auto; exists mt; auto.
    Qed.

    (* Coverability entails covering by lc *)
    Local Fact coverable_KMcovered : pn_coverable a b → KMcovered.
    Proof.
      intros (c & (lt & (mt & l & y & H1 & H2)%iseq_Δnext_cover_completeness) & H3).
      exists y; split.
      + apply in_map_iff.
        exists (l,y); split; auto.
        apply Hlc; eauto.
      + apply le_Ωvec_trans with (2 := H2).
        intro; vec rew; simpl; auto.
    Qed.

    Hint Resolve KMcovered_coverable coverable_KMcovered : core.

    (* The main theorem: decidabiliy of PN coverability *)
    Theorem pn_coverable_dec : decider (pn_coverable a b).
    Proof.
      generalize KMcovered_dec; apply decider_equiv.
      split; auto.
    Qed.

  End deciding_coverability.

  Section Karp_Miller_tree.

    (* The second procedure compute the Karp-Miller tree
       where its edges are decorated with accelerated 
       transitions, hence we get more information *)

    Hint Resolve fin_Δnext : core.

    Local Fact fin_Δnext_pair lx : fin (λ '(t,ly), Δnext t lx ly).
    Proof.
      finite as (fun p => Δnext (fst p) lx (snd p)).
      1: revert lx; intros [] []; simpl; tauto.
      apply finite_dep_prod with (R := fun u v => _ u _ v); auto.
    Qed.

    (* The construction of the Karp Miller tree follows from a generic procedure
       of recovering a tree spanning an indexed transition relation when it is
         1) finitely branching   and    2) well founded at the root *)

    Variable (x₀ : Ωmarking).

    Local Fact km_tree_pwc : { tr : itree TrIdx Δmarking 
                                  | ∀ lt ly, itree_path tr lt (ε,x₀) ly ↔ iseq Δnext lt (ε,x₀) ly }.
    Proof.
      apply itree_span.
      + intros; apply fin_Δnext_pair.
      + apply Acc_incl with (2 := Δnext_SN _).
        intros [] [] (? & []); eexists _; split; eauto.
    Qed.

    (** The Karp Miller Tree *)
    Definition km_tree := proj1_sig km_tree_pwc.

    (** The properties of its nodes *)
    Fact km_tree_spec lt ly : itree_path km_tree lt (ε,x₀) ly ↔ iseq Δnext lt (ε,x₀) ly.
    Proof. apply (proj2_sig km_tree_pwc). Qed.

    (** Its root is (ε,x₀) *)
    Fact km_tree_root : itree_root km_tree = (ε,x₀).
    Proof. apply itree_path_root with [] (ε,x₀), km_tree_spec; constructor. Qed.

    (* For any Ωmarking x, we can either computes a 
         1) a path in the km_tree from the root (ε,x₀) to covering of x 
         2) or else a proof that such path exists in the km_tree *)
    Lemma km_tree_search x : { '(lt,m,y) | x ≦Ω⁺ y ∧ itree_path km_tree lt (ε,x₀) (m,y) } 
                             + { ∀ lt m y, itree_path km_tree lt (ε,x₀) (m,y) → x ≦Ω⁺ y → False }.
    Proof.
      rewrite <- km_tree_root.
      set (covered x (ly : Δmarking) := x ≦Ω⁺ snd ly).
      destruct itree_path_find_dec 
        with (P := covered x) (Q := fun ly => ¬ covered x ly) (t := km_tree)
        as [ ((lt,(m,y)) & H1 & H2) | H ].
      + intros []; apply le_Ωmarking_dec.
      + left; exists (lt,m,y); split; auto.
      + right; intros ? ? ?; apply (H _ (_,_)).
    Qed.
 
  End Karp_Miller_tree.

  (* Then we use the search procedure associated to the KM tree to decide
     for coverability. Notice that this search procedure also completely 
     visits the whole tree, so there is no advantage here compared to the 
     previous procedure using the list of nodes of the KM tree only.

     The only difference here is that we could also output an accelerated
     transition sequence that would lead to the covering. However, if one 
     wants the whole transition sequence to the covering (not only the 
     accelerated one), one would need to keep more information in the 
     soundness theorem above, ie Δseq_cover_soundness. Probably a not 
     very complicated enhancement. *)

  Theorem pn_coverable_km_tree_dec a b : decider (pn_coverable a b).
  Proof.
    destruct (km_tree_search ↥a ↥b) 
      as [ (((lt,m),c) & H1 & H2) | H ].
    + left.
      apply km_tree_spec in H2.
      destruct iseq_Δnext_cover_soundness with (1 := H2) (2 := H1)
        as (mt & d & ? & ?).
      exists d; split; auto; now exists mt.
    + right; intros (d & (lt & H1) & H2).
      apply iseq_Δnext_cover_completeness in H1 as (mt & l & y & H3 & H4).
      apply (H mt l y).
      * now apply km_tree_spec.
      * apply le_Ωvec_trans with (2 := H4).
        intro; vec rew; simpl; auto.
  Qed.

End Petri_Net.

Check km_tree.
Check km_tree_root.
Check pn_coverable_km_tree_dec.

Print pn_coverable.
Check pn_coverable_dec.

  

  
