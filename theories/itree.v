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
  Require Import notations list_utils.

From KruskalFinite
  Require Import finite decide.

Require Import iseq.

Import ListNotations iseq_notations.

Set Implicit Arguments.

Fact list_choice_Type_Prop X (P : X → Type) (Q : X → Prop) l:
       (∀x, x ∈ l → P x + Q x)
     → {x & P x & x ∈ l} 
     + (∀x, x ∈ l → Q x).
Proof.
  induction l as [ | x l IHl ]; intros Hl.
  + right; intros _ [].
  + destruct (Hl x) as [ p | q ]; simpl; auto.
    * left; exists x; auto.
    * destruct IHl as [ [ y H1 H2 ] | H ].
      - intros; apply Hl; simpl; auto.
      - left; exists y; auto.
      - right; intros z []; subst; auto.
Qed.

Fact forall_In_sig_pair X Y (R : X → Y → Prop) l : 
         (∀x, x ∈ l → sig (R x)) 
       → { ll | l = map fst ll 
              ∧ ∀ x y, (x,y) ∈ ll → R x y }.
Proof.
  induction l as [ | x l IHl ]; intros Hl.
  + exists nil; now simpl.
  + destruct (Hl x) as (y & Hy); simpl; auto.
    destruct IHl as (ll & H1 & H2).
    1: intros; apply Hl; simpl; auto.
    exists ((x,y)::ll); simpl; split.
    * f_equal; auto.
    * intros ? ? [ H | ]; auto; inversion H; now subst.
Qed.

#[local] Hint Constructors iseq : core.

Section itree.

  Variables (I X : Type).

  Unset Elimination Schemes.

  (* The type of indexed trees, ie branching is indexed by I *)
  Inductive itree := itree_node : X → list (I*itree) → itree.

  Set Elimination Schemes.

  Definition itree_root t :=
    match t with
    | itree_node x _ => x
    end.

  Section itree_rect.

    Let R r t :=
      match t with 
      | itree_node _ lt => ∃ i, (i,r) ∈ lt 
      end.

    Local Fixpoint Acc_R t : Acc R t.
    Proof.
      destruct t as [ x lt ].
      constructor; simpl.
      intros t (i & Hi); revert Hi.
      induction lt as [ | p lt IH ].
      + intros [].
      + intros [ H | H ].
        * specialize (Acc_R (snd p)); subst; trivial.
        * apply IH, H.
    Qed.

    Variables (P : itree → Type)
              (HP : ∀ x lt, (∀ i t, (i,t) ∈ lt → P t) → P (itree_node x lt)).

    Theorem itree_rect t : P t.
    Proof.
      induction (Acc_R t) as [ [ x lt ] IHt ] using Fix_F.
      apply HP.
      intros i t H.
      apply (IHt t).
      now exists i.
    Qed.

  End itree_rect.

  Definition itree_rec (P : _ → Set) := itree_rect P.
  Definition itree_ind (P : _ → Prop) := itree_rect P.

  Section itree_fall.

    Variables (P : X → list (I * itree) → Prop).

    Fixpoint itree_fall t : Prop :=
      match t with
      | itree_node x l => P x l ∧ ∀ h, h ∈ map (fun '(_,t') => itree_fall t') l → h
      end.

    Fixpoint itree_exst t : Prop :=
      match t with
      | itree_node x l => P x l ∨ ∃h, h ∈ map (fun '(_,t') => itree_exst t') l ∧ h
      end.

    Fact itree_fall_fix x l :
      itree_fall (itree_node x l) ↔ P x l ∧ ∀ i t, (i,t) ∈ l → itree_fall t.
    Proof.
      simpl; split; intros [ H1 H2 ]; split; auto.
      + intros y t H; apply H2, in_map_iff; exists (y,t); auto.
      + intros h ((y,t) & <- & ?)%in_map_iff; eauto.
    Qed.

    Fact itree_exst_fix x l :
      itree_exst (itree_node x l) ↔ P x l ∨ ∃ i t, (i,t) ∈ l ∧ itree_exst t.
    Proof.
      simpl; split; intros [ H1 | H2 ]; auto; right.
      + destruct H2 as (h & (((i,t) & <- & H3)%in_map_iff & H2)); eauto.
      + destruct H2 as (i & t & H1 & H2).
        exists (itree_exst t); split; auto.
        apply in_map_iff.
        now exists (i,t).
    Qed.

  End itree_fall.

  Section itree_fall_exst.

    Variables (P Q : X → list (I * itree) → Prop).

    Theorem itree_fall_exst_dec : 
          (∀ x l, {P x l} + {Q x l})
         → ∀t, {itree_fall P t} + {itree_exst Q t}.
    Proof.
      intros PQ_dec. 
      induction t as [ x l IH ].
      destruct (PQ_dec x l) as [ Hxl | Hxl ].
      2: right; apply itree_exst_fix; auto.
      destruct list_choice_t 
        with (l := l) 
             (P := λ p : I*itree, itree_fall P (snd p)) 
             (Q := λ p : I*itree, itree_exst Q (snd p))
        as [ H | ((i,t) & H1 & H2) ].
      + intros []; apply IH.
      + left; apply itree_fall_fix; split; auto.
        intros ? ?; apply (H (_,_)).
      + right; apply itree_exst_fix; right; eauto.
    Qed.

    Fact itree_fall_exst_absurd :
          (∀ x l, P x l → Q x l → False)
         → ∀t, itree_fall P t → itree_exst Q t → False.
    Proof.
      intros HPQ t.
      induction t; rewrite itree_fall_fix, itree_exst_fix.
      intros [] [ | (? & ? & []) ]; eauto.
    Qed.

  End itree_fall_exst.

  Fact itree_exst_dec P : (∀ x l, decider (P x l)) → ∀t, decider (itree_exst P t).
  Proof.
    intros H t.
    destruct itree_fall_exst_dec 
      with (Q := P) (P := λ x l, ~ P x l) (t := t)
      as [ H1 | H1 ]; auto.
    right; red; revert H1; apply itree_fall_exst_absurd; tauto.
  Qed.

  Fact itree_fall_dec P : (∀ x l, decider (P x l)) → ∀t, decider (itree_fall P t).
  Proof.
    intros H t.
    destruct itree_fall_exst_dec 
      with (P := P) (Q := λ x l, ~ P x l) (t := t)
      as [ H1 | H1 ]; auto.
    right; intros H2; revert H2 H1; apply itree_fall_exst_absurd; tauto.
  Qed.

  Definition itree_occurs x := itree_exst (λ y _, x = y).

  Fact itree_occurs_fix x y l : 
         itree_occurs x (itree_node y l) 
       ↔ x = y 
       ∨ ∃ i t, (i,t) ∈ l
              ∧ itree_occurs x t.
  Proof. apply itree_exst_fix. Qed.

  Fact itree_occurs_dec : discrete X → ∀ x t, decider (itree_occurs x t).
  Proof. intros; apply itree_exst_dec; auto. Qed.

  Inductive itree_path : itree → list I → X → X → Prop :=
    | itree_path_nil  x lt : itree_path (itree_node x lt) ε x x 
    | itree_path_cons x i y li z t lt : (i,t) ∈ lt → itree_path t li y z → itree_path (itree_node x lt) ([i] ∺ li) x z.

  Hint Constructors itree_path : core.

  Fact itree_path_root t l x y : itree_path t l x y → itree_root t = x.
  Proof. now induction 1. Qed.

  Fact itree_path_inv t l x y :
      itree_path t l x y
    ↔ match t with 
      | itree_node x' lit => 
              x' = x
            ∧ ( l = ε ∧ y = x 
              ∨ ∃ i l' t', l = [i] ∺ l' 
                         ∧ (i,t') ∈ lit 
                         ∧ itree_path t' l' (itree_root t') y )
      end.
  Proof. 
    split. 
    + induction 1; split; eauto; right; exists i, li, t; repeat split; auto.
      erewrite itree_path_root; eauto.
    + destruct t as [ x' lit ].
      intros (<- & [ (-> & ->) | (i & l' & t & -> & ? & ?) ]); econstructor; eauto. 
  Qed.

  Fact itree_fall_path_iff P t : itree_fall (λ x _, P x) t ↔ ∀ li x y, itree_path t li x y → P y.
  Proof.
    induction t as [ u lt IH ]; rewrite itree_fall_fix; split.
    + intros (H1 & H2) l x y (-> & [ (-> & ->) | (i & li' & t' & H3 & H4 & H5) ])%itree_path_inv; auto.
      revert H5; apply (IH _ _ H4); eauto.
    + intros H; split.
      * apply (H [] u u); auto.
      * intros i t Hit.
        apply (IH _ _ Hit).
        intros li x y Hl.
        apply (H ([i] ∺ li) u); eauto.
  Qed.

  Fact itree_exst_path_iff P t : itree_exst (λ x _, P x) t ↔ ∃ l x y, P y ∧ itree_path t l x y.
  Proof.
    split.
    + induction t as [ u lt IH ]; intros [ | (i & t & Hit & H) ]%itree_exst_fix.
      * exists [], u, u; auto.
      * apply IH with (1 := Hit) in H as (li & x & y & ? & ?).
        exists ([i] ∺ li), u, y; eauto.
    + intros (l & x & y & H1 & H2); revert H2 H1.
      induction 1; rewrite itree_exst_fix; eauto.
      right; eexists _, _; eauto.
  Qed.

  Fact itree_occurs_path_iff t y : itree_occurs y t ↔ ∃ li x, itree_path t li x y.
  Proof.
    unfold itree_occurs.
    rewrite itree_exst_path_iff.
    split.
    + intros (? & ? & ? & -> & ?); eauto.
    + intros (? & ? & ?); eauto.
  Qed.

  Section itree_path_find_dec.

    Variables (P Q : X → Prop)
              (PQ_dec : ∀ x, {P x} + {Q x}).

    (* Finds a path from the root of t to a node satisfying P, 
       or otherwise a proof that Q holds on every node *)
    Theorem itree_path_find_dec t : { '(l,y) | P y ∧ itree_path t l (itree_root t) y } 
                                  + { ∀ l y, itree_path t l (itree_root t) y → Q y }.
    Proof.
      induction t as [ u lt IH ].
      destruct (PQ_dec u) as [ Hu | Hu ].
      1: left; exists ([], u); simpl; auto.
      destruct list_choice_Type_Prop
        with (l := lt) 
             (P := λ p : I*_, { '(m,y) | P y ∧ itree_path (snd p) m (itree_root (snd p)) y}) 
             (Q := λ p : I*_, itree_fall (λ x _, Q x) (snd p))
        as [ [ (i,t) ((m,y) & H1 & H2) H3 ] | H ]; simpl in *.
      + intros (i,t) Hit.
        destruct IH with (1 := Hit) as [ (p & Hp) | q ].
        * left; now exists p.
        * right; apply itree_fall_path_iff; simpl.
          intros li x y H.
          apply (q li y).
          now rewrite (itree_path_root H).
      + left; exists ([i] ∺ m, y); eauto.
      + right.
        intros li y (_ & [ (-> & -> ) | (i & li' & t & Hi & Ht & H1) ])%itree_path_inv; auto.
        specialize (H _ Ht).
        rewrite itree_fall_path_iff in H.
        revert H1; apply H.
    Qed.

  End itree_path_find_dec.

  Variable (R : I → X → X → Prop).

  Variables (R_fin : ∀x, fin (λ '(i,y), R i x y)).

  Let itree_spanning x t := ∀ l y, itree_path t l x y ↔ iseq R l x y.

  Fact itree_spanning_root x t : itree_spanning x t → itree_root t = x.
  Proof. intros H; apply itree_path_root with [] x, H; constructor. Qed.

  (* Assuming R _ x _ is finitary and x is accessible for λ y x, ∃i, R i x y, then
     there is a spanning itree of which the paths are exactly the R-sequences from x *)
  Theorem itree_span x : Acc (λ y x, ∃i, R i x y) x → { t | itree_spanning x t }.
  Proof.
    induction 1 as [ x IH ] using Fix_F.
    destruct (R_fin x) as (liy & Hliy).
    assert (forall p, p ∈ liy -> sig (itree_spanning (snd p))) as Hliy'.
    1:{ intros (i,y) ?%Hliy; apply IH; now exists i. }
    apply forall_In_sig_pair in Hliy' as (liyt & H1 & H2).
    exists (itree_node x (map (fun '(i,_,t) => (i,t)) liyt)).
    intros l y.
    rewrite itree_path_inv, iseq_rinv; split.
    + intros (_ & [ (-> & ->) | (i & l' & t & -> & (((i',x'),t') & G1 & G2)%in_map_iff & G4)]); auto; right.
      inversion G1; subst i' t'.
      assert (itree_spanning x' t) as G3.
      1:{ apply (H2 _ _ G2). }
      generalize (itree_spanning_root G3); intros <-.
      exists i, (itree_root t), l'; repeat split; auto.
      * apply in_map with (f := fst) in G2.
        now rewrite <- H1, <- Hliy in G2.
      * apply G3, G4.
    + intros [ (-> & <-) | (i & z & l' & -> & G1 & G2) ]; split; auto; right.
      exists i, l'.
      rewrite (Hliy (i,z)), H1, in_map_iff in G1.
      destruct G1 as ((p,t) & G1 & G3); simpl in G1; subst p.
      exists t; repeat split; auto.
      * apply in_map_iff; now exists (i,z,t).
      * apply H2 in G3; simpl in G3.
        rewrite itree_spanning_root with (1 := G3).
        now apply G3.
  Qed.

  (* A covering itree for x collects in its node all R-accessible elements from x *) 
  Let itree_covering x t := itree_root t = x ∧ ∀y, itree_occurs y t ↔ ∃l, iseq R l x y.

  Lemma itree_spanning_covering : itree_spanning ⊆₂ itree_covering.
  Proof.
    intros x t Ht; split.
    + apply itree_spanning_root with (1 := Ht).
    + intros y; split.
      * intros (l & r & Hl)%itree_occurs_path_iff.
        generalize (itree_path_root Hl); rewrite (itree_spanning_root Ht); intros <-.
        apply Ht in Hl; eauto.
      * intros (l & Hl).
        apply itree_occurs_path_iff.
        exists l, x.
        now apply Ht.
  Qed.

  (* A collecting tree is a covering tree *)
  Corollary itree_cover x : Acc (λ y x, ∃i, R i x y) x → { t | itree_covering x t }.
  Proof.
    intros (t & Ht)%itree_span.
    exists t.
    revert Ht; apply itree_spanning_covering.
  Qed.

End itree.

Check itree_path_find_dec.
Check itree_span.
Check itree_cover.
