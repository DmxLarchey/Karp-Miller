```
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)
```

# What is this project

The project contains a correct by construction algorithm for deciding _coverability for Petri nets_, based on the construction of the 
Karp-Miller tree. It crucially exploits Dickson's lemma from the [`Kruskal-AlmostFull`](https://github.com/DmxLarchey/Kruskal-AlmostFull) library

```coq
af_vec_fall2 n X R : af R → af (λ u v : vec X n, ∀ i, R u⦃i⦄ v⦃i⦄).
```

The project is loosely inspired from an [Mathematical Components based version](https://bitbucket.org/mituharu/karpmiller/src/master/)
based on the paper [_Formalization of Karp-Miller tree construction on Petri nets (CPP 2017)_](https://dl.acm.org/doi/10.1145/3018610.3018626).

It was started as a basis for further discussions with the team of [Jérôme Leroux of LaBRI](https://www.labri.fr/perso/leroux/).

The main statement that we prove here is the following:
```coq
(** with imports from Relations, KruskalTrees, KruskalFinite
    and KruskalAFProp *)

Variables (NbPlaces : nat)             (* number of places *)
          (TrIdx : Type)               (* type of indices of transitions *)
          (TrIdx_fin : finite TrIdx).  (* finitely many transitions *)

Notation place := (idx NbPlaces).
Notation marking := (vec nat NbPlaces).

(* Infix notations for the component wise sum and comparison of vectors *)
Infix "+ₘ" := (vec_scal plus) (at level 50, left associativity).
Infix "≦⁺"  := (vec_fall2 le) (at level 70).

(* Description of a Petri net via its pre/post transitions *)
Variables (pre post : TrIdx → marking).

(* One Petri net transition *)
Inductive pn_trans : X → X → Prop :=
  | pnt_intro t u : pn_trans (u +ₘ pre t) (u +ₘ post t).

(* Reachability and coverability *)
Definition pn_reachable a b := clos_refl_trans pn_trans a b.
Definition pn_coverable s a := ∃b, pn_reacheable s b ∧ a ≦⁺ b.

(* One of the main results *)
Theorem pn_coverable_dec s a : { pn_coverable s a } + { ~ pn_coverable s a }.
```
but notice that we also build the whole Karp-Miller tree as a variant. However,
its statement requires many more definitions.

# How to compile

First you need to install the dependencies via `opam`:
```console
opam update
opam install . --deps-only
make all
```
and then you can review the code, starting with the main file [`karp_miller.v`](theories/karp_miller.v).
