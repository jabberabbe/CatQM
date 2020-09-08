Set Warnings "-notation-overridden".

Require Import Program.
From Coq Require Import ssreflect.
From mathcomp.ssreflect Require Import ssrnat ssrbool bigop fintype finfun eqtype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export Category.Theory.
Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Export CatQM.Dagger.
Require Import CatQM.Monoidal.
Require Import CatQM.Biproduct.
Require Import CatQM.Superposition.
Require Import CatQM.Zero.

Section BigOps.
Context {C : Category}.
Context `{_ : @Monoidal C} `{S' : @Superposition C} `{Z : @Zero C} `{_ : @Biproduct C S' Z}.

Lemma ordinal_equality {k a : nat} (p q : ltn a (S k)) : (Ordinal p) = (Ordinal q).
Proof. by apply/val_inj. Defined.

Lemma ord0_fin1 (k : ordinal 1) : k = ord0.
Proof.
  destruct k; unfold ord0.
  have Q : m = 0%N by move: m i; case.
  move: i; rewrite Q.
  symmetry; by apply ordinal_equality.
Qed.

Definition ord_widen_succ (a : nat) (b : ordinal a) : ordinal (S a).
Proof. case: b => m i; construct. exact (S m). exact i. Defined.

Program Fixpoint biprodN' {n : nat} (X : ordinal (n.+1) -> obj[C]) : obj[C] :=
    match n with
    | O => (X ord0)
    | S n' => (X ord0) ⨁ (@biprodN' n' (fun k => X (ord_widen_succ k)))
    end.

Definition biprodN (n : nat) (X : obj[C]) := @biprodN' n (fun _ => X).

Lemma biprodN_succ {X : obj[C]} {n : nat} : (X ⨁ (biprodN n X))%object = (biprodN (S n) X).
Proof. reflexivity. Qed.

Lemma biprod0 {X : obj[C]} : X = biprodN 0 X.
Proof. reflexivity. Qed.

Lemma biprod0' {X : ordinal 1 -> obj[C]} : (X ord0) = biprodN' (n:=0) X.
Proof. reflexivity. Qed.

Fixpoint inj_n' {maxn : nat} {X : ordinal (maxn.+1) -> obj[C]} {n : ordinal (maxn.+1)} : (X n) ~> biprodN' (n:=maxn) X.
Proof.
    move: X n.
    case: maxn => [X n //=|maxn X].
    - case: n => [m H']; rewrite (ord0_fin1 (Ordinal H')); exact id.
    - case; case => [i //=|n i]. 
      + rewrite /ord0 (ordinal_equality i (ltn0Sn (S maxn))); exact inj_l.
      + simpl; have P : (ltn n (S maxn)) by [].
        have -> : (Ordinal i) = (ord_widen_succ (Ordinal P)) by rewrite /ord_widen_succ ordinal_equality.
        exact (inj_r ∘ (@inj_n' maxn (fun k => X (ord_widen_succ k)) (Ordinal P))).
Defined.
Definition inj_n {maxn : nat} {X} := @inj_n' maxn (fun _ => X).

Fixpoint proj_n' {maxn : nat} {X : ordinal (maxn.+1) -> obj[C]} {n : ordinal (maxn.+1)} : biprodN' (n:=maxn) X ~> (X n).
Proof.
    move: X n.
    case: maxn => [X n //=|maxn X].
    - case: n => [m H']; rewrite (ord0_fin1 (Ordinal H')); exact id.
    - case; case => [i //=|n i]. 
      + rewrite /ord0 (ordinal_equality i (ltn0Sn (S maxn))); exact proj_l.
      + simpl; have P : (ltn n (S maxn)) by [].
        have -> : (Ordinal i) = (ord_widen_succ (Ordinal P)) by rewrite /ord_widen_succ ordinal_equality.
        exact ((@proj_n' maxn (fun k => X (ord_widen_succ k)) (Ordinal P)) ∘ proj_r).
Defined.
Definition proj_n {maxn : nat} {X} := @proj_n' maxn (fun _ => X).

Ltac done := cat_simpl.

Definition bigsum {maxn : nat} {A : obj[C]} {B : forall x : (ordinal (maxn.+1)), obj[C]}
    (f : forall n : (ordinal (maxn.+1)), A ~> (@B n)) : A ~> biprodN' B :=
    \big[sum/through_zero]_ (i < (maxn.+1)) (inj_n' ∘ (f i)).
End BigOps.

