Set Warnings "-notation-overridden".

From Coq Require Import ssreflect.
From mathcomp.ssreflect Require Import ssrnat ssrbool bigop.
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

Fixpoint biprodN `{_ : @Monoidal C} (X : obj[C]) (n : nat) : obj[C] :=
    match n with
    | O => X
    | S n' => X ⨁ (biprodN X n')
    end.

Lemma biprodN_succ {X : obj[C]} {n : nat} : (X ⨁ (biprodN X n))%object = (biprodN X (S n)).
Proof. reflexivity. Qed.

Lemma biprod0 {X : obj[C]} : X = biprodN X 0.
Proof. reflexivity. Qed.

Fixpoint inj_n  {X : obj[C]} (maxn : nat) (n : nat) : X ~> biprodN X maxn :=
    match maxn with
    | O => id
    | S maxn' => 
        match n with
        | O => inj_l
        | S n' => inj_r ∘ (inj_n maxn' n')
        end
    end.

Fixpoint proj_n {X : obj[C]} (maxn : nat) (n : nat) : biprodN X maxn ~> X :=
    match maxn with
    | O => id
    | S maxn' =>
        match n with
        | O => proj_l
        | S n' => (proj_n maxn' n') ∘ proj_r
        end
    end.
Ltac done := cat_simpl.

Lemma inj_n_succ {X : obj[C]} (maxn n : nat) : (@inj_n X (maxn.+1) (n.+1)) ≈ inj_r ∘ (inj_n maxn n).
Proof. reflexivity. Qed.
Lemma proj_n_succ {X: obj[C]} (maxn n : nat) : (@proj_n X (maxn.+1) (n.+1)) ≈ (proj_n maxn n) ∘ proj_r.
Proof. reflexivity. Qed.

Definition bigsum {A B : obj[C]} (f : nat -> A ~> B) (maxn : nat) : A ~> biprodN B maxn :=
    \big [sum/unit]_ (0 <= i < maxn) ((inj_n maxn i) ∘ (f i)).

End BigOps.
