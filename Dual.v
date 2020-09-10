Set Warnings "-notation-overridden".

From Coq Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export Category.Theory.
Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Import Category.Structure.Monoidal.Proofs.
Require Export CatQM.Dagger.
Require Import CatQM.Monoidal.

Section Dual.
Context {C : Category} `{M : @Monoidal C}.

Class Dual (L R : C) := {
    eta : I ~> R ⨂ L;
    eps : L ⨂ R ~> I;
    dual_id_l : (eps ⨂ id) ∘ tensor_assoc⁻¹ ∘ (id ⨂ eta) ≈ unit_left⁻¹ ∘ unit_right;
    dual_id_r : (id ⨂ eps) ∘ tensor_assoc ∘ (eta ⨂ id) ≈ unit_right⁻¹ ∘ unit_left
}.

Definition name   {A B A' B' : C} {dual_a : Dual A A'} {dual_b : Dual B B'} (f : A ~> B) : I ~> (A' ⨂ B) := (id ⨂ f) ∘ eta.
Definition coname {A B A' B' : C} {dual_a : Dual A A'} {dual_b : Dual B B'} (f : A ~> B) : (A ⨂ B') ~> I := eps ∘ (f ⨂ id).

Lemma double_snake_r {L R R' : C} {dual : Dual L R} {dual' : Dual L R'} : unit_right ∘ id{C} ⨂ eps ∘ tensor_assoc ∘ eta ⨂ id{C} ∘ unit_left⁻¹ ∘ (unit_right ∘ id{C} ⨂ eps ∘ tensor_assoc ∘ eta ⨂ id{C} ∘ unit_left⁻¹) ≈ (id : R ~{C}~> R).
Proof.
    do 3! [rewrite <- comp_assoc]; [rewrite -> (comp_assoc unit_left⁻¹ _ _)].
    rewrite <- from_unit_left_natural, -> !(comp_assoc (eta ⨂ id) _ _), <- interchange_law.
    rewrite -> id_right, -> id_left.
    rewrite <- (id_left eta), <- (id_right (_ ∘ (eta ⨂ id))), -> interchange_law.
    rewrite <- bimap_id_id, <- (comp_assoc _ tensor_assoc (eta ⨂ id{C})).
    rewrite <- (id_right (id{C} ⨂ id{C})), -> interchange_law, -> !(comp_assoc tensor_assoc _ _).
    rewrite <- to_tensor_assoc_natural, -> !comp_assoc, <- (comp_assoc unit_right (id ⨂ eps) _), <- interchange_law, -> id_left.
    rewrite <- (id_left id[L]), -> interchange_law, -> triangle_identity_right, -> !(comp_assoc eps _ _).

    rewrite -> to_unit_right_natural.
    rewrite <- (comp_assoc _ tensor_assoc⁻¹ _), <- from_tensor_assoc_natural.
    rewrite -> bimap_id_id, -> (comp_assoc (unit_right ∘ eps ⨂ id{C}) _ _);
    rewrite <- (comp_assoc _ (eps ⨂ id{C}) _), <- interchange_law.
    rewrite -> id_left, -> id_right. rewrite <- (id_left eps), <- (id_right (@eps _ _ dual)), -> interchange_law.
    rewrite <- !bimap_id_id.
    rewrite <- (comp_assoc _ _ tensor_assoc), <- (comp_assoc _ _ ((id{C} ⨂ id{C}) ⨂ (tensor_assoc ∘ eta ⨂ id{C}))),
    <- (comp_assoc _ tensor_assoc _). rewrite <- to_tensor_assoc_natural.
    rewrite -> (comp_assoc _ _ tensor_assoc), <- interchange_law.
    rewrite -> id_right, <- (id_right id[L]), -> interchange_law, -> (comp_assoc _ (id{C} ⨂ tensor_assoc) _), <- (comp_assoc _ tensor_assoc⁻¹ _).
    have by_pentagon_identity : tensor_assoc⁻¹ ∘ id{C} ⨂ tensor_assoc ≈ tensor_assoc ∘ tensor_assoc⁻¹ ⨂ id ∘ tensor_assoc⁻¹.
        move => a b c d. symmetry.
        rewrite <- id_left, <- (iso_from_to tensor_assoc).
        rewrite -> !comp_assoc, <- (comp_assoc _ tensor_assoc tensor_assoc), <- pentagon_identity, -> comp_assoc.
        rewrite <- (comp_assoc _ (tensor_assoc ⨂ id)), <- interchange_law, -> iso_to_from, -> id_right, -> bimap_id_id, -> id_right.
        rewrite -> comp_assoc, <- (comp_assoc _ tensor_assoc _), -> iso_to_from, -> id_right.
        reflexivity.
    rewrite -> by_pentagon_identity, <- !(comp_assoc _ _ (id{C} ⨂ eta ⨂ id{C})), <- from_tensor_assoc_natural.
    rewrite -> id_right, -> !comp_assoc, <- (comp_assoc _ (eps ⨂ id{C} ⨂ id{C}) tensor_assoc).
    rewrite -> to_tensor_assoc_natural, <- (comp_assoc _ _ (tensor_assoc⁻¹ ⨂ id{C})), <- (comp_assoc _ _ ((id{C} ⨂ eta) ⨂ id{C})).
    do 2! rewrite <- (comp_assoc tensor_assoc _ _), <- interchange_law.
    rewrite -> dual_id_l.

    rewrite -> interchange_law, <- !(comp_assoc _ _ tensor_assoc⁻¹), -> (comp_assoc tensor_assoc _ _ ), -> id_right.
    rewrite <- inverse_triangle_identity, -> !comp_assoc, <- (id_right id[R]), -> interchange_law.
    rewrite -> comp_assoc. rewrite <- (comp_assoc _ (id{C} ⨂ id{C} ⨂ unit_left) tensor_assoc).
    rewrite -> to_tensor_assoc_natural, -> bimap_id_id.
    rewrite -> comp_assoc. rewrite <- (comp_assoc _ (id{C} ⨂ unit_left)).
    rewrite <- interchange_law, -> id_left, bimap_id_id, -> id_right, -> id_left, <- (id_right eta), <- (id_left unit_left).
    rewrite -> interchange_law.
    rewrite -> comp_assoc, <- (comp_assoc _ (id{C} ⨂ unit_left) unit_left⁻¹).
    rewrite -> from_unit_left_natural, -> iso_from_to, -> id_right.
    have by_triangle_identity : tensor_assoc ∘ (unit_left⁻¹ ⨂ id) ≈ unit_left⁻¹.
        move => o1 o2.
        rewrite <- id_left, <- (iso_from_to unit_left), -> comp_assoc, <- (comp_assoc _ unit_left tensor_assoc).
        rewrite <- triangle_identity_left, <- comp_assoc, <- interchange_law, -> iso_to_from, -> id_right, -> bimap_id_id, -> id_right.
        reflexivity.
    rewrite <- (comp_assoc _ tensor_assoc (unit_left⁻¹ ⨂ id{C})), -> by_triangle_identity.
    rewrite <- (comp_assoc _ (id ⨂ eps) unit_left⁻¹), -> from_unit_left_natural, -> comp_assoc.
    rewrite <- (id_right id[R]), -> interchange_law, -> comp_assoc, <- (comp_assoc _ (id{C} ⨂ eps) _), -> id_right, <- (comp_assoc _ _ (eta ⨂ id)).
    rewrite -> dual_id_r.

    rewrite <- unit_identity, -> iso_to_from, -> bimap_id_id, -> id_right, -> !comp_assoc.
    rewrite -> iso_to_from, -> id_left, -> iso_to_from. reflexivity.
Qed.

Lemma right_dual_unique {L R R' : C} {dual : Dual L R} {dual' : Dual L R'} : R ≈ R'.
Proof.
    construct.
    exact (unit_right ∘ (id ⨂ eps) ∘ tensor_assoc ∘ (eta ⨂ id) ∘ unit_left⁻¹).
    exact (unit_right ∘ (id ⨂ eps) ∘ tensor_assoc ∘ (eta ⨂ id) ∘ unit_left⁻¹).
    all: apply double_snake_r.
Qed.

Lemma double_snake_l {L L' R : C} {dual : Dual L R} {dual' : Dual L' R} : unit_left ∘ eps ⨂ id ∘ tensor_assoc⁻¹ ∘ id ⨂ eta ∘ unit_right⁻¹ ∘ (unit_left ∘ eps ⨂ id ∘ tensor_assoc⁻¹ ∘ id ⨂ eta ∘ unit_right⁻¹) ≈ (id : L ~> L).
Proof.
    do 3! [rewrite <- comp_assoc]; [rewrite -> (comp_assoc unit_right⁻¹ _ _)].
    rewrite <- from_unit_right_natural, -> !(comp_assoc (id ⨂ eta) _ _), <- interchange_law.
    rewrite -> id_left, -> id_right.
    set tmp_var := (id ⨂ eta); rewrite  <- (id_right (_ ∘ tmp_var)), <- (id_left eta), -> interchange_law; unfold tmp_var; move: tmp_var => _.
    rewrite <- bimap_id_id, <- (comp_assoc _ tensor_assoc⁻¹ (id ⨂ eta)).
    rewrite <- (id_right (id ⨂ id)), -> interchange_law, -> !(comp_assoc tensor_assoc⁻¹ _ _).
    rewrite <- from_tensor_assoc_natural, -> !comp_assoc, <- (comp_assoc unit_left (eps ⨂ id)), <- interchange_law, -> id_left.
    rewrite <- (id_left id[R]), -> interchange_law, -> triangle_identity_left, -> !(comp_assoc eps).

    rewrite -> to_unit_left_natural.
    rewrite <- (comp_assoc _ tensor_assoc _), <- to_tensor_assoc_natural.
    rewrite -> bimap_id_id, -> (comp_assoc (unit_left ∘ id ⨂ eps)).
    rewrite <- (comp_assoc _ (id ⨂ eps) _), <- interchange_law.
    rewrite -> id_left, -> id_right. rewrite <- (id_right eps), <- (id_left (@eps _ _ dual')), -> interchange_law.
    rewrite <- !bimap_id_id.
    rewrite <- (comp_assoc _ _ tensor_assoc⁻¹), <- (comp_assoc _ _ ((tensor_assoc⁻¹ ∘ id{C} ⨂ eta) ⨂ id{C} ⨂ id{C})),
        <- (comp_assoc _ tensor_assoc⁻¹ _). rewrite <- from_tensor_assoc_natural.
    rewrite -> (comp_assoc _ _ tensor_assoc⁻¹). rewrite <- interchange_law.
    rewrite -> id_right, <- (id_right id[R]), -> interchange_law, -> (comp_assoc _ (tensor_assoc⁻¹ ⨂ id) _), <- (comp_assoc _ tensor_assoc _).
    have by_pentagon_identity : tensor_assoc ∘ tensor_assoc⁻¹ ⨂ id ≈ tensor_assoc⁻¹ ∘ id ⨂ tensor_assoc ∘ tensor_assoc.
        move => a b c d. symmetry.
        rewrite <- id_left, <- (iso_to_from tensor_assoc).
        rewrite -> !comp_assoc, <- (comp_assoc _ tensor_assoc⁻¹ tensor_assoc⁻¹), <- inverse_pentagon_identity.
        rewrite -> (comp_assoc _ _ (id ⨂ tensor_assoc⁻¹)), <- (comp_assoc _ (id ⨂ tensor_assoc⁻¹) (id ⨂ tensor_assoc)),
            <- interchange_law, -> iso_from_to, -> id_left, -> bimap_id_id, -> id_right.
        rewrite -> comp_assoc, <- (comp_assoc _ tensor_assoc⁻¹ tensor_assoc), -> iso_from_to, -> id_right.
        reflexivity.
    rewrite -> by_pentagon_identity, <- !(comp_assoc _ _ ((id{C} ⨂ eta) ⨂ id{C})), <- to_tensor_assoc_natural.
    rewrite -> !id_right, -> !comp_assoc, <- (comp_assoc _ ((id ⨂ id) ⨂ eps) tensor_assoc⁻¹).
    rewrite -> from_tensor_assoc_natural, <- (comp_assoc _ _ (id ⨂ tensor_assoc)), <- (comp_assoc _ _ (id ⨂ eta ⨂ id)).
    do 2! rewrite <- (comp_assoc tensor_assoc⁻¹ _ _), <- interchange_law.
    rewrite -> dual_id_r.

    rewrite -> interchange_law, <- !(comp_assoc _ _ tensor_assoc), -> (comp_assoc tensor_assoc⁻¹ _ _), -> id_right.
    rewrite <- triangle_identity, -> !comp_assoc. rewrite <- (id_right id[L]), -> interchange_law.
    rewrite -> comp_assoc, <- (comp_assoc _ ((unit_right ⨂ id{C}) ⨂ id{C}) tensor_assoc⁻¹).
    rewrite -> from_tensor_assoc_natural, -> bimap_id_id.
    rewrite -> comp_assoc, <- (comp_assoc _ (unit_right ⨂ id)), <- interchange_law.
    rewrite -> id_left, bimap_id_id, -> id_right, -> id_left.
    rewrite <- (id_right eta), <- (id_left unit_right), -> interchange_law.
    rewrite -> comp_assoc, <- (comp_assoc _ (unit_right ⨂ id) unit_right⁻¹).
    rewrite -> from_unit_right_natural, -> iso_from_to, -> id_right.
    have by_triangle_identity : tensor_assoc⁻¹ ∘ id ⨂ unit_right⁻¹ ≈ unit_right⁻¹.
        move => o1 o2.
        rewrite <- id_left, <- (iso_from_to unit_right), -> comp_assoc, <- (comp_assoc _ unit_right _), <- triangle_identity_right.
        rewrite <- comp_assoc, <- interchange_law, -> iso_to_from, -> id_right, -> bimap_id_id, -> id_right.
        reflexivity.
    rewrite <- (comp_assoc _ tensor_assoc⁻¹ (id{C} ⨂ unit_right⁻¹)), -> by_triangle_identity.
    rewrite <- (comp_assoc _ (eps ⨂ id) _), -> from_unit_right_natural, -> comp_assoc.
    rewrite <- (id_right id[L]), -> interchange_law, -> comp_assoc, <- (comp_assoc _ (eps ⨂ id) _), -> id_right, <- (comp_assoc _ _ (id ⨂ eta)).
    rewrite -> dual_id_l.

    rewrite -> unit_identity, -> iso_to_from, -> bimap_id_id, -> id_right, -> !comp_assoc.
    rewrite -> iso_to_from, -> id_left, -> iso_to_from. reflexivity.
Qed.

Lemma left_dual_unique {L L' R : C} {dual : Dual L R} {dual' : Dual L' R} : L ≈ L'.
Proof.
    construct.
    exact (unit_left ∘ eps ⨂ id ∘ tensor_assoc⁻¹ ∘ id ⨂ eta ∘ unit_right⁻¹).
    exact (unit_left ∘ eps ⨂ id ∘ tensor_assoc⁻¹ ∘ id ⨂ eta ∘ unit_right⁻¹).
    all: apply double_snake_l.
Qed.

Lemma left_dual_iso {L L' R : C} {dual : Dual L R} (iso : L ≈ L') : Dual L' R.
Proof.
    construct.
    + exact (id ⨂ iso ∘ eta).
    + exact (eps ∘ iso⁻¹ ⨂ id).
    + rewrite <- (id_left id[L']), -> interchange_law, <- (comp_assoc _ _ tensor_assoc⁻¹).
      rewrite -> from_tensor_assoc_natural, -> comp_assoc, <- (comp_assoc _ (iso⁻¹ ⨂ id{C} ⨂ id{C}) _).
      rewrite <- interchange_law, -> bimap_id_id, -> !id_right, -> id_left.
      rewrite <- (id_left iso⁻¹), <- (id_right (id{C} ⨂ iso ∘ eta)), -> interchange_law, -> comp_assoc.
      rewrite <- (id_left id[L]), -> interchange_law, -> comp_assoc, <- (comp_assoc _ tensor_assoc⁻¹ _), <- from_tensor_assoc_natural, -> comp_assoc.
      rewrite -> bimap_id_id, <- interchange_law, -> id_left, -> id_right, <- (id_right iso), <- (id_left eps), -> interchange_law.
      do 2! [rewrite <- (comp_assoc (id ⨂ iso))]; rewrite -> dual_id_l, -> comp_assoc.
      rewrite -> from_unit_left_natural, <- comp_assoc, <- to_unit_right_natural.
      rewrite -> comp_assoc, <- (comp_assoc _ iso _), -> iso_to_from, -> id_right.
      reflexivity.
    + rewrite <- (id_left id[R]), -> !interchange_law, <- (comp_assoc _ _ tensor_assoc), -> to_tensor_assoc_natural.
      rewrite -> !comp_assoc, -> id_left, <- (comp_assoc _ ((id{C} ⨂ iso⁻¹) ⨂ id{C})), <- interchange_law, <- interchange_law.
      rewrite -> iso_from_to, -> id_right, -> !bimap_id_id, -> id_right.
      apply dual_id_r.
Qed.

Lemma right_dual_iso {L R R' : C} {dual : Dual L R} (iso : R ≈ R') : Dual L R'.
Proof.
    construct.
    + exact (iso ⨂ id ∘ eta).
    + exact (eps ∘ id ⨂ iso⁻¹).
    + rewrite <- (id_left id[L]), -> !interchange_law, <- (comp_assoc _ _ tensor_assoc⁻¹), -> from_tensor_assoc_natural.
      rewrite <- !comp_assoc, -> id_left, -> (comp_assoc _ (id{C} ⨂ iso ⨂ id{C}) _), <- interchange_law, <- (interchange_law (g:=iso⁻¹) (f:=iso)).
      rewrite -> iso_from_to, -> id_right, -> !bimap_id_id, -> id_left, -> comp_assoc.
      apply dual_id_l.
    + rewrite <- (id_left id[R']), -> interchange_law, <- (comp_assoc _ _ tensor_assoc).
      rewrite -> to_tensor_assoc_natural, -> comp_assoc, <- (comp_assoc _ ((id{C} ⨂ id{C}) ⨂ iso⁻¹) _).
      rewrite <- interchange_law, -> bimap_id_id, -> !id_right, -> id_left.
      rewrite <- (id_left iso⁻¹), <- (id_right (iso ⨂ id ∘ eta)), -> interchange_law, -> comp_assoc.
      rewrite <- (id_left id[R]), -> interchange_law, -> comp_assoc, <- (comp_assoc _ tensor_assoc _), <- to_tensor_assoc_natural, -> comp_assoc.
      rewrite -> bimap_id_id, <- interchange_law, -> id_left, -> id_right, <- (id_right iso), <- (id_left eps), -> interchange_law.
      do 2! [rewrite <- (comp_assoc (iso ⨂ id) _ _)]; rewrite -> dual_id_r, -> comp_assoc.
      rewrite -> from_unit_right_natural, <- comp_assoc, <- to_unit_left_natural.
      rewrite -> comp_assoc, <- (comp_assoc _ iso _), -> iso_to_from, id_right.
      reflexivity.
Qed.

Lemma eps_map_unique {L R : C} {dual dual' : Dual L R} (eta_iso : (@eta L R dual) ≈ (@eta L R dual')) : (@eps L R dual) ≈ (@eps L R dual').
Proof.
    rewrite <- (id_right eps), <- bimap_id_id, <- (iso_to_from (y:=L) unit_left).
    rewrite <- (id_right unit_left⁻¹), <- (iso_to_from unit_right), -> (comp_assoc unit_left⁻¹ _ _), <- dual_id_l.
    rewrite <- (id_right id[R]), -> interchange_law, -> triangle_identity_left, -> !comp_assoc, -> to_unit_left_natural.
    rewrite <- (id_right id[R]), <- (id_right id[R]), <- !(comp_assoc _ _ unit_right⁻¹), -> !interchange_law, -> !comp_assoc, <- (comp_assoc _ tensor_assoc _), <- to_tensor_assoc_natural, -> comp_assoc, -> bimap_id_id, <- (comp_assoc _ (id ⨂ eps) _).
    rewrite <- interchange_law, -> id_left, -> id_right, <- (id_left (@eps L R dual)), <- (id_right (@eps L R dual')), -> interchange_law.
    have by_pentagon_identity : tensor_assoc ∘ tensor_assoc⁻¹ ⨂ id ≈ tensor_assoc⁻¹ ∘ id ⨂ tensor_assoc ∘ tensor_assoc.
        move => a b c d. symmetry.
        rewrite <- id_left, <- (iso_to_from tensor_assoc).
        rewrite -> !comp_assoc, <- (comp_assoc _ tensor_assoc⁻¹ tensor_assoc⁻¹), <- inverse_pentagon_identity.
        rewrite -> (comp_assoc _ _ (id ⨂ tensor_assoc⁻¹)), <- (comp_assoc _ (id ⨂ tensor_assoc⁻¹) (id ⨂ tensor_assoc)),
            <- interchange_law, -> iso_from_to, -> id_left, -> bimap_id_id, -> id_right.
        rewrite -> comp_assoc, <- (comp_assoc _ tensor_assoc⁻¹ tensor_assoc), -> iso_from_to, -> id_right.
        reflexivity.
    rewrite <- (comp_assoc _ tensor_assoc _), -> by_pentagon_identity, -> (comp_assoc unit_left _ _), <- (comp_assoc _ (id ⨂ eps) _), -> !(comp_assoc (id ⨂ eps) _ _), <- bimap_id_id, -> from_tensor_assoc_natural.
    rewrite <- (comp_assoc (unit_left ∘ eps ⨂ id{C}) _ _), <- (comp_assoc _ tensor_assoc _), <- to_tensor_assoc_natural, -> (comp_assoc _ _ tensor_assoc), <- !(comp_assoc tensor_assoc⁻¹ _ _), <- !interchange_law, -> !id_right.
    rewrite <- eta_iso, -> (@dual_id_r L R dual).
    have by_triangle_identity : tensor_assoc⁻¹ ∘ id ⨂ unit_right⁻¹ ≈ unit_right⁻¹.
        move => o1 o2.
        rewrite <- id_left, <- (iso_from_to unit_right), -> comp_assoc, <- (comp_assoc _ unit_right _), <- triangle_identity_right.
        rewrite <- comp_assoc, <- interchange_law, -> iso_to_from, -> id_right, -> bimap_id_id, -> id_right.
        reflexivity.
    rewrite <- (id_left id[L]), -> interchange_law, <- (comp_assoc _ _ tensor_assoc), <- triangle_identity, -> (comp_assoc tensor_assoc⁻¹ _ _), -> by_triangle_identity.
    rewrite <- (comp_assoc unit_left _ _), -> (comp_assoc _ unit_right⁻¹ _), -> from_unit_right_natural.
    rewrite -> !comp_assoc, -> unit_identity, -> iso_to_from, -> id_right, -> id_left, <- comp_assoc, <- interchange_law, -> iso_to_from, -> id_right. reflexivity.
Qed.

Lemma eta_map_unique {L R : C} {dual dual' : Dual L R} (eps_iso : (@eps L R dual) ≈ (@eps L R dual')) : (@eta L R dual) ≈ (@eta L R dual').
Proof.
    rewrite <- (id_left eta), <- bimap_id_id, <- (iso_to_from (y:=R) unit_left).
    rewrite <- (id_left unit_left), <- (iso_to_from unit_right), <- (comp_assoc unit_right _ _), <- dual_id_r.
    rewrite <- (id_left id[L]), <- (id_left id[L]), <- (id_left id[L]), -> !(comp_assoc unit_right _ _), <- (comp_assoc _ (eta ⨂ id{C}) _), -> !interchange_law, -> id_right.
    have by_triangle_identity : unit_left⁻¹ ⨂ id ≈ tensor_assoc⁻¹ ∘ unit_left⁻¹.
        move => a b.
        rewrite <- id_right, <- (iso_to_from (y:=(a ⨂ b)) unit_left), <- (id_right unit_left), <- (iso_to_from (y:=(I ⨂ a ⨂ b)) tensor_assoc).
        rewrite -> (comp_assoc unit_left _ _), <- triangle_identity_left, -> !comp_assoc, <- interchange_law, -> iso_from_to. cat.
    rewrite -> by_triangle_identity, <- !(comp_assoc _ _ eta), -> (comp_assoc _ tensor_assoc⁻¹ _), <- from_unit_left_natural, -> from_tensor_assoc_natural.
    rewrite -> (comp_assoc _ (id{C} ⨂ eta) _), <- (comp_assoc _ _ (id{C} ⨂ eta)).
    rewrite <- (interchange_law (f:=id) (h:=eta)), -> bimap_id_id, -> id_left, -> id_right, <- (id_left (@eta L R dual')), <- (id_right (@eta L R dual)), -> interchange_law, <- bimap_id_id.
    have by_pentagon_identity : tensor_assoc ⨂ id ∘ tensor_assoc⁻¹ ≈ tensor_assoc⁻¹ ∘ id ⨂ tensor_assoc⁻¹ ∘ tensor_assoc.
        move => a b c d. symmetry.
        rewrite <- id_left, <- bimap_id_id, <- (iso_to_from tensor_assoc), <- (id_left id[d]), -> interchange_law.
        rewrite <- comp_assoc, -> !(comp_assoc (tensor_assoc⁻¹ ⨂ id{C}) _ _), -> inverse_pentagon_identity.
        rewrite <- comp_assoc, -> iso_from_to; cat.
    rewrite -> !comp_assoc, <- (comp_assoc _ _ tensor_assoc⁻¹), -> by_pentagon_identity.
    rewrite -> !comp_assoc, <- (comp_assoc _ _ tensor_assoc⁻¹), <- (comp_assoc _ tensor_assoc _).
    rewrite -> from_tensor_assoc_natural, <- to_tensor_assoc_natural.
    rewrite -> !comp_assoc, <- (comp_assoc _ _ (id ⨂ tensor_assoc⁻¹)), <- (comp_assoc _ _ (id ⨂ id ⨂ eta)).
    rewrite <- !interchange_law, -> !id_left.
    rewrite <- eps_iso, -> (@dual_id_l L R dual).
    have by_triangle_identity' : tensor_assoc⁻¹ ∘ id ⨂ unit_left⁻¹ ≈ unit_right⁻¹ ⨂ id.
        move => o1 o2. symmetry.
        rewrite <- id_right, <- bimap_id_id, <- (id_left id[o1]), <- (iso_to_from unit_left), -> interchange_law, -> inverse_triangle_identity.
        normal; rewrite -> iso_to_from, -> iso_from_to; cat.
    rewrite <- (id_left id[R]), -> interchange_law, -> comp_assoc, <- (comp_assoc _ _ (id{C} ⨂ unit_left⁻¹)), <- (comp_assoc _ _ tensor_assoc), -> by_triangle_identity', <- bimap_triangle_right.
    rewrite <- (comp_assoc _ unit_right _), <- to_unit_right_natural, -> comp_assoc, <- (comp_assoc _ _ unit_left⁻¹), <- unit_identity, <- interchange_law, -> !iso_to_from.
    normal. reflexivity.
Qed.

End Dual.

Class Compact `{C : Category} := {
    monoidal_witness :> @Monoidal C;
    dual : C -> C;
    dual_witness : forall X : C, Dual X (dual X)
}.

