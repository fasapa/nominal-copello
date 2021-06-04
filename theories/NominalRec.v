From FP Require Import Base Atom Permutation Term.

Lemma var_nominal_rec P: (forall b, P ('b)) -> forall a p, P (p ∙ₜ ('a)).
Proof. intros; rewrite perm_action_var; simpls; auto. Defined.

Lemma app_nominal_rec P:
  (forall p q, P p -> P q -> P (p × q)) ->
  forall m, (forall p, P (p ∙ₜ m)) -> forall n, (forall p, P (p ∙ₜ n)) -> (forall p, P (p ∙ₜ (m × n))).
Proof. intros; rewrite perm_action_app; simpls; auto. Defined.

Lemma abs_nominal_rec P:
  (forall a m, (forall p, P (p ∙ₜ m)) -> P (\a ⋅ m)) ->
  forall a m, (forall p, P (p ∙ₜ m)) -> (forall p, P (p ∙ₜ (\a ⋅ m))).
Proof.
  intros H1 ? ? ? ?; rewrite perm_action_abs; apply H1; intros.
    rewrite <- perm_action_concat; auto.
Defined.

Lemma nominal_rect:
  forall P: Λ -> Type,
    (forall t, P ('t)) ->
    (forall m n, P m -> P n -> P (m × n)) ->
    (forall a m, (forall p, P (p ∙ₜ m)) -> P (\a ⋅ m)) ->
    forall t, P t.
Proof.
  intros P Hvar Happ Habs t;
    apply (term_rect (fun t => forall p, P (p ∙ₜ t))
          (var_nominal_rec _ Hvar)
          (app_nominal_rec _ Happ)
          (abs_nominal_rec _ Habs)
          t []).
Defined.

Definition nominal_ind := (fun P: Λ -> Prop => nominal_rect P).
Definition nominal_rec := (fun P: Λ -> Set => nominal_rect P).
