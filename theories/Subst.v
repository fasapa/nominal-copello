From FP Require Import Base Atom Permutation Term NominalRec Alpha.
Local Open Scope aset_scope.

(* Term substitution *)
Definition subst_term (M N: Λ) (a: atom): Λ :=
  @LIt Λ (fun b => if a == b then N else 'b) App Abs ({{a}} ∪ support N) M.

(* Notação temporária *)
Notation " '[' a ':=' N ']' M " :=
  (subst_term (M%term) (N%term) (a%atom))
    (at level 59, M at next level, format "[ a  :=  N ] M"): term_scope.

Lemma subst_aeq1 m n t a: m ≡α n -> [a := t]m = [a := t]n.
Proof. intros; apply LIt_StrongCompat; auto. Qed.

Lemma subst_app m n t a: [a := t](m × n) = ([a := t]m) × ([a := t]n).
Proof. unfold subst_term; rewrite LIt_app; auto. Qed.

Lemma subst_abs a c m t: [c := t](\a ⋅ m) = (let z := fresh (support (\a ⋅ m) ∪ {{c}} ∪ support t) in \z ⋅ ( [c := t]((a ∙ z)ₜ m) )).
Proof. unfold subst_term; rewrite LIt_abs; simpl; auto. Qed.

Lemma lala: forall a m n, m ≡α n -> \a ⋅ m ≡α \a ⋅ n.
Proof. intros; apply AeqAbs with (∅)%aset; intros; apply (aeq_perm _ _ [(_,_)]); auto. Qed.

Lemma subst_aeq2 m n n' a: n ≡α n' -> [a := n]m ≡α [a := n']m.
Proof.
  gen n n' a; induction m using nominal_ind; intros.
  - destruct (t == a); subst.
    + unfold subst_term; do 2 rewrite LIt_var; simplify.
    + unfold subst_term; do 2 rewrite LIt_var; simplify.
  - do 2 rewrite subst_app; constructor.
    + apply IHm1; auto.
    + apply IHm2; auto.
  - do 2 rewrite subst_abs; lets HH0:H0; apply aeq_support in H0; simpl.
    assert (HH1: ((a \ support m) ∪ {{a0}} ∪ support n [=] (a \ support m) ∪ {{a0}} ∪ support n')%aset).
    { rewrite H0; fsetdec. }
    assert (HH2: fresh ((a \ support m) ∪ {{a0}} ∪ support n) = fresh ((a \ support m) ∪ {{a0}} ∪ support n')).
    { apply fresh_set_eq; auto. }
    rewrite HH2. apply lala. set (z := fresh ((a \ support m) ∪ {{a0}} ∪ support n')).
    apply (H [(_,_)]); auto.
Qed.

Lemma subst_aeq3 a m m' n n': m ≡α m' -> n ≡α n' -> [a := n]m ≡α [a := n']m'.
Proof. intros H1 H2; rewrite (subst_aeq1 m m'); [apply subst_aeq2 |]; auto. Qed.

Lemma subst_var_eq a b p: a = b -> [b := p]('a) = p.
Proof. intros; subst; unfold subst_term; rewrite LIt_var; simplify. Qed.

Lemma subst_var_neq a b p: a <> b -> [b := p]('a) = 'a.
Proof. intros; unfold subst_term; rewrite LIt_var; simplify. Qed.

Lemma subst_abs_neq a b p m: a <> b -> b#(p) -> [a := p](\b ⋅ m) ≡α \b ⋅ ([a := p]m).
Proof. Admitted.

Lemma subst_neq a p m: a#(m) -> [a := p]m ≡α m.
Proof. Admitted.

Lemma aeq_abs_body a m n: m ≡α n -> \a ⋅ m ≡α \a ⋅ n.
Proof. Admitted.

Lemma support_subst a b p m: a <> b -> a#(p,m) -> a#([b := p]m).
Proof. Admitted.

Lemma subst_comp a b p q m:
  a <> b -> a#(p) -> [b := p]([a := q]m) ≡α [a := ([b := p]q)]([b := p]m).
Proof.
  intros; gen m; apply term_aeq_ind.
  - simpl; intros m n AEQ HY. apply aeq_trans with ([a := [b := p]q]([b := p]m)).
    + apply aeq_trans with ([b := p]([a := q]m)); [rewrite (subst_aeq1 _ _ _ _ AEQ) |]; auto.
    + rewrite (subst_aeq1 _ _ _ _ AEQ); auto.
  - intros x; simpl; destruct (x == a), (x == b); subst.
    + congruence.
    + rewrite~ (subst_var_neq a b); do 2 rewrite~ subst_var_eq.
    + rewrite~ subst_var_neq; rewrite~ subst_var_eq; symmetry; apply~ subst_neq.
    + repeat rewrite~ subst_var_neq.
  - intros; repeat rewrite subst_app; constructor; auto.
  - exists ({{a}} ∪ {{b}} ∪ support q ∪ support p); intros m x ? IH.
      apply aeq_trans with ([b := p](\x ⋅ ([a := q]m))).
    + rewrite (subst_aeq1 ([a := q](\x ⋅ m)) (\x ⋅ [a := q]m)); [| apply subst_abs_neq; fsetdec]; auto.
    + apply aeq_trans with (\x ⋅ [b := p]([a := q]m)).
      * apply subst_abs_neq; fsetdec.
      * apply aeq_trans with (\x ⋅ [a := [b := p]q]([b := p]m)).
        -- apply aeq_abs_body; auto.
        -- symmetry; apply aeq_trans with ([a := [b := p]q](\x ⋅ ([b := p]m))).
           ++ rewrite (subst_aeq1 ([b := p](\x ⋅ m)) (\x ⋅ [b := p]m)); [| apply subst_abs_neq; fsetdec]; auto.
           ++ apply aeq_trans with (\x ⋅ [a := [b := p]q]([b := p]m)).
              ** apply subst_abs_neq; [| apply support_subst]; fsetdec.
              ** auto.
Qed.
