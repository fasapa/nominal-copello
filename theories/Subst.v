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

Lemma subst_var a b m : [a := m]('b) = (if a == b then m else 'b).
Proof. unfold subst_term; rewrite LIt_var; reflexivity. Qed.

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

Lemma T1: ∀ a b c N M, (a ∙ b)ₜ ([c := N]M) ≡α [((a ∙ b)ₐ c) := ((a ∙ b)ₜ N)]((a ∙ b)ₜ M).
Proof. Admitted.

Lemma subst_abs_neq a b m n: a <> b -> b#(n) -> [a := n](\b ⋅ m) ≡α \b ⋅ ([a := n]m).
Proof. 
  intros; rewrite subst_abs; simpl; set (c := fresh _).
  apply fresh AeqAbs with d.
  etransitivity. apply T1.
  rewrite (subst_aeq1 ((c ∙ d)ₜ(b ∙ c)ₜm) ((b ∙ d)ₜm)).
  - rewrite swap_neither; [idtac | (* obvio, precisa do lema certo. *) admit | fsetdec].
    etransitivity. apply subst_aeq2 with (n' := n). apply aeq_perm_action1_neither.
    (* obvio, precisa do lema certo. *) admit. fsetdec.
    etransitivity. apply subst_aeq2 with (n' := (b ∙ d)ₜn). symmetry.
    apply aeq_perm_action1_neither. assumption. fsetdec.
    rewrite <- (swap_neither b d a) at 1; [idtac | assumption | fsetdec].
    symmetry. apply T1.
  - apply aeq_perm_action1_cancel2; simpl in *.
    + subst c. admit. (* obvio, precisa do lema certo. *) 
    + fsetdec. 
Admitted. 

Lemma aeq_abs_body a m n: m ≡α n -> \a ⋅ m ≡α \a ⋅ n.
Proof. Admitted. (* Lema deveria estar em Alpha.v *)

Lemma subst_neq a p : forall m, a#(m) -> [a := p]m ≡α m.
Proof. 
  (* por algum motivo gen m; apply term_aeq_ind não funciona *)
  apply (@term_aeq_rect (fun m => (a#(m) -> [a := p]m ≡α m))).
  - simpl; intros. rewrite subst_aeq1 with (n := m).
    etransitivity. apply H0. rewrite aeq_support. eassumption. assumption.
    assumption. symmetry. assumption.
  - intros b ?; rewrite subst_var; destruct (a == b); subst; simplify; fsetdec.
  - intros; rewrite subst_app; constructor; [apply H | apply H0]; simplify.
  - exists ({{a}} ∪ support p); intros m b ? ? ?. symmetry.
    etransitivity. apply (aeq_abs_body _ _ ([a := p]m)).
    symmetry. apply H0. simpl in *. fsetdec.
    etransitivity. symmetry. apply subst_abs_neq. fsetdec. fsetdec.
    reflexivity.
Qed.

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
  - exists ({{a}} ∪ {{b}} ∪ support q ∪ support p ∪ support ([b := p]q)); intros m x ? IH.
    rewrite (subst_aeq1 _ (\x ⋅ [a := q] m)); [idtac | apply subst_abs_neq; fsetdec].
    etransitivity. apply subst_abs_neq; fsetdec.
    etransitivity. apply aeq_abs_body. apply IH.
    etransitivity. symmetry. apply subst_abs_neq; fsetdec.
    rewrite (subst_aeq1 _ ([b := p](\x ⋅ m))); [idtac | symmetry; apply subst_abs_neq; fsetdec].
    reflexivity.
Qed.
