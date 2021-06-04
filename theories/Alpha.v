From FP Require Import Base Atom Permutation Term NominalRec.
Local Open Scope aset_scope.

(**  *α equivalence *)
Reserved Notation "a ≡α b" (at level 61).
Inductive aeq: Λ -> Λ -> Prop :=
| AeqVar: forall a, 'a ≡α 'a
| AeqApp: forall m n p q, m ≡α p -> n ≡α q -> (m × n) ≡α (p × q)
| AeqAbs: forall L a b m n, (forall c, c ∉ L -> (a ∙ c)ₜ m ≡α (b ∙ c)ₜ n) -> \a ⋅ m ≡α \b ⋅ n
where "a ≡α b" := (aeq (a%term) (b%term)).
Hint Constructors aeq: core.

Inductive aeq2: Λ -> Λ -> Prop :=
| AeqVar2: forall a, aeq2 ('a) ('a)
| AeqApp2: forall m n p q, aeq2 m p -> aeq2 n q -> aeq2 (m × n) (p × q)
| AeqAbs21: forall a b m n, a <> b -> a#(n) -> aeq2 m ((a ∙ b)ₜ n) -> aeq2 (\a ⋅ m) (\b ⋅ n)
| AeqAbs22: forall a m n, aeq2 m n -> aeq2 (\a ⋅ m) (\a ⋅ n).

Lemma aeq2_perm p m n: aeq2 m n -> aeq2 (p ∙ₜ m) (p ∙ₜ n).
Proof. Admitted.
Lemma aeq2_cancel a b c m: b#(m) -> c#(m) -> aeq2 ((c ∙ b)ₜ (a ∙ c)ₜ m) ((a ∙ b)ₜ m).
Proof. Admitted.
Lemma aeq2_trans: Transitive aeq2.
Proof. Admitted.
Lemma aeq_perm p m n: m ≡α n -> (p ∙ₜ m) ≡α (p ∙ₜ n).
Proof. Admitted.
Lemma aeq_perm_action1_cancel a b c m: b#(m) -> c#(m) -> (c ∙ b)ₜ (a ∙ c)ₜ m ≡α (a ∙ b)ₜ m.
Proof. Admitted.
Lemma aeq_trans: Transitive aeq.
Proof. Admitted.
Lemma aeq_support1 a m n: a#(m) -> m ≡α n -> a#(n).
Proof. Admitted.
Lemma dec2 a b c m: a <> b -> a <> c ->  a#((b ∙ c)ₜ m) -> a#(m).
Proof. Admitted.
Lemma action_neither a b m: a <> b -> a#(m) -> b#(m) -> (a ∙ b)ₜ m = m.
Proof. Admitted.

Section LOL.
  Import MSetDecideAuxiliary.

  Lemma aeqs m n: m ≡α n <-> aeq2 m n.
  Proof.
    split.
    - induction 1.
      + constructor.
      + constructor; auto.
      + destruct (a == b); subst.
        * apply AeqAbs22; pick fresh z; lets: (aeq2_perm [(b,z)]); simpls;
            assert (Hz: z ∉ L). fsetdec.
          specialize (H0 _ Hz); apply (aeq2_perm [(b,z)]) in H0; simpls;
            do 2 rewrite action_involutive in H0; auto.
        * destruct (dec_In a (support m)); pick fresh z.
          -- assert (HH1: a#((a ∙ z)ₜ m)).
             { apply action_fresh_left. fsetdec. fsetdec. }
             assert(HH2: z ∉ L).
             { fsetdec. }.
             specialize (H _ HH2).
             apply (aeq_support1 _ _ _ HH1) in H.
             assert (HH3: a <> z).
             { fsetdec. }
             apply (dec2 _ _ _ _ n0 HH3) in H.
             apply AeqAbs21. auto. auto. specialize (H0 _ HH2).
             apply (aeq2_perm [(a,z)]) in H0; simpls;
               rewrite action_involutive in H0; rewrite action_switch in H0.
             eapply aeq2_trans.
             ++ apply H0.
             ++ rewrite (action_switch a b). apply aeq2_cancel. auto. fsetdec.
          -- assert (Hz: z ∉ L). fsetdec.
             specialize (H _ Hz); rewrite action_neither in H; try fsetdec.
             apply (aeq_support1 _ _ _ H1) in H.
             assert (HH1: a <> z).
             { fsetdec. }
             apply (dec2 _ _ _ _ n0 HH1) in H.
             apply AeqAbs21. auto. fsetdec.
             specialize (H0 _ Hz). apply (aeq2_perm [(a,z)]) in H0; simpls.
             rewrite action_involutive in H0. rewrite action_switch in H0.
             eapply aeq2_trans.
             ++ apply H0.
             ++ rewrite (action_switch a b). apply aeq2_cancel. auto. fsetdec.
    - induction 1.
      + auto.
      + auto.
      + constructor 3 with (support n); intros; rewrite action_switch in IHaeq2;
          apply (aeq_perm [(a,c)]) in IHaeq2; simpls.
        lets: aeq_trans; unfold Transitive in *. specialize (H3 ((a ∙ c)ₜm) ((a ∙ c)ₜ(b ∙ a)ₜn)).
        apply H3; auto. apply aeq_perm_action1_cancel; auto.
      + constructor 3 with ∅; intros; lets: (aeq_perm ([(a,c)])); simpls; auto.
  Qed.
End LOL.

Lemma aeq_perm m n p: m ≡α n -> (p ∙ₜ m) ≡α (p ∙ₜ n).
Proof.
  induction 1 as [| | ? ? ? ? ? ? IH]; intros; simpls; autorewrite with nominal; auto.
    apply fresh AeqAbs with z; rewrite <- (perm_atom_notin_eq p z); auto;
      do 2 rewrite <- perm_action_action_distr; apply~ IH.
Qed.
Hint Resolve aeq_perm: core.

Lemma aeq_support: forall m n, m ≡α n -> support m [=] support n.
Proof. Admitted.
  (* induction 1. *)
  (* - admit. *)
  (* - admit. *)
  (* - simpl in *. (a ∙ b) (a \ T) -> ((a ∙ b)a \ (a ∙ b)T) *)

  (*   unfold "[=]"; intro w; split; intros; simpls. *)
  (*   +  *)

Instance aeq_refl: Reflexive aeq.
Proof.
  intros t; induction t; try constructor~; apply fresh AeqAbs; intros.
  apply (aeq_perm _ _ [(_,_)]); auto.
Qed.
Hint Resolve aeq_refl: core.

Instance aeq_sym: Symmetric aeq.
Proof. introv AEQ; induction AEQ; intros; try econstructor; eauto. Qed.

Instance aeq_trans: Transitive aeq.
Proof.
  intros ? ? z H; gen z; induction H; simpl; auto; introv HH; inversions HH.
  - constructor~.
  - apply fresh AeqAbs; eauto.
Qed.

Instance aeq_equiv: Equivalence aeq.
Proof. split; typeclasses eauto. Qed.

(** *Alpha conversion and freshness *)
Lemma aeq_perm_action1_cancel a b c m: b#(m) -> c#(m) -> (c ∙ b)ₜ (a ∙ c)ₜ m ≡α (a ∙ b)ₜ m.
Proof.
  destruct (a == b), (a == c), (b == c); subst; try (intros HB HC; autorewrite with nominal); auto;
    try rewriten (action_switch b c); auto.
  gen a b c; induction m as [| | t ? IH] using nominal_ind; intros a b ? HB c ? ? HC; simpls.
  - rewrite swap_cancel; fsetdec.
  - constructor; [apply IHm1 | apply IHm2]; fsetdec.
  - apply notin_remove_1 in HB as []; apply notin_remove_1 in HC as []; subst;
      autorewrite with nominal; auto.
    + rewriten (swap_neither a c b); auto; apply fresh AeqAbs;
        rewriten (action_distr c b a c); rewriten (action_distr a b c b);
          rewrite (action_switch c a); apply (IH [(_,_)]); auto; fsetdec.
    + apply fresh AeqAbs; rewriten (action_distr c b a c);
        rewriten (action_distr a b c b); apply (IH [(_,_)]); auto; fsetdec.
    + destruct (a == t), (b == t), (c == t); subst; simpls; autorewrite with nominal; auto; try congruence.
      * autorewrite with nominal; apply fresh AeqAbs with z.
        rewriten (action_distr b z t b); rewriten (action_distr b z c b);
          rewriten (action_distr b z t c); apply (IH [(_,_)]); auto; fsetdec.
      * rewriten (swap_neither a c t); auto; apply fresh AeqAbs with z;
          rewriten (action_distr c t a c); rewriten (action_distr a t c t);
            rewrite (action_switch c a); apply (IH [(_,_)]); auto; fsetdec.
      * autorewrite with nominal; apply fresh AeqAbs with z.
        rewriten (action_distr t b a t); rewriten (action_distr a b t b);
          apply (IH [(_,_)]); auto; fsetdec.
      * autorewrite with nominal; apply fresh AeqAbs with z;
          rewriten (action_distr t z c b); rewriten (action_distr t z a c);
            rewriten (action_distr t z a b); apply (IH [(_,_)]); auto; fsetdec.
Qed.
Hint Resolve aeq_perm_action1_cancel: core.

Lemma aeq_perm_action1_cancel1 a b c m: b#(\a ⋅ m) -> c#(m) -> (c ∙ b)ₜ (a ∙ c)ₜ m ≡α (a ∙ b)ₜ m.
Proof. Admitted.

Lemma aeq_perm_action1_neither a b m: a#(m) -> b#(m) -> (a ∙ b)ₜ m ≡α m.
Proof.
  gen a b; induction m using nominal_ind; simpl.
  - intros; autorewrite with nominal; auto.
  - intros; constructor; auto.
  - intros c z Hc Hz; destruct (c == z); subst; autorewrite with nominal; auto.
    + apply notin_remove_1 in Hc as []; apply notin_remove_1 in Hz as []; subst; autorewrite with nominal; auto.
      * apply fresh AeqAbs;
          do 2 rewriten (action_distr); apply (H [(_,_)]); auto.
      * apply fresh AeqAbs with w;
          do 2 rewriten action_distr; rewrite (action_switch w z); apply (H [(_,_)]); auto.
      * destruct (c == a), (z == a); subst; try congruence; autorewrite with nominal; apply fresh AeqAbs; auto.
        -- rewrite (action_switch c a); auto.
        -- rewriten action_distr; apply (H [(_,_)]); auto.
Qed.
Hint Resolve aeq_perm_action1_neither: core.

Lemma aeq_abs_perm b a m: b#(\a ⋅ m) -> \a⋅m ≡α \b⋅ ((a ∙ b)ₜ m).
Proof.
  intros; simpls; destruct (a == b); subst; autorewrite with nominal; auto;
    apply fresh AeqAbs; symmetry; auto.
Qed.
Hint Resolve aeq_abs_perm: core.

Lemma aeq_abs_perm1 b a m: b#(m) -> \a⋅m ≡α \b⋅ ((a ∙ b)ₜ m).
Proof.
  intros; simpls; destruct (a == b); subst; autorewrite with nominal; auto;
    apply fresh AeqAbs; symmetry; auto.
Qed.

(** *α Compatibility *)
Definition αCompat (P: Λ -> Type) := forall m n, m ≡α n -> P m -> P n.
Definition αStrongCompat {A: Type} (P: Λ -> A) := forall m n, m ≡α n -> P m = P n.
Arguments αCompat /P.
Arguments αStrongCompat {A} /P.

(** *α structural iteration *)
Lemma abs_aeq_rename:
  forall P: Λ -> Type, αCompat P -> forall L,
      (forall b m, b ∉ L -> (forall p, P (p ∙ₜ m)) -> P (\b ⋅ m)) ->
      forall a m, (forall p, P (p ∙ₜ m)) -> P (\a ⋅ m).
Proof.
  intros ? Pa L HL a M H; set (z := fresh (support (\a ⋅ M) ∪ L)); apply Pa with (\z ⋅ (a ∙ z)ₜ M).
  - apply aeq_sym; apply aeq_abs_perm; lets: (fresh_spec (support (\a ⋅ M) ∪ L)); fsetdec.
  - apply HL.
    + lets: (fresh_spec (support (\a ⋅ M) ∪ L)); fsetdec.
    + intros; pose proof (perm_action_concat p [(a,z)]) as C.  simpl in *; rewrite <- C; apply H.
Defined.

(* BVC *)
Definition term_aeq_rect:
  forall P: Λ -> Type,
    αCompat P ->
    (forall a, P ('a)) ->
    (forall m n, P m -> P n -> P (m × n)) ->
    {L & forall m a, a ∉ L -> P m -> P (\a ⋅ m)} ->
    forall m, P m.
Proof.
  introv ? Hv Happ [L HL]; apply nominal_rect.
  - admit.
  - admit.
  - intros; apply abs_aeq_rename with L.
  [apply Hv | apply Happ | apply abs_aeq_rename with L].
    auto; introv ? HP. apply HL; [| apply (HP [])]; auto.
Defined.

Definition term_aeq_rec := (fun P: Λ -> Set => term_aeq_rect P).
Definition term_aeq_ind := (fun P: Λ -> Prop => term_aeq_rect P).

(* BVC Iterator *)
Definition LIt {A: Type} (hv: atom -> A) (hp: A -> A -> A)
           (fabs: atom -> A -> A) (L: aset) (l: Λ): A :=
  term_aeq_rect (fun _ => A) (fun _ _ _ => id) hv (fun _ _ => hp)
                (existT _ L (fun _ b _ r => fabs b r)) l.

(* Iterator properties *)
Lemma LIt_var {A} a fvar fapp fabs L: @LIt A fvar fapp fabs L ('a) = fvar a.
Proof. lazy. auto. Defined.

Lemma LIt_app {A} a b fvar fapp fabs L:
  @LIt A fvar fapp fabs L (a × b) = fapp (@LIt A fvar fapp fabs L a)
                                         (@LIt A fvar fapp fabs L b).
Proof. lazy; auto. Defined.

(* term_aeq_rect fully unfolded (excluding names below) *)
Definition term_aeq_aux A (fvar: atom -> A) (fapp: A -> A -> A) (fabs: atom -> A -> A) L M p :=
  term_rect (fun _ => forall p, A) (var_nominal_rec _ fvar) (app_nominal_rec _ (fun _ _ => fapp))
            (abs_nominal_rec _
                             (abs_aeq_rename (fun _ => A)
                                             (fun _ _ _ => id)
                                             L
                                             (fun b _ _ f => fabs b (f []))))
            M p.

Definition term_aeq_aux_perm_eq A fvar fapp L fabs M :=
  forall p: Π, term_aeq_aux A fvar fapp fabs L M p = term_aeq_aux A fvar fapp fabs L (p ∙ₜ M) [].

Lemma LIt_abs_aux A (fvar: atom -> A) (fapp: A -> A -> A) (fabs: atom -> A -> A) L:
  forall M p, term_aeq_aux A fvar fapp fabs L M p = term_aeq_aux A fvar fapp fabs L (p ∙ₜ M) [].
Proof.
  intros; gen p; induction M as [| ? ? IH1 IH2 |] using nominal_ind; intros.
  - autorewrite with nominal; lazy [term_aeq_aux var_nominal_rec eq_rect_r eq_rect]; simpl;
      case (eq_sym (perm_action_var t p)). (* automatizar esse paço? *) auto.
  - autorewrite with nominal; lazy [term_aeq_aux app_nominal_rec eq_rect_r eq_rect] in *;
      simpl in *; case (eq_sym (perm_action_app p M1 M2)); f_equal; auto.
  - autorewrite with nominal; lazy [term_aeq_aux abs_nominal_rec abs_aeq_rename eq_rect_r eq_rect];
      simpl; case (eq_sym (perm_action_abs a p M)).
    set (z := fresh (((p ∙ₐ a) \ support (p ∙ₜ M)) ∪ L)); fequal.
    assert (T1: term_aeq_aux A fvar fapp fabs L M ((p ∙ₐ a, z) :: p) =
                term_aeq_aux A fvar fapp fabs L (((p ∙ₐ a, z) :: p) ∙ₜ M) []). {
      specialize (H [] ((p ∙ₐ a, z) :: p)); simpl in *; auto. }
    assert (T2: term_aeq_aux A fvar fapp fabs L (((p ∙ₐ a, z) :: p) ∙ₜ M) [] =
                term_aeq_aux A fvar fapp fabs L (p ∙ₜ M) [(p ∙ₐ a, z)]). {
      specialize (H p [(p ∙ₐ a, z)]); simpl in *; symmetry; auto. }
    eapply eq_trans; eauto.
Qed.

[A]X => (a)(λ a . ax)
f2: [A]X -> Y
f1: (A × X) -> Y

                             TemplateCoq => MetaCoq

Lemma LIt_abs {A} a M (fvar: atom -> A) (fapp: A -> A -> A)
      (fabs: atom -> A -> A) L:
  @LIt A fvar fapp fabs L (\a ⋅ M) =
  let z := fresh (support (\a ⋅ M) ∪ L) in
  fabs z (@LIt A fvar fapp fabs L ([(a,z)] ∙ₜ M)).
Proof.
  lazy [LIt term_aeq_rect nominal_rect abs_nominal_rec abs_aeq_rename eq_rect_r eq_rect id];
    simpl; fequal; apply LIt_abs_aux.
Defined.

Lemma LIt_StrongCompat {A} fvar fapp fabs L:
  αStrongCompat (@LIt A fvar fapp fabs L).
Proof.
  simpl in *; intros m n HAEQ; gen n; induction m as [| | a n] using nominal_ind; intros;
    inversion HAEQ as [| ? ? p q | G ? b ? m HH]; subst.
  - auto.
  - do 2 rewrite LIt_app; rewrite (IHm1 p), (IHm2 q); auto.
  - do 2 rewrite LIt_abs.
    assert (A1: support (\a ⋅ n) ∪ L [=] support (\b ⋅ m) ∪ L).
    { apply aeq_support in HAEQ; rewrite HAEQ; apply equal_refl. }
    assert (A2: fresh (support (\a ⋅ n) ∪ L) = fresh (support (\b ⋅ m) ∪ L)).
    { rewrite (fresh_set_eq _ _ A1); auto. }
    fequal; auto; rewrite A2; set (z := fresh (support (\_ ⋅ _) ∪ _)).
      pick fresh w for (G ∪ support m ∪ support n); apply H; simpls.
    assert (T1: (a ∙ z)ₜn ≡α (w ∙ z)ₜ(a ∙ w)ₜ n).
    { symmetry; apply aeq_perm_action1_cancel1; [subst z; rewrite <- A2 | fsetdec]. admit. }
    assert (T2:  (w ∙ z)ₜ(b ∙ w)ₜ m ≡α (b ∙ z)ₜ m).
    { apply aeq_perm_action1_cancel1; [| fsetdec]. admit. }
    eapply (aeq_perm _ _ [(w, z)]) in HH; simpls;
      [apply (aeq_trans _ _ _ T1 (aeq_trans _ _ _ HH T2)) |]; auto.
Admitted.
