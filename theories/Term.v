(** *λ calculus nominal *)
From FP Require Import Base Atom Permutation.

(** Lambda calculus terms *)
Inductive term: Set :=
| Var: atom -> term
| App: term -> term -> term
| Abs: atom -> term -> term.
Hint Constructors term: core.
Notation Λ := term.
(* Coercion Var : atom >-> Λ. *)

Declare Scope term_scope.
Delimit Scope term_scope with term.
Bind Scope term_scope with term.
Open Scope term_scope.

Notation " ' x " := (Var (x%atom)) (at level 60, format "'[' ' x ']'"): term_scope.
Notation " x × y " := (App (x%term) (y%term)) (at level 59, left associativity, format "'[' x  ×  y ']'"): term_scope.
Notation " \ x ⋅ y " := (Abs (x%atom) (y%term)) (at level 60, right associativity, format "'[' \ x  ⋅  y ']'"): term_scope.

Section TermProperties.
  Context (a b: atom) (m n p q: Λ).

  Lemma var_inj: 'a = 'b <-> a = b.
  Proof. split; introv H; inversion~ H. Qed.
  Hint Immediate var_inj: core.

  Lemma app_inj: m × n = p × q <-> m = p /\ n = q.
  Proof. split; introv H; inversion~ H; subst~. Qed.
  Hint Immediate app_inj: core.

  Lemma abs_inj: \a ⋅ m = \b ⋅ n <-> a = b /\ m = n.
  Proof. split; introv H; inversion~ H; subst~. Qed.
  Hint Immediate abs_inj: core.
End TermProperties.


(** *Swap action on terms  *)
Fixpoint action a b t: Λ :=
  match t with
  | 'x => '(a ∙ b)ₐ x
  | m × n => action a b m × action a b n
  | \x ⋅ m => \(a ∙ b)ₐ x ⋅ action a b m
  end.
Notation " ( a ∙ b )ₜ t " := (action (a%atom) (b%atom) (t%term)) (at level 0, right associativity, format "( a  ∙  b )ₜ t"): term_scope.

Section ActionProperties.
  Context (a b c d: atom) (m n: Λ).

  Lemma action_id: (a ∙ a)ₜ m = m.
  Proof.
    induction m as [| ? IH1 ? IH2 | ? ? IH]; simpls; autorewrite with nominal;
      [| rewrite IH1, IH2 | rewrite IH]; auto.
  Qed.

  Lemma action_distr: (a ∙ b)ₜ (c ∙ d)ₜ m = ((a ∙ b)ₐ c ∙ (a ∙ b)ₐ d)ₜ (a ∙ b)ₜ m.
  Proof.
    induction m as [| ? IH1 ? IH2 | ? ? IH]; intros; simpls;
      [ rewrite swap_distr | rewrite IH1, IH2 | rewrite swap_distr, IH]; auto.
  Qed.

  Lemma action_switch: (a ∙ b)ₜ m = (b ∙ a)ₜ m.
  Proof.
    induction m as [| ? IH1 ? IH2 | ? ? IH]; intros; simpls;
      [ rewrite swap_switch | rewrite IH1, IH2 | rewrite swap_switch, IH]; auto.
  Qed.

  Lemma action_involutive: (a ∙ b)ₜ (a ∙ b)ₜ m = m.
  Proof.
    induction m as [| ? IH1 ? IH2 | ? ? IH]; intros; simpls; autorewrite with nominal;
      [| rewrite IH1, IH2 | rewrite IH]; auto.
  Qed.

  Lemma action_injective: (a ∙ b)ₜ m = (a ∙ b)ₜ n -> m = n.
  Proof.
    generalize n as n'; induction m as [| ? IH1 ? IH2 | ? ? IH]; intros ? H; destruct n';
      simpls; try congruence.
    - apply var_inj in H; apply var_inj; eapply swap_injective; eauto.
    - apply app_inj in H as []; erewrite IH1, IH2; eauto.
    - apply abs_inj in H as [A ?]; apply swap_injective in A; subst; erewrite IH; eauto.
  Qed.
End ActionProperties.

Hint Rewrite action_id action_involutive: nominal.
Hint Immediate action_injective: core.

(** *Permutation (swap composition) action on terms *)
Definition perm_action (prm: Π) (trm: Λ): Λ := fold_right (fun a t => (fst a ∙ snd a)ₜ t) trm prm.
Notation "p ∙ₜ t" := (perm_action p (t%term)) (at level 60, right associativity, format "p  ∙ₜ  t"): term_scope.

Section ActionPermutation.
  Context (a b: atom) (p q: Π) (m n: Λ).

  (* Exist algum caso que precisamos dessa equivalencia? *)
  Lemma perm_action_action: [(a,b)] ∙ₜ m = (a ∙ b)ₜ m. Proof. auto. Qed.

  (* Similar ao caso acima, precisamos dessa equivalencia? *)
  Lemma perm_action_id: [(a,a)] ∙ₜ m = m.
  Proof. simpl; apply action_id. Qed.

(* Lemas posteriores precisam que estes lemas sejam transparentes para poderem reduzir
     suas definições. *)
  Lemma perm_action_empty: forall t, [] ∙ₜ t = t.
  Proof. auto. Defined.

  Lemma perm_action_var: p ∙ₜ ('a) = '(p ∙ₐ a).
  Proof. induction p as [| [] ? IH]; simpl; [| rewrite IH]; auto. Defined.

  Lemma perm_action_app: p ∙ₜ (m × n) = (p ∙ₜ m) × (p ∙ₜ n).
  Proof. induction p as [| [] ? IH]; simpls; [| rewrite IH]; auto. Defined.

  Lemma perm_action_abs: p ∙ₜ (\a ⋅ m) = \(p ∙ₐ a) ⋅ (p ∙ₜ m).
  Proof. induction p as [| [] ? IH]; simpls; [| rewrite IH]; auto. Defined.

  Lemma perm_action_concat: (p ++ q) ∙ₜ m = p ∙ₜ (q ∙ₜ m).
  Proof. induction p as [| [] ? IH]; intros; simpls~; rewrite~ IH. Defined.

  Lemma perm_action_action_distr: p ∙ₜ (a ∙ b)ₜ m = (p ∙ₐ a ∙ p ∙ₐ b)ₜ (p ∙ₜ m).
  Proof. induction p as [| [] ? IH]; intros; simpls; [| rewrite IH, action_distr]; auto. Qed.

  Lemma perm_action_injective: p ∙ₜ m = p ∙ₜ n -> m = n.
  Proof.
    induction p as [| [] ? IH]; intros H; simpls; subst~; apply action_injective in H; auto.
  Qed.
End ActionPermutation.

Hint Rewrite perm_action_action perm_action_id perm_action_empty: nominal.
Hint Rewrite perm_action_var perm_action_app perm_action_abs: nominal.
Hint Immediate perm_action_injective: core.

(** *λ terms support *)
(* See Pitts Nominal Sets for proof. *)
Fixpoint support (t: Λ): aset :=
  match t with
  | 'x => {{x}}
  | m × n => (support m) ∪ (support n)
  | \a ⋅ m => a \ (support m)
  end.

Local Open Scope aset_scope.
Notation " a #( x ) " := (a ∉ support x) (at level 65, format "a #( x )"): aset_scope.
Notation " a #( x , y ) " := (a ∉ (support x ∪ support y)) (at level 65, format "a #( x ,  y )"): aset_scope.
Notation " a #( x , y , z ) " := (a ∉ (support x ∪ support y ∪ support z)) (at level 65, format "a #( x ,  y ,  z )"): aset_scope.

(* Antiga regra recursiva começou a falhar: Erro variáveis x e y precisam estar no mesmo escopo? *)
(* (a ∉ ((support b ∪ .. support c ∪ ..) ∪ (support d ..))) *)
(*   (at level 65, format "a #( b ,  .. ,  c ,  d )"): aset_scope. *)

Hint Extern 4 (_ #(\_ ⋅ _)) => simpls; apply~ notin_remove_2: core.
Hint Extern 4 (_ #(\_ ⋅ _)) => simpls; apply~ notin_remove_1: core.

Section SupportProperties.
  Context (a b c: atom) (p: Π) (m n: Λ).

  (* Lemma support_fresh2: a#(m) -> a#(n) -> a#(m, n). *)
  (* Proof. apply notin_union_3. Qed. *)

  Lemma binder_fresh_support_abs: a#(\a⋅m).
  Proof. intros; simpls~. Qed.

  Lemma fresh_body_fresh_abs: a#(m) -> a#(\b⋅m).
  Proof. intros; simpls~. Qed.

  Lemma action_fresh_left: a <> b -> b#(m) -> a#((a ∙ b)ₜ m).
  Proof.
    intros ? H; induction m; simpls;
      [apply swap_notin_singleton1 | idtac
       | apply notin_remove_1 in H as []; subst; [autorewrite with nominal| idtac]]; fsetdec.
  Qed.

  Lemma action_fresh_right: a <> b -> b#(m) -> a#((b ∙ a)ₜ m).
  Proof. intros; rewrite action_switch; apply action_fresh_left; auto. Qed.

  Lemma action_fresh_both: a <> b -> a <> c -> a#(m) -> a#((b ∙ c)ₜ m).
  Proof.
    induction m; introv ? ? H3; simpls.
    - apply swap_notin_singleton; fsetdec.
    - apply notin_union_3; [apply IHt1 | apply IHt2]; fsetdec.
    - apply notin_remove_1 in H3 as []; subst; auto; apply notin_remove_3, swap_neither; auto.
  Qed.

  Lemma perm_action_fresh: a ∉ atoms p -> a#(m) -> a#(p ∙ₜ m).
  Proof.
    gen p; induction m as [| ? IH1 ? IH2 | ? ? IH]; introv ? H2; simpls.
    - rewrite perm_action_var; simpl; apply perm_atom_notin_singleton; fsetdec.
    - autorewrite with nominal; simpls; apply notin_union_3; [apply IH1 | apply IH2]; fsetdec.
    - rewrite perm_action_abs; simpls; apply notin_remove_1 in H2 as []; subst; auto;
        apply notin_remove_3; autorewrite with nominal; rewrite~ perm_atom_notin_eq.
  Qed.


End SupportProperties.

(* Resolve casos triviais de frescor. *)
Ltac solve_fresh :=
  match goal with
  | _: _ |- ?a #((?a ∙ ?b)ₜ _) => apply action_fresh_left
  | _: _ |- ?a #((?b ∙ ?a)ₜ _) => apply action_fresh_right
  | _: _ |- ?a #((?b ∙ ?c)ₜ _) => apply action_fresh_both
  | _: _ |- _ #(_ ∙ₜ _) => apply perm_action_fresh
  end.

(* a #( m ) = a ∉ ( m ) *)
Hint Extern 3 (_ ∉ ( _ )) => simpl; try solve_fresh; simpl; try fsetdec: core.

(* Coleciona variáveis para frescor *)
Ltac gather_atoms ::=
	let A := gather_atoms_with (fun x: atom => {{x}}) in
  let C := gather_atoms_with (fun x: Λ    => support x) in
  let B := gather_atoms_with (fun x: Π    => atoms x) in
  let D := gather_atoms_with (fun x: aset => x) in
	constr:(A ∪ B ∪ C ∪ D).
