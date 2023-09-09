(** *Swap based permutation *)
Require Import Base Atom.

Local Set Warnings "-deprecated-hint-without-locality -deprecated-instance-without-locality -deprecated-hint-rewrite-without-locality".

(* Swap function *)
Definition swap (a b: atom): atom -> atom :=
  fun c => if a == c then b else if b == c then a else c.

(* "For the sake of factorization with Coq predefined rules, simple rules have to be observed for notations starting with a symbol, e.g., rules starting with “{” or “(” should be put at level 0." https://coq.inria.fr/distrib/current/refman/user-extensions/syntax-extensions.html#simple-factorization-rules *)
Declare Scope atom_scope.
Delimit Scope atom_scope with atom.
Bind Scope atom_scope with atom.
Notation "( a ∙ b )ₐ c" :=
  (swap (a%atom) (b%atom) (c%atom)) (at level 0, right associativity, format "( a ∙ b )ₐ  c"): atom_scope.
Open Scope atom_scope.

(* Swap properties *)
Create HintDb nominal discriminated.

Section SwapProperties.
  Context (a b c d e: atom).

  Lemma swap_id: (a ∙ a)ₐ b = b.
  Proof. unfold swap; simplify. Qed.

  Lemma swap_involutive: (a ∙ b)ₐ (a ∙ b)ₐ c = c.
  Proof. unfold swap; simplify. Qed.

  Lemma swap_left: (a ∙ b)ₐ a = b.
  Proof. unfold swap; simplify. Qed.

  Lemma swap_right: (a ∙ b)ₐ b = a.
  Proof. unfold swap; simplify. Qed.

  Lemma swap_neither: c <> a -> c <> b -> (a ∙ b)ₐ c = c.
  Proof. unfold swap; simplify. Qed.

  Lemma swap_switch: (a ∙ b)ₐ c = (b ∙ a)ₐ c.
  Proof. unfold swap; simplify. Qed.

  (* SLOW *)
  Lemma swap_distr: (a ∙ b)ₐ (c ∙ d)ₐ e = ( (a ∙ b)ₐ c ∙ (a ∙ b)ₐ d )ₐ (a ∙ b)ₐ e.
  Proof. unfold swap; simplify. Qed.

  Lemma swap_cancel: b <> d -> c <> d -> (c ∙ b)ₐ (a ∙ c)ₐ d = (a ∙ b)ₐ d.
  Proof. unfold swap; simplify. Qed.

  Lemma swap_neq: a <> d -> b <> d -> c <> d -> (a ∙ b)ₐ c <> d.
  Proof. intros; unfold swap; simplify. Qed.

  Lemma swap_neq1: a <> b -> b <> c -> (a ∙ b)ₐ c <> a.
  Proof. intros; unfold swap; simplify. Qed.

  (** *Swap is a permutation. *)
  (* swap a b is a permutation form atom to atom and Bijective thus a permutation. *)
  Lemma swap_injective: forall x y, (a ∙ b)ₐ x = (a ∙ b)ₐ y -> x = y.
  Proof. repeat intro; unfolds swap; simplify; congruence. Qed.

  Lemma swap_surjective: exists x, (a ∙ b)ₐ x = c.
  Proof. exists ((a ∙ b)ₐ c). apply swap_involutive. Qed.
End SwapProperties.

Hint Rewrite swap_id swap_involutive swap_left swap_right: nominal.
Hint Rewrite swap_neither swap_cancel using (solve [congruence | fsetdec]): nominal.
Hint Resolve swap_neq swap_neq1: core.
Hint Immediate swap_injective: core.

Section SwapSetProperties.
  (* Import SetNotations. *)
  Local Open Scope aset_scope.
  Context (a b c d: atom).

  Lemma swap_notin_singleton: a <> b -> a <> c -> a <> d -> a ∉ {{(b ∙ c)ₐ d}}.
  Proof. intros; unfold swap; simplify. Qed.

  Lemma swap_notin_singleton1: a <> b -> b <> c -> a ∉ {{(a ∙ b)ₐ c}}.
  Proof. intros; unfold swap; simplify. Qed.
End SwapSetProperties.

Hint Resolve swap_notin_singleton swap_notin_singleton1: core.

(* Prevent simplification from unfolding *)
Global Opaque swap.

(** *Perm (swap composition) *)
Notation Π := (list (atom * atom)).

Definition perm_atom (prm: Π): atom -> atom := fun atm => fold_right (fun p a => ((fst p) ∙ (snd p))ₐ a) atm prm.
Definition perm_atom_inv (p: Π): atom -> atom := fun a => perm_atom (rev p) a.

Notation " p ∙ₐ a " := (perm_atom p (a%atom)) (at level 60, right associativity, format "p  ∙ₐ  a"): atom_scope.
Notation " p ∙ₐ⁻ a " := (perm_atom_inv p (a%atom)) (at level 60, right associativity, format "p  ∙ₐ⁻  a"): atom_scope.

Section Atoms.
  (* Import SetNotations. *)
  Local Open Scope aset_scope.

  Definition atoms (prm: Π): aset :=
    fold_right (fun (p: atom * atom) a => {{(fst p)}} ∪ {{(snd p)}} ∪ a) ∅ prm.
  Hint Extern 4 (_ ∉ (atoms _)) => simpls; fsetdec: core.

  Section PermutationProperties.
    Context (p q: Π) (a b c: atom).

    Lemma perm_atom_distr: p ∙ₐ (a ∙ b)ₐ c = ((p ∙ₐ a) ∙ (p ∙ₐ b))ₐ (p ∙ₐ c).
    Proof. induction p as [| ? ? IH]; intros; simpls~; rewrite IH, swap_distr; auto. Qed.

    Lemma perm_atom_comp_concat: (p ++ q) ∙ₐ a = p ∙ₐ q ∙ₐ a.
    Proof. induction p as [| [] ? IH]; intros; simpls~; rewrite~ IH. Qed.

    Lemma perm_atom_notin_neq: a <> b -> a ∉ atoms p -> p ∙ₐ b <> a.
    Proof. induction p; intros; simplify; apply swap_neq; fsetdec. Qed.

    Lemma perm_atom_notin_singleton: a ∉ atoms p -> a <> b -> a ∉ {{p ∙ₐ b}}.
    Proof. intros; apply notin_singleton_2; apply perm_atom_notin_neq; auto. Qed.

    Lemma perm_atom_notin_eq: a ∉ atoms p -> p ∙ₐ a = a.
    Proof.
      induction p as [| [] ? IH]; intros; simpls; auto; rewrite IH, swap_neither; fsetdec.
    Qed.
  End PermutationProperties.
End Atoms.

Hint Resolve perm_atom_notin_neq perm_atom_notin_singleton: core.

(** *Atom perm is a permutation *)
(* Swap is a finite permutation. Composition of swap is a finite permutation.
 Theorem 1.15 NominalSets. *)
Section PermutationPermutation.
  Context (p: Π) (a b: atom).

  Lemma perm_atom_right_inv: p ∙ₐ p ∙ₐ⁻ a = a.
	Proof.
	  gen a; induction p as [| [] ? IH]; intros; unfolds perm_atom_inv; simpls; auto;
      rewrite (perm_atom_comp_concat); rewrite~ IH; apply swap_involutive.
	Qed.

  Lemma perm_atom_injective: p ∙ₐ a = p ∙ₐ b -> a = b.
  Proof. induction p as [| ? ? IH]; intros H; simpls~; apply swap_injective in H; auto. Qed.

  Lemma perm_atom_surjective: exists x, p ∙ₐ x = a.
  Proof. eexists; eapply perm_atom_right_inv. Qed.
End PermutationPermutation.

Hint Rewrite  perm_atom_right_inv: nominal.
Hint Immediate perm_atom_injective: core.