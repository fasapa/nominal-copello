(* Implementação de átomos baseada na biblioteca Metalib do Grupo de Linguagens de
   Programação da Universidade da Pensilvânia.

   https://www.cis.upenn.edu/~plclub/
   https://github.com/plclub/metalib *)

Require Import Base.
From Coq Require Import Arith Arith.PeanoNat MSets.

(** *Nomes Atômicos *)
(** Átomos são identificadores, sua estrutura é irrelevante (opaca). As únicas propriedades de
    interesse que nomes devem possuir são:
    - Sempre podemos obter um átomo novo dado um conjunto de átomos (infinito).
    - Distinguíveis, ou seja, a igualdade entre átomos é decidível.

    Implementamos átomos como módulos de interface opaca (estrutura irrelevante). A igualdade
    é definida como a igualdade padrão (usual) do Coq decidível: igualdade de Leibniz.
    "Leibniz equality is a relation and every function
    is a morphism that respects Leibniz equality."
    https://coq.inria.fr/refman/addendum/generalized-rewriting.html
    Check eq_rect. *)

Module Type ATOM <: UsualDecidableType.

  (* Implementação de átomo é opaca. *)
  (* Parameter atom : Set. *)
  Parameter t: Set.
  (* Definition t := atom. *)

  (* Distinguíveis *)
  Parameter eq_dec : forall x y: t, {x = y} + {x <> y}.

  (* Infinitos: sempre podemos obter um átomo novo dado um conjunto. *)
  Parameter fresh_from_list :
      forall (xs : list t), {x : t | ~ List.In x xs}.

  (* atom_fresh obtem um átomo novo. *)
  Parameter fresh: list t -> t.

  Parameter fresh_notin_list : forall l, ~ In (fresh l) l.

  (* HasUsualEq: iguladade de Leibniz (usual) para átomos.
     UsualIsEq: iguladade entre átomos é uma relação de equivalência. *)
  Include HasUsualEq <+ UsualIsEq.
End ATOM.

(* Import Arith.PeanoNat.Nat. *)
(** Implementação opaca de átomo. *)
Module Atom : ATOM.

  (* Definition atom := nat. *)
  Definition t := nat.
  Definition eq_dec := eq_nat_dec.

  (* Dado uma lista e naturais, podemos obter n tal que seja maior, ou igual, à qualquer elemento
     dessa lista. *)
  Lemma nat_list_max : forall xs : list nat, { n : nat | forall x, List.In x xs -> x <= n }.
  Proof.
    induction xs as [| x ? [y IH]].
    - exists 0. inversion 1.
    - exists (max x y); intros ? []; subst;
          [apply Nat.le_max_l | apply Nat.max_le_iff; right; apply IH]; auto.
  Qed.

  (* Existe um natural que não está contido na lista. *)
  Lemma fresh_from_list : forall xs, {x: t | ~ List.In x xs}.
  Proof.
    intros xs; destruct (nat_list_max xs) as [x H].
    exists (S x); intros F; apply H in F; apply Nat.nle_succ_diag_l in F; auto.
  Qed.

  Definition fresh l := proj1_sig (fresh_from_list l).

  Lemma fresh_notin_list: forall l, ~ In (fresh l) l.
  Proof. intros; unfold fresh; destruct (fresh_from_list _); simpls~. Qed.

  Include HasUsualEq <+ UsualIsEq.
End Atom.

(* Definition atom := Atom.t. *)
(* Declare Scope atom_scope. *)
(* Delimit Scope atom_scope with atom. *)
(* Bind Scope atom_scope with atom. *)

(* (* Metalib https://raw.githubusercontent.com/plclub/metalib/master/Metalib/CoqEqDec.v *) *)
(* Require Import Coq.Classes.Equivalence Coq.Classes.EquivDec Coq.Logic.Decidable. *)

(* *********************************************************************** *)
(** * Specializing [EqDec] *)

(** It is convenient to be able to use a single notation for decidable *)
(*     equality on types.  This can naturally be done using a type class. *)
(*     However, the definition of [EqDec] in the EquivDec library is *)
(*     overly general for cases where the equality is [eq]: the extra *)
(*     layer of abstraction provided by abstracting over the equivalence *)
(*     relation gets in the way of smooth reasoning.  To get around this, *)
(*     we define a version of that class where the equivalence relation *)
(*     is hard-coded to be [eq]. *)

(*     Implementation note: One should not declare an instance for *)
(*     [EqDec_eq A] directly.  First, declare an instance for [@EqDec A *)
(*     eq eq_equivalence].  Second, let class inference build an instance *)
(*     for [EqDec_eq A] using the instance declaration below. *)

(*     Implementation note (BEA): Specifying [eq_equivalence] explicitly *)
(*     is important.  Following Murphy's Law, if type class inference can *)
(*     find multiple ways of inferring the [@Equivalence A eq] argument, *)
(*     it will do so in the most inconvenient way possible. *)
(*     Additionally, I choose to infer [EqDec_eq] instances from [EqDec] *)
(*     instances because the standard library already defines instances *)
(*     for [EqDec]. *)

Class EqDec_eq (A : Type) :=
  eq_dec : forall (x y : A), {x = y} + {x <> y}.

Instance EqDec_eq_of_EqDec (A : Type) `(@EqDec A eq eq_equivalence) : EqDec_eq A.
Proof. trivial. Defined.

(** We can also provide a reflexivity theorem for rewriting with, since types *)
(*     with decidable equality satisfy UIP/Axiom K and so we know that we can *)
(*     rewrite the equality proof to `eq_refl`. *)

Theorem eq_dec_refl {A : Type} `{EqDec_eq A} (x : A) : eq_dec x x = left eq_refl.
Proof.
  destruct (eq_dec x x); [|contradiction].
  f_equal; apply (Eqdep_dec.UIP_dec eq_dec).
Qed.

(* ********************************************************************** *)
(** * Decidable equality *)

(** We prefer that "==" refer to decidable equality at [eq], as *)
(*     defined by the [EqDec_eq] class from the CoqEqDec library. *)

Declare Scope coqeqdec_scope.
Notation " x == y " := (eq_dec x y) (at level 70) : coqeqdec_scope.
Open Scope coqeqdec_scope.

(* Igualdade entre átomos é decidível *)
Instance atom_eq_dec: @EqDec Atom.t eq eq_equivalence.
Proof. exact Atom.eq_dec. Defined.

