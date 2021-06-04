From Coq Require Import MSets.

Require Import Base AtomImpl.
Require MSetNotin.

(** *Conjunto de Átomos *)
(** Conjunto de átomos (não ordenado), com estrutura opaca, é implementado utilizando listas. *)
(* Exporta as operações de conjunto definidas por WSetsOn *)
Module AtomSet: (MSetInterface.WSetsOn Atom) := MSetWeakList.Make Atom.

(* Procedimento de decisão sobre conjuntos: fsetdec *)
Module Export AtomSetDec := MSetDecide.WDecideOn Atom AtomSet.

(* Fatos adicionais sobre conjuntos *)
Module Export AtomSetFac := MSetFacts.WFactsOn Atom AtomSet.

(* Táticas para lidar com notin. *)
Module Export AtomSetNotin := MSetNotin.WNotinOn Atom AtomSet.

(* Propriedades de conjuntos *)
Module Export AtomSetProp := MSetProperties.WPropertiesOn Atom AtomSet.

(** *Propriedades lista de átomos para conjunto de átomos *)
Definition fresh (L: AtomSet.t): Atom.t := Atom.fresh (AtomSet.elements L).

Lemma fresh_spec L: ~ AtomSet.In (fresh L) L.
Proof.
  unfold fresh; lets H: (Atom.fresh_notin_list (AtomSet.elements L));
    intros J; apply H; apply elements_iff in J;
      apply InA_alt in J as [x []]; subst; auto.
Qed.

(* Manter compatibildade com as táticas AtomTactics *)
Lemma fresh_spec_compat (L: AtomSet.t): {x: Atom.t | ~ AtomSet.In x L}.
Proof. exists (fresh L); apply fresh_spec. Qed.

Lemma fresh_set_eq a b: AtomSet.Equal a b -> fresh a = fresh b.
Proof. Admitted.

(* Definition atom_singleton: Atom.t -> AtomSet.t := fun a => AtomSet.singleton a. *)
(* Coercion atom_singleton : atom >-> ASet. *)

(* (* Notations *) *)
(* Notation "∅" :=  (AtomSet.empty). *)
(* Notation "{{ x }}" := (AtomSet.singleton (x%atom)) (format "{{ x }}"). *)
(* Infix "∈" := AtomSet.In (at level 70). *)
(* (* Infix "∉" := (fun a b => not (AtomSet.In (a%atom) b)) (at level 70). *) *)
(* Notation "x ∉ s" := (not (AtomSet.In (x%atom) s)) (at level 70). *)
(* Infix "∪" := AtomSet.union (at level 65, right associativity). *)
(* Infix "∩" := AtomSet.inter (at level 65, right associativity). *)
(* Notation "a \ b" := (AtomSet.remove (a%atom) b) (at level 65, right associativity). *)
(* (* Infix "\" := AtomSet.remove (at level 65, right associativity) *) *)
(* Notation "E [=] F" := (AtomSet.Equal E F) (at level 70, no associativity). *)
(* Hint Extern 5 (AtomSet.notin _ _) => fsetdec: core. *)
