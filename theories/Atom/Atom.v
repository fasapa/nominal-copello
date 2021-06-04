Require Import Base.
Require Export AtomImpl AtomSetImpl AtomTactics.
Require Export Tactics.

Notation atom := Atom.t.
Notation aset := AtomSet.t.
Notation aslt := AtomSet.elt.

(* Module SetNotations. *)
Declare Scope aset_scope.
Delimit Scope aset_scope with aset. (* aset é diferente de aset acima. *)

  (* Abaixo de 70 para ligar mais "tight" que igualdade = *)
Notation "a [=] b" := (AtomSet.Equal (a%aset) (b%aset)) (at level 70, no associativity): aset_scope.

Notation "∅" := AtomSet.empty: aset_scope.
Notation "{{ x }}" := (AtomSet.singleton x): aset_scope.

Infix "∈" := AtomSet.In (at level 30): aset_scope.
Notation "a ∉ b" := (not (AtomSet.In a (b%aset))) (at level 30): aset_scope.

  (* Não assumimos precedencia entre os operadores de conjuntos. Assumimos o uso de (). *)
Notation "a ∪ b" := (AtomSet.union (a%aset) (b%aset)) (at level 31, right associativity): aset_scope.
Notation "a ∩ b" := (AtomSet.inter (a%aset) (b%aset)) (at level 31, right associativity): aset_scope.
Notation "a \ b" := (AtomSet.remove a (b%aset)) (at level 31, no associativity): aset_scope.

Bind Scope aset_scope with aset.
Bind Scope aset_scope with AtomSet.t.
(* End SetNotations. *)
