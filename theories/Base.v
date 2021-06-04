(* https://github.com/robbertkrebbers/ch2o/blob/master/prelude/base.v *)
From Coq Require Export
     Program
     (* Classes.Morphisms *)
     (* Classes.SetoidClass *)
     Classes.RelationClasses
     Classes.Equivalence
     Classes.EquivDec
     (* Setoids.Setoid *)
     Lists.List
     Bool
     Utf8
     Lia.
Export ListNotations.

From TLC Require Export LibTactics.
Require Export Simp.

(* Always unfold id function *)
Arguments id / {A} x.

(* (** *Global Definitions *) *)
(* Definition Injective {A B} (f: A -> B) := forall x y, f x = f y -> x = y. *)
(* Arguments Injective {A B} / f. *)

(* Definition Surjective {A B} (f: A -> B) := forall y, exists x, f x = y. *)
(* Definition Bijective {A B} (f: A -> B) := Injective f /\ Surjective f. *)
