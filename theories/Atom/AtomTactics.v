Require Import AtomImpl AtomSetImpl.

(** *Táticas para escolher nomes frescos *)

(* [ltac_remove_dups] takes a [list] and removes duplicate items from *)
(* 	 it.  The supplied list must, after simplification via [simpl], be *)
(* 	 built from only [nil] and [cons].  Duplicates are recognized only *)
(* 	 "up to syntax," i.e., the limitations of Ltac's [context] *)
(* 	 check. *)

(* TODO: Táctica não específica, pode ir para outro lugar. *)
Ltac ltac_remove_dups xs :=
	let rec remove xs acc :=
			match xs with
			| List.nil => acc
			| List.cons ?x ?xs =>
				match acc with
				| context [x] => remove xs acc
				| _ => remove xs (List.cons x acc)
				end
			end
	in
	match type of xs with
	| List.list ?A =>
		let xs := eval simpl in xs in
		let xs := remove xs (@List.nil A) in
		eval simpl in (List.rev xs)
	end.

(* The auxiliary tactic [simplify_list_of_atom_sets] takes a list of *)
(* 	 finite sets of atoms and unions everything together, returning the *)
(*    resulting single finite set. *)
Ltac simplify_list_of_atom_sets L :=
	let L := eval simpl in L in
	let L := ltac_remove_dups L in
	let L := eval simpl in (List.fold_right AtomSet.union AtomSet.empty L) in
	match L with
	| context C [AtomSet.union ?E AtomSet.empty] => context C [ E ]
	end.

(* [gather_atoms_with F] returns the union of all the finite sets *)
(* 	 [F x] where [x] is a variable from the context such that [F x] *)
(* 	 type checks. *)
Ltac gather_atoms_with F :=
	let apply_arg x :=
			match type of F with
			| _ -> _ -> _ -> _ => constr:(@F _ _ x)
			| _ -> _ -> _ => constr:(@F _ x)
			| _ -> _ => constr:(@F x)
			end in
	let rec gather V :=
			match goal with
			| H : _ |- _ =>
				let FH := apply_arg H in
				match V with
				| context [FH] => fail 1
				| _ => gather (AtomSet.union FH V)
				end
			| _ => V
			end in
	let L := gather AtomSet.empty in eval simpl in L.

(* [beautify_fset V] assumes that [V] is built as a union of finite *)
(* 	 sets and returns the same set cleaned up: empty sets are removed *)
(* 	 and items are laid out in a nicely parenthesized way. *)
Ltac beautify_fset V :=
	let rec go Acc E :=
			match E with
			| AtomSet.union ?E1 ?E2 => let Acc2 := go Acc E2 in go Acc2 E1
			| AtomSet.empty => Acc
			| ?E1 => match Acc with
							| AtomSet.empty => E1
							| _ => constr:(AtomSet.union E1 Acc)
							end
			end
	in go AtomSet.empty V.

(* The tactic [pick fresh Y for L] takes a finite set of atoms [L] *)
(* 	 and a fresh name [Y], and adds to the context an atom with name *)
(* 	 [Y] and a proof that [~ In Y L], i.e., that [Y] is fresh for [L]. *)
(* 	 The tactic will fail if [Y] is already declared in the context. *)

(* 	 The variant [pick fresh Y] is similar, except that [Y] is fresh *)
(* 	 for "all atoms in the context."  This version depends on the *)
(* 	 tactic [gather_atoms], which is responsible for returning the set *)
(* 	 of "all atoms in the context."  By default, it returns the empty *)
(* 	 set, but users are free (and expected) to redefine it. *)

(* Espera-se redefinir essa tática para escolher adequadamente átomos em cada contexto. *)
Ltac gather_atoms :=
	constr:(AtomSet.empty).

Tactic Notation "pick" "fresh" ident(Y) "for" constr(L) :=
	let Fr := fresh "Fr" in
	let L := beautify_fset L in
	(destruct (fresh_spec_compat L) as [Y Fr]).

Tactic Notation "pick" "fresh" ident(Y) :=
	let L := gather_atoms in
	pick fresh Y for L.

(* Ltac pick_fresh y := *)
(* 	pick fresh y. *)

(** Example: We can redefine [gather_atoms] to return all the *)
(* 	    "obvious" atoms in the context using the [gather_atoms_with] thus *)
(* 	    giving us a "useful" version of the "[pick fresh]" tactic. *)

Ltac gather_atoms ::=
	(* let A := gather_atoms_with (fun x : Atom.t => x) in *)
	let B := gather_atoms_with (fun x : Atom.t => AtomSet.singleton x) in
	constr:(B).
