Require Import Atom.AtomTactics.

Tactic Notation "apply" "fresh" constr(H) "with" ident(z) :=
  let L := beautify_fset gather_atoms in
  apply H with L; intros z ?.

Tactic Notation "apply" "fresh" constr(H) :=
  let z := fresh "v" in
  apply fresh H with z.

Tactic Notation "rewriten" "<-" constr(H) := rewrite <- H; autorewrite with nominal.
Tactic Notation "rewriten" constr(H) := rewrite H; autorewrite with nominal.
