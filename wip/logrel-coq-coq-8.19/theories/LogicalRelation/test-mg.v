From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms UntypedReduction Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Reflexivity Irrelevance Escape.

Set Universe Polymorphism.


(** experimenting of the form (tProd dom⟨ρ⟩ cod⟨upRen_term_term ρ⟩) = tProd (?dom_ ?cod_)⟨ρ⟩ *)

Parameter dom cod : term.
Parameter ρ : nat -> nat.


Goal True.

evar (dom_: term).
evar (cod_: term).
assert ( (tProd dom⟨ρ⟩ cod⟨upRen_term_term ρ⟩) = (tProd ?dom_ ?cod_)⟨ρ⟩).
simpl.
reflexivity.

