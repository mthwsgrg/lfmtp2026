Require Export Coq.Lists.List.
Require Import Coq.Program.Equality.
From poplmark Require Export sysf_pat.
Require Import Coq.Program.Tactics.
Require Import Coq.ZArith.Zcompare.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.
From poplmark Require Import POPLMark22.



Parameter update_map: forall {X Y} {f : X -> Y} (xs: list (nat * X)) l x,
  (map (prod_map (fun x => x) f) (update xs l x)) = update (map (prod_map (fun x => x) f) xs) l (f x). 

Parameter pat_eval_subst : forall {n p' q' p q: nat} (P: pat p') (s : tm p' q') (tBar: fin n -> tm p' q')  (σ: fin p' -> ty p) (τ: fin q' -> tm p q), pat_eval n P s tBar ->  pat_eval n P[σ] s[σ;τ] (tBar >> [σ; τ]).

Parameter value_subst: forall {p' q' p q: nat} (s : tm p' q') (σ: fin p' -> ty p) (τ: fin q' -> tm p q), value s -> value s[σ; τ].


(** Substitutivity of Evaluation relation of System F<: with records 

- Three times as_apply are used corresponding to the reduction of three binders: abstraction, type abstraction and variadic let abstraction

*)

Lemma eval_subst {p' q' p q: nat} : forall (s t : tm p' q') (σ: fin p' -> ty p) (τ: fin q' -> tm p q), eval s t -> eval s[σ; τ] t[σ; τ].
Proof.
  intros.
  induction H; asimpl; try constructor; eauto.
  - as_apply E_appabs.
  - as_apply E_Tapptabs.
  - apply in_map; eauto.
  - as_apply letpat_eval. apply pat_eval_subst; eauto.
  - apply value_subst; eauto.
  - rewrite update_map. econstructor. apply IHeval.
    apply in_map; eauto.
Qed.

