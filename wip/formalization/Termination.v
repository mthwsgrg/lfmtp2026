Require Export SigmaMatch.
Require Import Init.Wf.




Definition Triple_order (Q Q': nat * nat * nat) :=
  let N1  := fst (fst Q) in
  let N1' := fst (fst Q') in
  let N2  := snd (fst Q) in
  let N2' := snd (fst Q') in
  let N3  := snd Q in
  let N3' := snd Q' in
   (N1 > N1') \/
  ((N1 >= N1') /\ (N2 > N2')) \/
  (((N1 >= N1') /\ (N2 >= N2')) /\ (N3 > N3')).


Definition Problem_measure (P: Problem) :=
  (length (Problem_vars P), Problem_size P, σmin_steps_possible P).


Definition smatch_step_size_order (T T' : Tuple) := 
  Triple_order (Problem_measure (snd T')) (Problem_measure (snd T)).


Definition smatch_step_order (T T' : Tuple) :=  smatch T' T.

Notation "T <<* T'" := (smatch_step_size_order T T') (at level 67).


Lemma smatch_step_termination : forall T T',  smatch T T' ->  T' <<* T.
Admitted.



(* This is standard because lexicographic ordering of triples of natural numbers is obviously well-founded *)
Lemma smatch_step_size_order_wf : well_founded smatch_step_size_order.
Admitted.



Lemma unif_step_order_wf : well_founded smatch_step_order.
Proof.
  unfold well_founded. intro T.
  apply well_founded_ind with (R:= smatch_step_size_order).
  apply smatch_step_size_order_wf. intros T' H.
  apply Acc_intro. intros T'' H0.
  unfold smatch_step_order in H0.
  apply smatch_step_termination in H0.
  apply H; trivial.
Qed.
