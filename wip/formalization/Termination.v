Require Export SigmaMatch.
Require Import Init.Wf.
Require Import Wf_nat.
Require Import Inverse_Image.



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
Proof.
  intros T T' H.
  unfold smatch_step_size_order.
  unfold Problem_measure.
  unfold Triple_order.
  
  destruct H; simpl.
  - right. left. split.
    apply nat_leq_inv. eapply subset_list; intros.
    apply NoDup_Problem_vars. eapply problem_var_remove_one_mem.
    apply H0.
    rewrite Problem_size_remove; trivial.
    simpl. admit. (* obvious reasoning with arithmetic 
    assert (Q : Problem_size P >= Problem_size ([(equ s s)])).
    apply Problem_size_neq_nil; trivial.
    assert (Q' : Problem_size P > 0).
    apply Problem_size_gt_0 with (s:=s) (t:=s); trivial. 
    assert (Q'' : exp_size s > 0).
    apply exp_size_gt_0.
    simpl in Q. lia. *)
  - (* same as above *) admit.
  - right. left. split.
    apply nat_leq_inv. apply subset_list; intros.
    apply NoDup_Problem_vars. 
    admit. (* same reasoning as earlier *)
    admit. (* arithmetic reasoning *)
  - admit.
  - admit.
  - admit.
  - admit.
  (* σmin case start *)  
  - right. right. repeat split.
    admit. (* set related reasoning *)
    rewrite Problem_size_remove; trivial.
    assert ( Problem_size P + Problem_size ([equ (Lam s)[σ]  s'[σ']]) >= Problem_size (P |+ equ (Lam s) [σ] s' [σ'])) by apply Problem_size_add.
    assert (Equation_size (equ (Lam s [Zero .: σ >> ↑]) s' [σ']) > Equation_size (equ (Lam s)[σ]  s'[σ'])) by admit.

    simpl. simpl in H0. lia.
    apply set_add_intro1; trivial.

    
    
    
    
Admitted.

Lemma Triple_order_wf : well_founded (fun q q' => Triple_order q' q).
Proof.
  unfold well_founded.
  intros [[n1 n2] n3].
  generalize dependent n3.
  generalize dependent n2.
  induction n1 as [n1 IH1] using (well_founded_induction lt_wf).
  intros n2.
  induction n2 as [n2 IH2] using (well_founded_induction lt_wf).
  intros n3.
  induction n3 as [n3 IH3] using (well_founded_induction lt_wf).
  constructor. intros [[m1 m2] m3] H.
  unfold Triple_order in H. simpl in H.
  destruct H as [H1 | [[H1 H2] | [[H1 H2] H3]]].
  - apply IH1. lia.
  - destruct (var_eqdec m1 n1) as [Eq1 | Neq1].
    + subst m1. apply IH2. lia.
    + apply IH1. lia.      
  - destruct (var_eqdec m1 n1) as [Eq1 | Neq1].
    + subst m1. destruct (var_eqdec m2 n2) as [Eq2 | Neq2].
      * subst m2. apply IH3. lia.
      * apply IH2. lia.
    + apply IH1. lia.
Qed.


Lemma smatch_step_size_order_wf : well_founded smatch_step_size_order.
  Proof.
  unfold smatch_step_size_order.
  apply wf_inverse_image with (f := fun T => Problem_measure (snd T))
                              (R := fun q q' => Triple_order q' q).
  exact Triple_order_wf.
Qed.  




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
