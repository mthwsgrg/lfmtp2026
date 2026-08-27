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
    simpl. (* obvious reasoning with arithmetic *) 
    assert (Q : Problem_size P >= Problem_size ([(equ s s)])).
    apply Problem_size_neq_nil; trivial.
    assert (Q' : Problem_size P > 0).
    apply Problem_size_gt_0 with (e:= equ s s); trivial. 
    assert (Q'' : exp_size s > 0).
    apply (proj1 exps_size_gt_0).
    simpl in Q. lia. 
 - right. left. split.
    apply nat_leq_inv. eapply subset_list; intros.
    apply NoDup_Problem_vars. eapply problem_var_remove_one_mem.
    apply H0.
    rewrite Problem_size_remove; trivial.
    simpl. (* obvious reasoning with arithmetic *) 
    assert (Q : Problem_size P >= Problem_size ([(equ_s σ σ)])).
    apply Problem_size_neq_nil; trivial.
    assert (Q' : Problem_size P > 0).
    apply Problem_size_gt_0 with (e:= equ_s σ σ); trivial. 
    assert (Q'' : sexp_size σ > 0).
    apply (proj2 exps_size_gt_0).
    simpl in Q. lia. 
  
  - right. left. split.
    apply nat_leq_inv. apply subset_list; intros.
    apply NoDup_Problem_vars.
    case (set_In_dec sortedvar_eqdec b
            (set_union sortedvar_eqdec (vars_of_exp (App s t)) (vars_of_exp (App s' t')))).

      intro HIn.
      apply set_union_elim in HIn. destruct HIn.
      apply in_left_problem_then_in_problem.
      eapply in_exp_then_in_left_problem; swap 1 2. apply H. now apply H1.
      apply in_right_problem_then_in_problem.
      eapply in_exp_then_in_right_problem; swap 1 2. apply H. now apply H1.

      intro HIn.
      apply problem_var_remove_one_mem in H0.
      apply problem_var_ext_vars in H0.
      apply problem_var_ext_vars in H0.
      apply H0.
      intro. apply HIn. simpl in H1.
      simpl. apply set_union_elim in H1.
      destruct H1. now repeat apply set_union_intro1.
      apply set_union_intro2. now apply set_union_intro1.
      intro. apply HIn. simpl in H1.
      simpl. apply set_union_elim in H1.
      destruct H1. 
      apply set_union_intro1. now apply set_union_intro2.
      now repeat apply set_union_intro2.

      rewrite Problem_size_remove.
      assert (Q : Problem_size (P |+ (equ s s')) + Problem_size ([equ t t']) >=
                 Problem_size ((P |+ (equ s s')) |+ (equ t t'))).
      apply Problem_size_add.
      assert (Q' : Problem_size P  + Problem_size ([equ s s']) >=
                 Problem_size (P |+ (equ s s'))).
      apply Problem_size_add.
      assert (Q'': Problem_size P > 0).
      apply Problem_size_gt_0 with (e:= equ (App s t) (App s' t')); trivial.
      assert (Q''' : exp_size s > 0).
      apply (proj1 exps_size_gt_0).
      simpl in * |- *. lia.
      now repeat apply set_add_intro1. 

  - admit.
  - admit.
  - admit.
  - admit.
  (* σmin case start *)
    (* lam *)
  - right. right. repeat split.
    apply nat_leq_inv. apply subset_list; intros.
    apply NoDup_Problem_vars.
    case (set_In_dec sortedvar_eqdec b (set_union sortedvar_eqdec
                                          (vars_of_exp (Lam s [Zero .: σ >> ↑]))
                                          (vars_of_exp s'[σ']))).

    intro Hin.
    apply set_union_elim in Hin. destruct Hin.
    apply in_left_problem_then_in_problem.
    eapply in_exp_then_in_left_problem; swap 1 2.
    apply H. apply H1.
    apply in_right_problem_then_in_problem.
    eapply in_exp_then_in_right_problem; swap 1 2.
    apply H. apply H1.

    intro Hn. apply problem_var_remove_one_mem in H0.
    apply problem_var_ext_vars in H0.
    apply H0.
    intro. apply Hn.
    simpl in H1. simpl.
    apply set_union_elim in H1. destruct H1.
    apply set_union_elim in H1. destruct H1.
    now repeat apply set_union_intro1.
    apply set_union_intro1. now repeat apply set_union_intro2.
    apply set_union_elim in H1. destruct H1.
    apply set_union_intro2. now apply set_union_intro1.
    now repeat apply set_union_intro2.
        
 (* set related reasoning *)
    rewrite Problem_size_remove; trivial.
    assert ( Problem_size P + Problem_size ([equ (Lam s)[σ]  s'[σ']]) >= Problem_size (P |+ equ (Lam s) [σ] s' [σ'])) by apply Problem_size_add.
    assert (Equation_size (equ (Lam s [Zero .: σ >> ↑]) s' [σ']) > Equation_size (equ (Lam s)[σ]  s'[σ'])).
    { unfold Equation_size.
      assert (exp_size (Lam s[Zero .: σ >> ↑]) > exp_size (Lam s)[σ]) by (simpl; lia).
      lia.
    }
     

    simpl. simpl in H0. lia.
    apply set_add_intro1; trivial.
    rewrite σmin_steps_remove; trivial.
    unfold lEqn_σmin_steps.
    assert (Q' : σmin_steps_possible P > 0)
     by ( eapply σmin_step_lam_gt_0; apply H). 
    
    assert (σmin_steps_possible P + σmin_steps_possible ([equ (Lam s)[σ] s'[σ']]) >= σmin_steps_possible (P |+ equ (Lam s) [σ] s' [σ'])) by (apply σmin_steps_add).
    assert (σmin_steps_possible ([equ (Lam s) [σ] s' [σ']]) = σmin_rhs_form_exp (Lam s) [σ]) by
    (simpl; lia). rewrite H1 in H0.

    assert (σmin_rhs_form_exp (Lam s[Zero .: σ >> ↑]) > (σmin_rhs_form_exp  (Lam s)[σ])) by (apply σmin_lam_step_less). 
    lia. 
    apply set_add_intro1. apply H.
     
  - right. right. repeat split.
    apply nat_leq_inv. apply subset_list; intros.
    apply NoDup_Problem_vars.
    case (set_In_dec sortedvar_eqdec b (set_union sortedvar_eqdec
                                          (vars_of_sexp (σ >> τ >> ρ))
                                          (vars_of_sexp (σ' >> τ')))).

    intro Hin.
    apply set_union_elim in Hin. destruct Hin.
    apply in_left_problem_then_in_problem.
    eapply in_sexp_then_in_left_problem; swap 1 2.
    apply H. apply H1.
    apply in_right_problem_then_in_problem.
    eapply in_sexp_then_in_right_problem; swap 1 2.
    apply H. apply H1.

    intro Hn. apply problem_var_remove_one_mem in H0.
    apply problem_var_ext_vars in H0.
    apply H0.
    intro. apply Hn.
    simpl in H1. simpl. 
    apply set_union_elim in H1. destruct H1.
    apply set_union_intro1. now rewrite set_union_assoc.
    now apply set_union_intro2. 

    rewrite Problem_size_remove; trivial.
    assert ( Problem_size P + Problem_size ([equ_s ((σ >> τ)>>ρ)  (σ' >> τ')]) >= Problem_size (P |+ equ_s ((σ >> τ)>>ρ)  (σ' >> τ'))) by apply Problem_size_add.
    assert (Equation_size (equ_s (σ >> τ >> ρ) (σ' >> τ')) >= Equation_size (equ_s ((σ >> τ)>>ρ)  (σ' >> τ') )).
    { unfold Equation_size.
      assert (sexp_size (σ >> τ >> ρ) >= sexp_size ((σ >> τ)>>ρ)) by (simpl; lia).
      lia.
    }
    simpl. simpl in H0. lia.
    apply set_add_intro1; trivial.

    rewrite σmin_steps_remove; trivial.
    unfold lEqn_σmin_steps.
    assert (Q' : σmin_steps_possible P > 0)
     by ( eapply σmin_step_assoc_gt_0; apply H). 

    
    assert (σmin_steps_possible P + σmin_steps_possible ([equ_s ((σ >> τ)>>ρ)  (σ' >> τ')]) >= σmin_steps_possible (P |+ equ_s ((σ >> τ)>>ρ)  (σ' >> τ'))) by (apply σmin_steps_add).

    (** to edit from here *)
    assert (σmin_steps_possible ([equ (Lam s) [σ] s' [σ']]) = σmin_rhs_form_exp (Lam s) [σ]) by
    (simpl; lia). rewrite H1 in H0.

    assert (σmin_rhs_form_exp (Lam s[Zero .: σ >> ↑]) > (σmin_rhs_form_exp  (Lam s)[σ])) by (apply σmin_lam_step_less). 
    lia. 
    apply set_add_intro1. apply H.

    


    
  - admit.
  - admit.
  - left.
    apply nat_lt_inv.
    eapply subset_list'.
    apply NoDup_Problem_vars.
    intros.
    destruct (sortedvar_eqdec (exp_var X) b) as [HEq | HnEq].
      destruct b as [X' | Y']; try inversion HEq.
       subst. 
       assert (~In (exp_var X') (Problem_vars ((P \ equ s (VarExp X')) |^^ [exp_assign X' s]))).
       { apply problem_X_clear. simpl.
         split. intro. apply H. eapply in_exp_then_in_left_problem. apply H1. apply H0.
         intro. apply H. eapply problem_lhvar_remove_one_mem. apply H1. now simpl. }
       contradiction.
     destruct (set_In_dec sortedvar_eqdec b (vars_of_exp s)).
        apply in_left_problem_then_in_problem.
         eapply in_exp_then_in_left_problem.
         apply s0. apply H0.
       eapply problem_var_remove_one_mem.
        eapply problem_vars_desubst. apply H2.
        simpl. congruence. simpl. apply n.     
        exists (exp_var X). split. apply in_right_problem_then_in_problem.
        eapply in_exp_then_in_right_problem; swap 1 2. apply H0.  now left.
    apply problem_X_clear. simpl.
    split. intro. apply H. eapply in_exp_then_in_left_problem. apply H2. apply H0.
    intro. apply H. eapply problem_lhvar_remove_one_mem. apply H2.
    now simpl.
 -  left.
    apply nat_lt_inv.
    eapply subset_list'.
    apply NoDup_Problem_vars.
    intros.
    destruct (sortedvar_eqdec (sexp_var Y) b) as [HEq | HnEq].
      destruct b as [X' | Y']; try inversion HEq.
       subst. 
       assert (~In (sexp_var Y') (Problem_vars ((P \ equ_s σ (VarSExp Y')) |^^ [sexp_assign Y' σ]))).
       { apply problem_X_clear. simpl.
         split. intro. apply H. eapply in_sexp_then_in_left_problem. apply H1. apply H0.
         intro. apply H. eapply problem_lhvar_remove_one_mem. apply H1. now simpl. }
       contradiction.
     destruct (set_In_dec sortedvar_eqdec b (vars_of_sexp σ)).
        apply in_left_problem_then_in_problem.
         eapply in_sexp_then_in_left_problem.
         apply s. apply H0.
       eapply problem_var_remove_one_mem.
        eapply problem_vars_desubst. apply H2.
        simpl. congruence. simpl. apply n.     
        exists (sexp_var Y). split. apply in_right_problem_then_in_problem.
        eapply in_sexp_then_in_right_problem; swap 1 2. apply H0.  now left.
    apply problem_X_clear. simpl.
    split. intro. apply H. eapply in_sexp_then_in_left_problem. apply H2. apply H0.
    intro. apply H. eapply problem_lhvar_remove_one_mem. apply H2.
    now simpl.
 
    
    
    
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
