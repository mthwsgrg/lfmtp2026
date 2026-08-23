Require Export SigmaMatch.

(* Temp lemmas in this file start*)


(* Temp lemmas in this file end *)
 
Definition valid_tuple (T : Tuple) :=
  let S := (fst T) in
  let P := (snd T) in
  ( set_inter sortedvar_eqdec (dom_rec S) (Problem_vars P) = [] ).


Definition match_sol (S' :Subst) (T : Tuple) :=
  let S := (fst T) in
  let P := (snd T) in
  ( forall s t, set_In (equ s t) P ->  σmin_equiv s (sub t S') ) /\
  ( forall σ τ, set_In (equ_s σ τ) P -> σmin_equivs σ (sub_s τ S')) /\  
  ( exists S'', (sub_comp S S'') ~:c S' ).


Lemma match_sol_preservation : forall Sl T T',

      valid_tuple T ->

      set_inter sortedvar_eqdec (dom_rec Sl)  (lhvars_Probl (snd T)) = [] ->

      smatch T T' ->

      match_sol Sl T' -> match_sol Sl T.   
Proof.
  intros Sl T T' HVl HLh HSt HSl. unfold valid_tuple in HVl.
  destruct HSt; intros; unfold match_sol in *; simpl in *;
  destruct HSl as [HEq1 [HEq2 HEq3]]; destruct HEq3 as [S'' HEq3]; repeat split;
  try (exists S''; assumption); try intros s0 t0 HinP. 
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  (* Inst Exp Case *)
  - unfold subs_equiv in HEq3; destruct HEq3 as [HEq3 HEq3'].   
    destruct (Equation_eqdec (equ s0 t0) (equ s (VarExp X))) as [Eq | Eq]; intros.
    + rewrite Eq in *. simpl in *.
      inversion Eq; subst. clear Eq.
      simpl. apply σmin_equiv_trans with (t := sub s S'').
      apply (proj1 not_in_dom_same_exp); split; intros.      
      eapply σmin_comp_prop_exp with (S:= sub_comp S ([exp_assign X s])%list).
      eapply set_nocommon_inter_forall_flip with (X:= exp_var X0) in HVl.
      apply In_dom_eq_dom_flip_exp. apply not_In_dom_lookup_flip_exp.
      apply not_in_dom_lookup_same_exp in HVl.
      rewrite look_up_sub_comp_exp. rewrite HVl. simpl.
      destruct (var_eqdec X X0); subst.
      eapply in_exp_then_in_left_problem with (P := P) in H1. contradiction. apply HinP. trivial.
      eapply in_exp_then_in_left_problem with (P := P) in H1.
      now apply in_left_problem_then_in_problem. apply HinP.
      eapply set_nocommon_inter_forall_flip in HLh.
      apply HLh. eapply in_exp_then_in_left_problem. apply H1. apply H0.
      unfold subs_equiv; split; eauto. 

      eapply σmin_comp_prop_sexp with (S:= sub_comp S ([exp_assign X s])%list).
      eapply set_nocommon_inter_forall_flip with (X := sexp_var Y) in HVl.
      apply In_dom_eq_dom_flip_sexp. apply not_In_dom_lookup_flip_sexp.
      apply not_in_dom_lookup_same_sexp in HVl.
      rewrite look_up_sub_comp_sexp.  rewrite HVl. now simpl.
      eapply in_exp_then_in_left_problem with (P := P) in H1. 
      now apply in_left_problem_then_in_problem. apply HinP. 
      eapply set_nocommon_inter_forall_flip in HLh.
      apply HLh. eapply in_exp_then_in_left_problem. apply H1. apply H0.
      unfold subs_equiv; split; eauto.

      specialize (HEq3 X).
      rewrite look_up_sub_comp_exp in HEq3. rewrite in_subcomp_second_arg_exp in HEq3.
      simpl in HEq3. destruct (var_eqdec X X); [assumption | contradiction].
      eapply set_nocommon_inter_forall_flip with (X:= exp_var X) in HVl.
      apply HVl. eapply in_right_problem_then_in_problem.
      eapply in_exp_then_in_right_problem.
      2: apply H0. now left.
   +  destruct (set_In_dec sortedvar_eqdec (exp_var X) (vars_of_exp t0)) as [Ht0 | Hnt0].
      apply σmin_equiv_trans with (t  := sub t0 (sub_comp ([exp_assign X s]) Sl)).
      rewrite (proj1 subst_comp_expand).
      apply HEq1. apply push_subst_problem_exp.
      now apply set_remove_3.

      
       
      
      

      
     
Admitted.      
