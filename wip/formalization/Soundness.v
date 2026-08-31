Require Export SigmaMatch.
Require Import ARS.

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
  destruct HSl as [HEq1 [HEq2 HEq3]]; destruct HEq3 as [S'' HEq3];
  unfold subs_equiv in HEq3; destruct HEq3 as [HEq3 HEq3'];
  repeat split; try (exists S''; unfold subs_equiv; split; assumption).

  (* refl case start *)
  - intros s0 t0 HinP.
    destruct (Equation_eqdec (equ s0 t0) (equ s s)) as [Eq |nEq] ; intros.
     + inversion Eq; subst.
       rewrite (proj1 vacous_subst_same). apply σmin_equiv_refl.
       apply set_nocommon_forall_inter_flip. intros.
       eapply set_nocommon_inter_forall_flip in HLh.
       apply HLh. eapply in_exp_then_in_left_problem. apply H0. apply H.
     + apply HEq1. apply set_remove_3; eauto.
  - intros σ τ HinP.
    destruct (Equation_eqdec (equ_s σ τ) (equ s s)) as [Eq | nEq]; intros; try inversion Eq.
    apply HEq2. apply set_remove_3; eauto.
  - intros s t HinP.
    destruct (Equation_eqdec (equ s t) (equ_s σ σ)) as [Eq | nEq]; intros; try inversion Eq.
    apply HEq1. apply set_remove_3; eauto.
  - intros σ0 τ0 HinP.
    destruct (Equation_eqdec (equ_s σ0 τ0) (equ_s σ σ)) as [Eq |nEq] ; intros.
     + inversion Eq; subst.
       rewrite (proj2 vacous_subst_same). apply σmin_equivs_refl.
       apply set_nocommon_forall_inter_flip. intros.
       eapply set_nocommon_inter_forall_flip in HLh.
       apply HLh. eapply in_sexp_then_in_left_problem. apply H0. apply H.
     + apply HEq2. apply set_remove_3; eauto.
 
  (* refl case end *)
       
  (* congruence cases start *)
     (* App *)  
  - intros s0 t0 HinP.
    destruct (Equation_eqdec (equ s0 t0) (equ (App s t) (App s' t'))) as [Eq | nEq]; subst.
    + inversion Eq; subst.
      apply σmin_equiv_app; apply HEq1.
      apply (set_remove_3 Equation_eqdec).
      apply set_add_intro1. now apply set_add_intro2.
      intro. inversion H0; subst.
      eapply s_noteq_app. exact H2.

      apply (set_remove_3 Equation_eqdec).
      now apply set_add_intro2.
      intro. inversion H0; subst.
      eapply t_noteq_app. exact H2.
    + apply HEq1.
      apply (set_remove_3 Equation_eqdec); eauto.
      now repeat apply set_add_intro1.

    
  - intros σ τ HinP.
    destruct (Equation_eqdec (equ_s σ τ) (equ (App s t) (App s' t'))) as [Eq | nEq]; try inversion Eq.
    apply HEq2. apply (set_remove_3 Equation_eqdec); eauto.
    now repeat apply set_add_intro1.

    (* Lam *)
  - intros s0 t0 HinP.
    destruct (Equation_eqdec (equ s0 t0) (equ (Lam s) (Lam s'))) as [Eq | nEq].
      +  inversion Eq; subst.
         apply σmin_equiv_lam; apply HEq1.
         apply (set_remove_3 Equation_eqdec).  
         now apply set_add_intro2.
         intro. inversion H0; subst.
         eapply s_noteq_lam. exact H3.              
      +  apply HEq1.
         apply (set_remove_3 Equation_eqdec); eauto.
         now apply set_add_intro1.
  -  intros σ τ HinP.
     case (Equation_eqdec (equ_s σ τ) (equ (Lam s) (Lam s'))) as [Eq | nEq]; intros; try inversion Eq.
     apply HEq2. apply (set_remove_3 Equation_eqdec); eauto.
     now repeat apply set_add_intro1.
    (* subst *) 
  - intros s0 t0 HinP.
    case (Equation_eqdec (equ s0 t0) (equ (s [σ]) (s' [σ']))) as [Eq | nEq]; intros.
      + inversion Eq; subst.
        simpl. apply σmin_equiv_subst. 
        *   apply HEq1. apply (set_remove_3 Equation_eqdec).
            apply set_add_intro1.
            now apply set_add_intro2.
            intro. inversion H0; subst.
            eapply s_noteq_inst. exact H2.            
        *  apply HEq2.
           apply (set_remove_3 Equation_eqdec).
            now apply set_add_intro2.
            intro. inversion H0; subst.            
      + apply HEq1. apply (set_remove_3 Equation_eqdec); eauto.
        now repeat apply set_add_intro1.
     
  - intros σ0 τ0 HinP.
    case (Equation_eqdec (equ_s σ0 τ0) (equ (s [σ]) (s' [σ']))) as [Eq | nEq]; intros; try inversion Eq.
    apply HEq2. apply (set_remove_3 Equation_eqdec); eauto.
    now repeat apply set_add_intro1.
    (* cons *)
  -  intros s0 t0 HinP.
     case (Equation_eqdec (equ s0 t0) (equ_s (s .: σ) (s' .: σ'))) as [Eq | nEq]; intros; try inversion Eq.
     apply HEq1. apply (set_remove_3 Equation_eqdec); eauto.
     now repeat apply set_add_intro1.
  -  intros σ0 τ0 HinP.
      case (Equation_eqdec (equ_s σ0 τ0) (equ_s (s .: σ) (s' .: σ'))) as [Eq | nEq]; intros.
       + inversion Eq; subst; simpl.
         apply σmin_equivs_cons.
         * apply HEq1. apply (set_remove_3 Equation_eqdec).
            apply set_add_intro1.
            now apply set_add_intro2.
            intro. inversion H0; subst.
         * apply HEq2. apply (set_remove_3 Equation_eqdec).
            now apply set_add_intro2.
            intro. inversion H0; subst.
            eapply σ_noteq_cons. apply H3.
       + apply HEq2.
         apply (set_remove_3 Equation_eqdec).
         now repeat apply set_add_intro1. apply nEq.
   (* comp *)
  -  intros s t HinP.
      case (Equation_eqdec (equ s t) (equ_s (σ >> τ) ( σ'>> τ'))) as [Eq | nEq]; intros; try inversion Eq.
       apply HEq1.  apply (set_remove_3 Equation_eqdec); eauto.
       now repeat apply set_add_intro1.
  -  intros σ0 τ0 HinP.
     case (Equation_eqdec (equ_s σ0 τ0) (equ_s (σ >> τ) (σ' >> τ'))) as [Eq | nEq]; intros.
     +  inversion Eq; subst.
        simpl. apply σmin_equivs_comp; apply HEq2.
        *  apply (set_remove_3 Equation_eqdec).
            apply set_add_intro1.
            now apply set_add_intro2.
            intro. inversion H0; subst.
            eapply σ_noteq_comp. exact H2.            
        * apply (set_remove_3 Equation_eqdec).
          now apply set_add_intro2.
          intro. inversion H0; subst.
          eapply τ_noteq_comp. exact H2.            
      + apply HEq2. apply (set_remove_3 Equation_eqdec); eauto.
        now repeat apply set_add_intro1.
  (* congruence cases end *)
        
  (* σmin cases start *)      
  - intros s0 t0 HinP.
    case (Equation_eqdec (equ s0 t0) (equ (Lam s [Zero .: σ >> ↑]) s' [σ'])) as [Eq | nEq]; intros.
      + inversion Eq; subst.
        apply σmin_equiv_trans with (t := (Lam s)[σ]).
        repeat constructor.
        apply HEq1. apply (set_remove_3 Equation_eqdec).
        now apply (set_add_intro2). 
        intro. inversion H0.
      + apply HEq1. apply (set_remove_3 Equation_eqdec).
        now apply (set_add_intro1). assumption.
  - intros σ0 τ0 HinP.
    case (Equation_eqdec (equ_s σ0 τ0) (equ (Lam s [Zero .: σ >> ↑]) s' [σ'])) as [Eq | nEq]; intros; try inversion Eq.
    apply HEq2.  apply (set_remove_3 Equation_eqdec).  now apply (set_add_intro1). assumption.
  - intros s t HinP.
    case (Equation_eqdec (equ s t) (equ_s (σ >> τ >> ρ) (σ' >> τ'))) as [Eq | nEq]; intros; try inversion Eq.  apply HEq1. apply (set_remove_3 Equation_eqdec).
    now apply (set_add_intro1). assumption.
  - intros σ0 τ0 HinP.
     case (Equation_eqdec (equ_s σ0 τ0) (equ_s (σ >> τ >> ρ) (σ' >> τ'))) as [Eq | nEq]; intros.
       + inversion Eq; subst.
          apply σmin_equivs_trans with (τ := (σ >> τ) >> ρ).
          repeat constructor.
          apply HEq2.
          apply (set_remove_3 Equation_eqdec).
          now apply (set_add_intro2).
          intro. inversion H0.
          eapply (τ_noteq_comp). apply H3.
      +   apply HEq2. apply (set_remove_3 Equation_eqdec).
          now apply (set_add_intro1). assumption.
  - intros s0 t0 HinP.
    case (Equation_eqdec (equ s0 t0) (equ_s (s[τ] .: σ>>τ) (σ' >> τ'))) as [Eq | nEq]; intros; try inversion Eq.
    apply HEq1. apply (set_remove_3 Equation_eqdec).
    now apply (set_add_intro1). assumption.
  - intros σ0 τ0 HinP.
    case (Equation_eqdec (equ_s σ0 τ0) (equ_s (s[τ] .: σ >> τ) (σ' >> τ'))) as [Eq | nEq]; intros.
       +  inversion Eq; subst.
          apply σmin_equivs_trans with (τ := (s .: σ) >> τ).
          repeat constructor. apply HEq2.
          apply (set_remove_3 Equation_eqdec).
          now apply (set_add_intro2).
          intro. inversion H0.
       + apply HEq2. apply (set_remove_3 Equation_eqdec).
         now apply (set_add_intro1). assumption.
   
  - intros s0 t0 HinP.
    case (Equation_eqdec (equ s0 t0) (equ s[σ>>τ] s'[ρ])) as [Eq | nEq]; intros.
      +  inversion Eq; subst.
         apply σmin_equiv_trans with (t := (s[σ])[τ]).
         repeat constructor.  apply HEq1.
         apply (set_remove_3 Equation_eqdec).
         now apply (set_add_intro2).
         intro. inversion H0.
        eapply (τ_noteq_comp). apply H3.
      + apply HEq1. apply (set_remove_3 Equation_eqdec).
        now apply (set_add_intro1). assumption.
  - intros σ0 τ0 HinP.
    case (Equation_eqdec (equ_s σ0 τ0) (equ s[σ >> τ] s'[ρ])) as [Eq | nEq]; intros; try inversion Eq.
    apply HEq2. apply (set_remove_3 Equation_eqdec).
    now apply (set_add_intro1). assumption.
   
  - intros s0 t0 HinP.
     case (Equation_eqdec (equ s0 t0) (equ (App s[σ] t[σ]) s'[σ'])) as [Eq | nEq]; intros.
       +  inversion Eq; subst.
          apply σmin_equiv_trans with (t := (App s t)[σ]).
          repeat constructor. apply HEq1.
          apply (set_remove_3 Equation_eqdec).
          now apply (set_add_intro2).
          intro. inversion H0.
       + apply HEq1. apply (set_remove_3 Equation_eqdec).
         now apply (set_add_intro1). assumption.
  - intros σ0 τ0 HinP.
     case (Equation_eqdec (equ_s σ0 τ0) (equ (App s[σ] t[σ]) s'[σ'])) as [Eq | nEq]; intros; try inversion Eq.
    apply HEq2. apply (set_remove_3 Equation_eqdec).
    now apply (set_add_intro1). assumption.

 
  (* σmin cases end *)
    
  (* Inst exp case start *)
  - intros s0 t0 HinP. (* unfold subs_equiv in HEq3; destruct HEq3 as [HEq3 HEq3']. *)  
    destruct (Equation_eqdec (equ s0 t0) (equ s (VarExp X))) as [Eq | Eq]; intros.
    + rewrite Eq in *. simpl in *.
      inversion Eq; subst. clear Eq.
      simpl. apply σmin_equiv_trans with (t := sub s S'').
      apply (proj1 not_in_dom_same); split; intros.      
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


      
    + destruct (set_In_dec sortedvar_eqdec (exp_var X) (vars_of_exp t0)) as [Ht0 | Hnt0].
      * (* when t0 does have (exp_var x) *)
        apply σmin_equiv_trans with (t  := sub t0 (sub_comp ([exp_assign X s]) Sl)).
        rewrite (proj1 subst_comp_expand).
        apply HEq1. apply push_subst_problem_exp.
        now apply set_remove_3.
        apply (proj1 σmin_subst_ext).
        unfold subs_equiv; split; simpl; intros; try apply σmin_equivs_refl.
        destruct (var_eqdec X X0); subst; try apply σmin_equiv_refl.
        apply σmin_equiv_trans with (t:= s).
        rewrite (proj1 vacous_subst_same). apply σmin_equiv_refl.
        apply (set_nocommon_forall_inter_flip); intros.
        eapply set_nocommon_inter_forall_flip in HLh.
        apply HLh. eapply in_exp_then_in_left_problem. apply H1. apply H0.

        (* rest in this * is similar to first + case *)
        apply σmin_equiv_trans with (t := sub s S'').
        apply (proj1 not_in_dom_same); split; intros.      
        eapply σmin_comp_prop_exp with (S:= sub_comp S ([exp_assign X0 s])%list).
        eapply set_nocommon_inter_forall_flip with (X:= exp_var X) in HVl.
        apply In_dom_eq_dom_flip_exp. apply not_In_dom_lookup_flip_exp.
        apply not_in_dom_lookup_same_exp in HVl.
        rewrite look_up_sub_comp_exp. rewrite HVl. simpl.
        destruct (var_eqdec X0 X); subst.
        eapply in_exp_then_in_left_problem with (P := P) in H1. contradiction. apply H0. trivial.
        eapply in_exp_then_in_left_problem with (P := P) in H1.
        now apply in_left_problem_then_in_problem. apply H0.
        eapply set_nocommon_inter_forall_flip in HLh.
        apply HLh. eapply in_exp_then_in_left_problem. apply H1. apply H0.
        unfold subs_equiv; split; eauto. 

        eapply σmin_comp_prop_sexp with (S:= sub_comp S ([exp_assign X0 s])%list).
        eapply set_nocommon_inter_forall_flip with (X := sexp_var Y) in HVl.
        apply In_dom_eq_dom_flip_sexp. apply not_In_dom_lookup_flip_sexp.
        apply not_in_dom_lookup_same_sexp in HVl.
        rewrite look_up_sub_comp_sexp.  rewrite HVl. now simpl.
        eapply in_exp_then_in_left_problem with (P := P) in H1. 
        now apply in_left_problem_then_in_problem. apply H0. 
        eapply set_nocommon_inter_forall_flip in HLh.
        apply HLh. eapply in_exp_then_in_left_problem. apply H1. apply H0.
        unfold subs_equiv; split; eauto.

        specialize (HEq3 X0). simpl in HEq3.
        rewrite look_up_sub_comp_exp in HEq3. rewrite in_subcomp_second_arg_exp in HEq3.
        simpl in HEq3. destruct (var_eqdec X0 X0); [assumption | contradiction].
        eapply set_nocommon_inter_forall_flip with (X:= exp_var X0) in HVl.
        apply HVl. eapply in_right_problem_then_in_problem.
        eapply in_exp_then_in_right_problem.
        2: apply H0. now left.
       
      * (* when t0 doesn't have (exp_var X) *) 
        apply HEq1.
        eapply (set_remove_3 Equation_eqdec) in  HinP.
        2: apply Eq.
        eapply push_subst_problem_exp in HinP.
        rewrite (proj1 vacous_subst_same) in HinP.
        apply HinP. eapply set_nocommon_forall_inter; intros.
        destruct X0 as [X'| Y'].
        apply <- In_dom_eq_dom_rec_exp in H2. unfold In_dom_exp in H2. simpl in H2.
        destruct (var_eqdec X X'); subst.
        now apply Hnt0. contradiction. 
        apply <- In_dom_eq_dom_rec_sexp in H2. unfold In_dom_sexp in H2. simpl in H2. contradiction.
  - intros σ τ HinP. (* unfold subs_equiv in HEq3; destruct HEq3 as [HEq3 HEq3']. *)
    destruct (Equation_eqdec (equ_s σ τ) (equ s (VarExp X))) as [Eq | nEq]; subst; try now inversion Eq.
    destruct (set_In_dec sortedvar_eqdec (exp_var X) (vars_of_sexp τ)) as [Hτ | Hnτ]; intros.
    + (* when (exp_var X) in τ *)
      apply σmin_equivs_trans with (τ  := sub_s τ (sub_comp ([exp_assign X s]) Sl)).
      rewrite (proj2 subst_comp_expand).
      apply HEq2. apply push_subst_problem_sexp.
      now apply set_remove_3.
      apply (proj2 σmin_subst_ext).
      unfold subs_equiv; split; simpl; intros; try apply σmin_equivs_refl.
      destruct (var_eqdec X X0); subst; try apply σmin_equiv_refl.
      apply σmin_equiv_trans with (t:= s).
      rewrite (proj1 vacous_subst_same). apply σmin_equiv_refl.
      apply (set_nocommon_forall_inter_flip); intros.
      eapply set_nocommon_inter_forall_flip in HLh.
      apply HLh. eapply in_exp_then_in_left_problem. apply H1. apply H0.

      apply σmin_equiv_trans with (t := sub s S'').
      apply (proj1 not_in_dom_same); split; intros.      
      eapply σmin_comp_prop_exp with (S:= sub_comp S ([exp_assign X0 s])%list).
      eapply set_nocommon_inter_forall_flip with (X:= exp_var X) in HVl.
      apply In_dom_eq_dom_flip_exp. apply not_In_dom_lookup_flip_exp.
      apply not_in_dom_lookup_same_exp in HVl.
      rewrite look_up_sub_comp_exp. rewrite HVl. simpl.
      destruct (var_eqdec X0 X); subst.
      eapply in_exp_then_in_left_problem with (P := P) in H1. contradiction. apply H0. trivial.
      eapply in_exp_then_in_left_problem with (P := P) in H1.
      now apply in_left_problem_then_in_problem. apply H0.
      eapply set_nocommon_inter_forall_flip in HLh.
      apply HLh. eapply in_exp_then_in_left_problem. apply H1. apply H0.
      unfold subs_equiv; split; eauto.


      eapply σmin_comp_prop_sexp with (S:= sub_comp S ([exp_assign X0 s])%list).
      eapply set_nocommon_inter_forall_flip with (X := sexp_var Y) in HVl.
      apply In_dom_eq_dom_flip_sexp. apply not_In_dom_lookup_flip_sexp.
      apply not_in_dom_lookup_same_sexp in HVl.
      rewrite look_up_sub_comp_sexp.  rewrite HVl. now simpl.
      eapply in_exp_then_in_left_problem with (P := P) in H1. 
      now apply in_left_problem_then_in_problem. apply H0. 
      eapply set_nocommon_inter_forall_flip in HLh.
      apply HLh. eapply in_exp_then_in_left_problem. apply H1. apply H0.
      unfold subs_equiv; split; eauto.

      specialize (HEq3 X0). simpl in HEq3.
      rewrite look_up_sub_comp_exp in HEq3. rewrite in_subcomp_second_arg_exp in HEq3.
      simpl in HEq3. destruct (var_eqdec X0 X0); [assumption | contradiction].
      eapply set_nocommon_inter_forall_flip with (X:= exp_var X0) in HVl.
      apply HVl. eapply in_right_problem_then_in_problem.
      eapply in_exp_then_in_right_problem.
      2: apply H0. now left.

    + (*when (exp_var X) not in τ*)   
      apply HEq2.
      eapply (set_remove_3 Equation_eqdec) in  HinP.
      2: apply nEq.
      eapply push_subst_problem_sexp in HinP.
      rewrite (proj2 vacous_subst_same) in HinP.
      apply HinP. eapply set_nocommon_forall_inter; intros.
      destruct X0 as [X'| Y'].
      apply <- In_dom_eq_dom_rec_exp in H1. unfold In_dom_exp in H1. simpl in H1.
      destruct (var_eqdec X X'); subst.
      now apply Hnτ. contradiction. 
      apply <- In_dom_eq_dom_rec_sexp in H1. unfold In_dom_sexp in H1. simpl in H1. contradiction.

  - (* unfold subs_equiv in *; destruct HEq3. *)
    rewrite H1 in HEq3. rewrite H1 in HEq3'.
    exists (sub_comp ([exp_assign X s])%list S'').   
    split; intros.
    specialize (HEq3 X0).
    now rewrite <- subst_comp_assoc_exp in HEq3.
    specialize (HEq3' X0).
    now rewrite <- subst_comp_assoc_sexp in HEq3'.
    (* Inst exp case end *)

  - (* Inst sexp case start *)
    intros s t HinP. (* unfold subs_equiv in HEq3; destruct HEq3 as [HEq3 HEq3']. *)  
    destruct (Equation_eqdec (equ s t) (equ_s σ (VarSExp Y))) as [Eq | nEq]; subst; try now inversion Eq. 
   destruct (set_In_dec sortedvar_eqdec (sexp_var Y) (vars_of_exp t)) as [Ht | Hnt]; intros.
    + (* when (sexp_var Y) in t *)
      apply σmin_equiv_trans with (t  := sub t (sub_comp ([sexp_assign Y σ]) Sl)).
      rewrite (proj1 subst_comp_expand).
      apply HEq1. apply push_subst_problem_exp.
      now apply set_remove_3.
      apply (proj1 σmin_subst_ext).
      unfold subs_equiv; split; simpl; intros; try apply σmin_equiv_refl.
      destruct (var_eqdec Y X); subst; try apply σmin_equivs_refl.
      apply σmin_equivs_trans with (τ:= σ).
      rewrite (proj2 vacous_subst_same). apply σmin_equivs_refl.
      apply (set_nocommon_forall_inter_flip); intros.
      eapply set_nocommon_inter_forall_flip in HLh.
      apply HLh. eapply in_sexp_then_in_left_problem. apply H1. apply H0.

      apply σmin_equivs_trans with (τ := sub_s σ S'').
      apply (proj2 not_in_dom_same); split; intros.
      eapply σmin_comp_prop_exp with (S:= sub_comp S ([sexp_assign X σ])%list).
      eapply set_nocommon_inter_forall_flip with (X := exp_var X0) in HVl.
      apply In_dom_eq_dom_flip_exp. apply not_In_dom_lookup_flip_exp.
      apply not_in_dom_lookup_same_exp in HVl.
      rewrite look_up_sub_comp_exp.  rewrite HVl. now simpl.
      eapply in_sexp_then_in_left_problem with (P := P) in H1. 
      now apply in_left_problem_then_in_problem. apply H0. 
      eapply set_nocommon_inter_forall_flip in HLh.
      apply HLh. eapply in_sexp_then_in_left_problem. apply H1. apply H0.
      unfold subs_equiv; split; eauto.
      
      eapply σmin_comp_prop_sexp with (S:= sub_comp S ([sexp_assign X σ])%list).
      eapply set_nocommon_inter_forall_flip with (X:= sexp_var Y) in HVl.
      apply In_dom_eq_dom_flip_sexp. apply not_In_dom_lookup_flip_sexp.
      apply not_in_dom_lookup_same_sexp in HVl.
      rewrite look_up_sub_comp_sexp. rewrite HVl. simpl.
      destruct (var_eqdec X Y); subst.
      eapply in_sexp_then_in_left_problem with (P := P) in H1. contradiction. apply H0. trivial.
      eapply in_sexp_then_in_left_problem with (P := P) in H1.
      now apply in_left_problem_then_in_problem. apply H0.
      eapply set_nocommon_inter_forall_flip in HLh.
      apply HLh. eapply in_sexp_then_in_left_problem. apply H1. apply H0.
      unfold subs_equiv; split; eauto. 

      specialize (HEq3' X). simpl in HEq3'.
      rewrite look_up_sub_comp_sexp in HEq3'. rewrite in_subcomp_second_arg_sexp in HEq3'.
      simpl in HEq3'. destruct (var_eqdec X X); [assumption | contradiction].
      eapply set_nocommon_inter_forall_flip with (X:= sexp_var X) in HVl.
      apply HVl. eapply in_right_problem_then_in_problem.
      eapply in_sexp_then_in_right_problem.
      2: apply H0. now left.
    + (* when (sexp_var Y) not in t *)
      apply HEq1.
      eapply (set_remove_3 Equation_eqdec) in  HinP.
      2: apply nEq.
      eapply push_subst_problem_exp in HinP.
      rewrite (proj1 vacous_subst_same) in HinP.
      apply HinP. eapply set_nocommon_forall_inter; intros.
      destruct X as [X'| Y'].
      apply <- In_dom_eq_dom_rec_exp in H1. unfold In_dom_exp in H1. simpl in H1. contradiction.
      apply <- In_dom_eq_dom_rec_sexp in H1. unfold In_dom_sexp in H1. simpl in H1. 
      destruct (var_eqdec Y Y'); subst.
      now apply Hnt. contradiction. 

  - intros σ0 τ0 HinP. (* unfold subs_equiv in HEq3; destruct HEq3 as [HEq3 HEq3']. *)   
    destruct (Equation_eqdec (equ_s σ0 τ0) (equ_s σ (VarSExp Y))) as [Eq | nEq]; intros.
    + rewrite Eq in *. simpl in *.
      inversion Eq; subst. clear Eq.
      simpl. apply σmin_equivs_trans with (τ := sub_s σ S'').
      apply (proj2 not_in_dom_same); split; intros.
      eapply σmin_comp_prop_exp with (S:= sub_comp S ([sexp_assign Y σ])%list).
      eapply set_nocommon_inter_forall_flip with (X := exp_var X) in HVl.
      apply In_dom_eq_dom_flip_exp. apply not_In_dom_lookup_flip_exp.
      apply not_in_dom_lookup_same_exp in HVl.
      rewrite look_up_sub_comp_exp.  rewrite HVl. now simpl.
      eapply in_sexp_then_in_left_problem with (P := P) in H1. 
      now apply in_left_problem_then_in_problem. apply HinP. 
      eapply set_nocommon_inter_forall_flip in HLh.
      apply HLh. eapply in_sexp_then_in_left_problem. apply H1. apply H0.
      unfold subs_equiv; split; eauto.

      eapply σmin_comp_prop_sexp with (S:= sub_comp S ([sexp_assign Y σ])%list).
      eapply set_nocommon_inter_forall_flip with (X:= sexp_var Y0) in HVl.
      apply In_dom_eq_dom_flip_sexp. apply not_In_dom_lookup_flip_sexp.
      apply not_in_dom_lookup_same_sexp in HVl.
      rewrite look_up_sub_comp_sexp. rewrite HVl. simpl.
      destruct (var_eqdec Y Y0); subst.
      eapply in_sexp_then_in_left_problem with (P := P) in H1. contradiction. apply HinP. trivial.
      eapply in_sexp_then_in_left_problem with (P := P) in H1.
      now apply in_left_problem_then_in_problem. apply HinP.
      eapply set_nocommon_inter_forall_flip in HLh.
      apply HLh. eapply in_sexp_then_in_left_problem. apply H1. apply H0.
      unfold subs_equiv; split; eauto. 

      specialize (HEq3' Y).
      rewrite look_up_sub_comp_sexp in HEq3'. rewrite in_subcomp_second_arg_sexp in HEq3'.
      simpl in HEq3'. destruct (var_eqdec Y Y); [assumption | contradiction].
      eapply set_nocommon_inter_forall_flip with (X:= sexp_var Y) in HVl.
      apply HVl. eapply in_right_problem_then_in_problem.
      eapply in_sexp_then_in_right_problem.
      2: apply H0. now left.
   + destruct (set_In_dec sortedvar_eqdec (sexp_var Y) (vars_of_sexp τ0)) as [Hτ0 | Hnτ0].
      * (* when τ0 does have (sexp_var Y) *)
        apply σmin_equivs_trans with (τ  := sub_s τ0 (sub_comp ([sexp_assign Y σ]) Sl)).
        rewrite (proj2 subst_comp_expand).
        apply HEq2. apply push_subst_problem_sexp.
        now apply set_remove_3.
        apply (proj2 σmin_subst_ext).
        unfold subs_equiv; split; simpl; intros; try apply σmin_equiv_refl.
        destruct (var_eqdec Y X); subst; try apply σmin_equivs_refl.
        apply σmin_equivs_trans with (τ:= σ).
        rewrite (proj2 vacous_subst_same). apply σmin_equivs_refl.
        apply (set_nocommon_forall_inter_flip); intros.
        eapply set_nocommon_inter_forall_flip in HLh.
        apply HLh. eapply in_sexp_then_in_left_problem. apply H1. apply H0.

        apply σmin_equivs_trans with (τ := sub_s σ S'').
        apply (proj2 not_in_dom_same); split; intros.      
        eapply σmin_comp_prop_exp with (S:= sub_comp S ([sexp_assign X σ])%list).
        eapply set_nocommon_inter_forall_flip with (X := exp_var X0) in HVl.
        apply In_dom_eq_dom_flip_exp. apply not_In_dom_lookup_flip_exp.
        apply not_in_dom_lookup_same_exp in HVl.
        rewrite look_up_sub_comp_exp.  rewrite HVl. now simpl.
        eapply in_sexp_then_in_left_problem with (P := P) in H1. 
        now apply in_left_problem_then_in_problem. apply H0. 
        eapply set_nocommon_inter_forall_flip in HLh.
        apply HLh. eapply in_sexp_then_in_left_problem. apply H1. apply H0.
        unfold subs_equiv; split; eauto.

        eapply σmin_comp_prop_sexp with (S:= sub_comp S ([sexp_assign X σ])%list).
        eapply set_nocommon_inter_forall_flip with (X:= sexp_var Y) in HVl.
        apply In_dom_eq_dom_flip_sexp. apply not_In_dom_lookup_flip_sexp.
        apply not_in_dom_lookup_same_sexp in HVl.
        rewrite look_up_sub_comp_sexp. rewrite HVl. simpl.
        destruct (var_eqdec X Y); subst.
        eapply in_sexp_then_in_left_problem with (P := P) in H1. contradiction. apply H0. trivial.
        eapply in_sexp_then_in_left_problem with (P := P) in H1.
        now apply in_left_problem_then_in_problem. apply H0.
        eapply set_nocommon_inter_forall_flip in HLh.
        apply HLh. eapply in_sexp_then_in_left_problem. apply H1. apply H0.
        unfold subs_equiv; split; eauto. 

        specialize (HEq3' X). simpl in HEq3'.
        rewrite look_up_sub_comp_sexp in HEq3'. rewrite in_subcomp_second_arg_sexp in HEq3'.
        simpl in HEq3'. destruct (var_eqdec X X); [assumption | contradiction].
        eapply set_nocommon_inter_forall_flip with (X:= sexp_var X) in HVl.
        apply HVl. eapply in_right_problem_then_in_problem.
        eapply in_sexp_then_in_right_problem.
        2: apply H0. now left.

      * (* when τ0 doesn't have (sexp_var Y) *) 
        apply HEq2.
        eapply (set_remove_3 Equation_eqdec) in  HinP.
        2: apply nEq.
        eapply push_subst_problem_sexp in HinP.
        rewrite (proj2 vacous_subst_same) in HinP.
        apply HinP. eapply set_nocommon_forall_inter; intros.
        destruct X as [X'| Y'].
        apply <- In_dom_eq_dom_rec_exp in H2. unfold In_dom_exp in H2. simpl in H2. contradiction.
       apply <- In_dom_eq_dom_rec_sexp in H2. unfold In_dom_sexp in H2. simpl in H2. 
       destruct (var_eqdec Y Y'); subst.
       now apply Hnτ0. contradiction.
   -  (* unfold subs_equiv in *; destruct HEq3. *)
    rewrite H1 in HEq3. rewrite H1 in HEq3'.
    exists (sub_comp ([sexp_assign Y σ])%list S'').   
    split; intros.
    specialize (HEq3 X).
    now rewrite <- subst_comp_assoc_exp in HEq3.
    specialize (HEq3' X).
    now rewrite <- subst_comp_assoc_sexp in HEq3'.
   - admit.
   - admit.
   - admit.
   - intros s0 t0 HinP. destruct H as [H H'].
     destruct (Equation_eqdec (equ s0 t0) (equ s (VarExp X)[(VarSExp Y)])) as [HEq | HnEq].
     + inversion HEq; subst.
       simpl. apply σmin_equiv_trans with (t := look_up_exp X Sl).       

      apply σmin_equiv_trans with (t := sub s S'').
      apply (proj1 not_in_dom_same); split; intros.      
      eapply σmin_comp_prop_exp with (S:= sub_comp (sub_comp S ([exp_assign X s])%list) ([sexp_assign Y I])).
      eapply set_nocommon_inter_forall_flip with (X:= exp_var X0) in HVl.
      apply In_dom_eq_dom_flip_exp. apply not_In_dom_lookup_flip_exp.
      apply not_in_dom_lookup_same_exp in HVl.
      rewrite look_up_sub_comp_exp.
      rewrite look_up_sub_comp_exp.
      rewrite HVl. simpl.
      destruct (var_eqdec X X0); subst.
      eapply in_exp_then_in_left_problem with (P := P) in H1. contradiction.
      apply HinP. trivial.
      eapply in_exp_then_in_left_problem with (P := P) in H1.
      now apply in_left_problem_then_in_problem. apply HinP.
      eapply set_nocommon_inter_forall_flip in HLh.
      apply HLh. eapply in_exp_then_in_left_problem. apply H1. apply H0.
      unfold subs_equiv; split; eauto.

      eapply σmin_comp_prop_sexp with (S:= sub_comp (sub_comp S ([exp_assign X s])%list) ([sexp_assign Y I])).
      eapply set_nocommon_inter_forall_flip with (X := sexp_var Y0) in HVl.
      apply In_dom_eq_dom_flip_sexp. apply not_In_dom_lookup_flip_sexp.
      apply not_in_dom_lookup_same_sexp in HVl.
      rewrite look_up_sub_comp_sexp.
      rewrite look_up_sub_comp_sexp. simpl. 
      rewrite HVl. simpl.
      destruct (var_eqdec Y Y0); subst.
      eapply in_exp_then_in_left_problem with (P := P) in H1. contradiction. apply HinP. trivial.
      eapply in_exp_then_in_left_problem with (P := P) in H1. 
      now apply in_left_problem_then_in_problem. apply HinP. 
      eapply set_nocommon_inter_forall_flip in HLh.
      apply HLh. eapply in_exp_then_in_left_problem. apply H1. apply H0.
      unfold subs_equiv; split; eauto.

      specialize (HEq3 X). simpl in HEq3.
      rewrite look_up_sub_comp_exp in HEq3.
      rewrite look_up_sub_comp_exp in HEq3.
      rewrite in_subcomp_second_arg_exp in HEq3.
      simpl in HEq3. destruct (var_eqdec X X); try contradiction.
      rewrite (proj1 vacous_subst_same) with (S := [sexp_assign Y I])in HEq3.
      assumption. apply set_nocommon_forall_inter_flip. intros.
      destruct (sortedvar_eqdec X0 (sexp_var Y)).
      subst. intro. apply H'. eapply in_exp_then_in_left_problem. apply H1. apply H0. unfold dom_rec.
      simpl. destruct (var_eqdec Y Y); try contradiction.
      destruct (sexp_eqdec I (VarSExp Y)). inversion e1. simpl. intro. destruct H2. congruence.
      trivial.
       eapply set_nocommon_inter_forall_flip with (X:= exp_var X) in HVl.
      apply HVl. eapply in_right_problem_then_in_problem.
      eapply in_exp_then_in_right_problem.
      2: apply H0. simpl. destruct (sortedvar_eqdec (sexp_var Y) (exp_var X)) as [Eq' | HnEq']; try inversion Eq'. simpl. now left.


           
       apply σmin_equiv_trans with (t := (look_up_exp X Sl)[I]).
       apply σmin_equiv_sym. apply σmin_id_exp.
       apply σmin_equiv_subst. apply σmin_equiv_refl. 
       simpl in HEq3'. specialize HEq3' with Y.
       rewrite look_up_sub_comp_sexp in HEq3'.
       rewrite in_subcomp_second_arg_sexp in HEq3'. 
       simpl in HEq3'. destruct (var_eqdec Y Y);try contradiction. now simpl in HEq3'.
       apply set_nocommon_inter_forall_flip with (X:= sexp_var Y) in HVl.
       intro. apply HVl. apply In_dom_eq_dom_rec_sexp. unfold In_dom_sexp.
       apply In_dom_eq_dom_rec_sexp in H1. unfold In_dom_sexp in H1. simpl in H1.
       rewrite in_subcomp_second_arg_sexp in H1.
       simpl in H1. contradiction. apply HVl.
       apply in_right_problem_then_in_problem. eapply in_exp_then_in_right_problem.
       2: apply HinP. simpl.
       destruct (sortedvar_eqdec (sexp_var Y) (exp_var X)); try congruence.
       simpl. right. now left.

       
              
     + destruct (set_In_dec sortedvar_eqdec (exp_var X) (vars_of_exp t0)) as [HXt0 | HXnt0]; intros.
       * destruct (set_In_dec sortedvar_eqdec (sexp_var Y) (vars_of_exp t0)) as [HYt0 | HYnt0]; intros.
         **  (* when t0 have X  and Y*)
             apply σmin_equiv_trans with (t  := sub t0 (sub_comp (sub_comp ([exp_assign X s]) ([sexp_assign Y I])) Sl)).
             rewrite (proj1 subst_comp_expand).
             rewrite (proj1 subst_comp_expand).
             apply HEq1. apply push_subst_problem_exp.
             apply push_subst_problem_exp.
             now apply set_remove_3.
             apply (proj1 σmin_subst_ext).
             unfold subs_equiv; split; simpl; intros.
             destruct (var_eqdec X X0); subst; try apply σmin_equiv_refl.
             rewrite (proj1 vacous_subst_same) with (S:= ([sexp_assign Y I])).
             apply σmin_equiv_trans with (t:=s).
             rewrite (proj1 vacous_subst_same). apply σmin_equiv_refl.
             apply set_nocommon_forall_inter_flip; intros.
             eapply set_nocommon_inter_forall_flip in HLh.
             apply HLh. eapply in_exp_then_in_left_problem. apply H1. apply H0.

             (* repeat case start*)
             
      apply σmin_equiv_trans with (t := sub s S'').
      apply (proj1 not_in_dom_same); split; intros.      
      eapply σmin_comp_prop_exp with (S:= sub_comp (sub_comp S ([exp_assign X0 s])%list) ([sexp_assign Y I])).
      eapply set_nocommon_inter_forall_flip with (X:= exp_var X) in HVl.
      apply In_dom_eq_dom_flip_exp. apply not_In_dom_lookup_flip_exp.
      apply not_in_dom_lookup_same_exp in HVl.
      rewrite look_up_sub_comp_exp.
      rewrite look_up_sub_comp_exp.
      rewrite HVl. simpl.
      destruct (var_eqdec X0 X); subst.
      eapply in_exp_then_in_left_problem with (P := P) in H1. contradiction.
      apply H0. trivial.
      eapply in_exp_then_in_left_problem with (P := P) in H1.
      now apply in_left_problem_then_in_problem. apply H0.
      eapply set_nocommon_inter_forall_flip in HLh.
      apply HLh. eapply in_exp_then_in_left_problem. apply H1. apply H0.
      unfold subs_equiv; split; eauto.

      eapply σmin_comp_prop_sexp with (S:= sub_comp (sub_comp S ([exp_assign X0 s])%list) ([sexp_assign Y I])).
      eapply set_nocommon_inter_forall_flip with (X := sexp_var Y0) in HVl.
      apply In_dom_eq_dom_flip_sexp. apply not_In_dom_lookup_flip_sexp.
      apply not_in_dom_lookup_same_sexp in HVl.
      rewrite look_up_sub_comp_sexp.
      rewrite look_up_sub_comp_sexp. simpl. 
      rewrite HVl. simpl.
      destruct (var_eqdec Y Y0); subst.
      eapply in_exp_then_in_left_problem with (P := P) in H1. contradiction. apply H0. trivial.
      eapply in_exp_then_in_left_problem with (P := P) in H1. 
      now apply in_left_problem_then_in_problem. apply H0. 
      eapply set_nocommon_inter_forall_flip in HLh.
      apply HLh. eapply in_exp_then_in_left_problem. apply H1. apply H0.
      unfold subs_equiv; split; eauto.

      specialize (HEq3 X0). simpl in HEq3.
      rewrite look_up_sub_comp_exp in HEq3.
      rewrite look_up_sub_comp_exp in HEq3.
      rewrite in_subcomp_second_arg_exp in HEq3.
      simpl in HEq3. destruct (var_eqdec X0 X0); try contradiction.
      rewrite (proj1 vacous_subst_same) with (S := [sexp_assign Y I])in HEq3.
      assumption. apply set_nocommon_forall_inter_flip. intros.
      destruct (sortedvar_eqdec X (sexp_var Y)).
      subst. intro. apply H'. eapply in_exp_then_in_left_problem. apply H1. apply H0. unfold dom_rec.
      simpl. destruct (var_eqdec Y Y); try contradiction.
      destruct (sexp_eqdec I (VarSExp Y)). inversion e1. simpl. intro. destruct H2. congruence.
      trivial.
       eapply set_nocommon_inter_forall_flip with (X:= exp_var X0) in HVl.
      apply HVl. eapply in_right_problem_then_in_problem.
      eapply in_exp_then_in_right_problem.
      2: apply H0. simpl. destruct (sortedvar_eqdec (sexp_var Y) (exp_var X0)) as [Eq' | HnEq']; try inversion Eq'. simpl. now left.         
             
      (* repeat case end *)

      (* this annoying reasoning can be eliminated by probably generalizing look_up *)
      apply set_nocommon_forall_inter_flip. intros.
      destruct (sortedvar_eqdec X (sexp_var Y)).
      subst. intro. apply H'. eapply in_exp_then_in_left_problem. apply H1. apply H0. unfold dom_rec.
      simpl. destruct (var_eqdec Y Y); try contradiction.
      destruct (sexp_eqdec I (VarSExp Y)). inversion e0. simpl. intro. destruct H2. congruence.
      trivial.

      destruct (var_eqdec Y X0) as [eqyx0 | neqyx0]; try apply σmin_equivs_refl. subst.
      simpl in HEq3'. specialize HEq3' with X0.
      rewrite look_up_sub_comp_sexp in HEq3'.
      rewrite in_subcomp_second_arg_sexp in HEq3'. 
      simpl in HEq3'. destruct (var_eqdec X0 X0);try contradiction. now simpl in HEq3'.
      apply set_nocommon_inter_forall_flip with (X:= sexp_var X0) in HVl.
      intro. apply HVl. apply In_dom_eq_dom_rec_sexp. unfold In_dom_sexp.
      apply In_dom_eq_dom_rec_sexp in H1. unfold In_dom_sexp in H1. simpl in H1.
      rewrite in_subcomp_second_arg_sexp in H1.
      simpl in H1. contradiction. apply HVl.
      apply in_right_problem_then_in_problem. eapply in_exp_then_in_right_problem.
      2: apply HinP. simpl.
      destruct (sortedvar_eqdec (sexp_var X0) (exp_var X)); try congruence.

    **         (* when t0 have X  but not Y*)
             apply σmin_equiv_trans with (t  := sub t0 (sub_comp ([exp_assign X s]) Sl)).
             rewrite (proj1 subst_comp_expand).
             apply HEq1.
             eapply (set_remove_3 (Equation_eqdec)) in HinP; trivial.
             eapply (push_subst_problem_exp) in HinP.
             eapply (push_subst_problem_exp)  with (S:= [sexp_assign Y I]) in HinP.
             erewrite (proj1 vacous_subst_same) with (S:=[sexp_assign Y I]) in HinP.
             apply HinP.
             apply (set_nocommon_forall_inter). intros.
             intro. apply HYnt0.
             eapply (proj1 exp_sexp_desubst).
             unfold dom_rec in H2. simpl in H2. destruct (var_eqdec Y Y); try contradiction.
             destruct (sexp_eqdec I (VarSExp Y)); try contradiction. simpl in H2. destruct H2; try contradiction. rewrite <- e0 in H3. apply H3. simpl. congruence. simpl.
             intro. apply H'. eapply in_exp_then_in_left_problem. apply H4. apply H0. apply HnEq.
              apply (proj1 σmin_subst_ext).
             unfold subs_equiv; split; simpl; intros; try apply σmin_equivs_refl.
             destruct (var_eqdec X X0); subst; try apply σmin_equiv_refl.
             apply σmin_equiv_trans with (t:=s).
             rewrite (proj1 vacous_subst_same). apply σmin_equiv_refl.
             apply set_nocommon_forall_inter_flip; intros.
             eapply set_nocommon_inter_forall_flip in HLh.
             apply HLh. eapply in_exp_then_in_left_problem. apply H1. apply H0.


             
             
             (* repeat case start*)
             
      apply σmin_equiv_trans with (t := sub s S'').
      apply (proj1 not_in_dom_same); split; intros.      
      eapply σmin_comp_prop_exp with (S:= sub_comp (sub_comp S ([exp_assign X0 s])%list) ([sexp_assign Y I])).
      eapply set_nocommon_inter_forall_flip with (X:= exp_var X) in HVl.
      apply In_dom_eq_dom_flip_exp. apply not_In_dom_lookup_flip_exp.
      apply not_in_dom_lookup_same_exp in HVl.
      rewrite look_up_sub_comp_exp.
      rewrite look_up_sub_comp_exp.
      rewrite HVl. simpl.
      destruct (var_eqdec X0 X); subst.
      eapply in_exp_then_in_left_problem with (P := P) in H1. contradiction.
      apply H0. trivial.
      eapply in_exp_then_in_left_problem with (P := P) in H1.
      now apply in_left_problem_then_in_problem. apply H0.
      eapply set_nocommon_inter_forall_flip in HLh.
      apply HLh. eapply in_exp_then_in_left_problem. apply H1. apply H0.
      unfold subs_equiv; split; eauto.

      eapply σmin_comp_prop_sexp with (S:= sub_comp (sub_comp S ([exp_assign X0 s])%list) ([sexp_assign Y I])).
      eapply set_nocommon_inter_forall_flip with (X := sexp_var Y0) in HVl.
      apply In_dom_eq_dom_flip_sexp. apply not_In_dom_lookup_flip_sexp.
      apply not_in_dom_lookup_same_sexp in HVl.
      rewrite look_up_sub_comp_sexp.
      rewrite look_up_sub_comp_sexp. simpl. 
      rewrite HVl. simpl.
      destruct (var_eqdec Y Y0); subst.
      eapply in_exp_then_in_left_problem with (P := P) in H1. contradiction. apply H0. trivial.
      eapply in_exp_then_in_left_problem with (P := P) in H1. 
      now apply in_left_problem_then_in_problem. apply H0. 
      eapply set_nocommon_inter_forall_flip in HLh.
      apply HLh. eapply in_exp_then_in_left_problem. apply H1. apply H0.
      unfold subs_equiv; split; eauto.

      specialize (HEq3 X0). simpl in HEq3.
      rewrite look_up_sub_comp_exp in HEq3.
      rewrite look_up_sub_comp_exp in HEq3.
      rewrite in_subcomp_second_arg_exp in HEq3.
      simpl in HEq3. destruct (var_eqdec X0 X0); try contradiction.
      rewrite (proj1 vacous_subst_same) with (S := [sexp_assign Y I])in HEq3.
      assumption. apply set_nocommon_forall_inter_flip. intros.
      destruct (sortedvar_eqdec X (sexp_var Y)).
      subst. intro. apply H'. eapply in_exp_then_in_left_problem. apply H1. apply H0. unfold dom_rec.
      simpl. destruct (var_eqdec Y Y); try contradiction.
      destruct (sexp_eqdec I (VarSExp Y)). inversion e1. simpl. intro. destruct H2. congruence.
      trivial.
       eapply set_nocommon_inter_forall_flip with (X:= exp_var X0) in HVl.
      apply HVl. eapply in_right_problem_then_in_problem.
      eapply in_exp_then_in_right_problem.
      2: apply H0. simpl. destruct (sortedvar_eqdec (sexp_var Y) (exp_var X0)) as [Eq' | HnEq']; try inversion Eq'. simpl. now left.


       *  destruct (set_In_dec sortedvar_eqdec (sexp_var Y) (vars_of_exp t0)) as [HYt0 | HYnt0]; intros.
          ** (* when t0 not have X but have Y *)

            apply σmin_equiv_trans with (t  := sub t0 (sub_comp ([sexp_assign Y I]) Sl)).
             rewrite (proj1 subst_comp_expand).
             apply HEq1.
             eapply (set_remove_3 (Equation_eqdec)) in HinP; trivial.
             eapply (push_subst_problem_exp) with (S := [exp_assign X s]) in HinP.
             eapply (push_subst_problem_exp) with (S := [sexp_assign Y I]) in HinP.
             rewrite (proj1 vacous_subst_same) with (S:=[exp_assign X s]) in HinP.
             apply HinP.
             apply (set_nocommon_forall_inter). intros.
             unfold dom_rec in H2. simpl in H2. destruct (var_eqdec X X); try contradiction.
             destruct (exp_eqdec s (VarExp X)); try contradiction. simpl in H2. destruct H2; try contradiction. now rewrite <- H2.
             apply HnEq.
             apply (proj1 σmin_subst_ext).
             unfold subs_equiv; split; simpl; intros; try apply σmin_equiv_refl.
             destruct (var_eqdec Y X0); subst; try apply σmin_equivs_refl.
             simpl in HEq3'. specialize HEq3' with X0.
             rewrite look_up_sub_comp_sexp in HEq3'.
             rewrite in_subcomp_second_arg_sexp in HEq3'. 
             simpl in HEq3'. destruct (var_eqdec X0 X0);try contradiction. now simpl in HEq3'.
             apply set_nocommon_inter_forall_flip with (X:= sexp_var X0) in HVl.
             intro. apply HVl. apply In_dom_eq_dom_rec_sexp. unfold In_dom_sexp.
             apply In_dom_eq_dom_rec_sexp in H1. unfold In_dom_sexp in H1. simpl in H1.
             rewrite in_subcomp_second_arg_sexp in H1.
             simpl in H1. contradiction. apply HVl.
             apply in_right_problem_then_in_problem. eapply in_exp_then_in_right_problem.
             2: apply HinP. simpl.
             destruct (sortedvar_eqdec (sexp_var X0) (exp_var X)); try congruence.
          **  apply σmin_equiv_trans with (t  := sub t0 Sl).
              apply HEq1.
             eapply (set_remove_3 (Equation_eqdec)) in HinP; trivial.
             eapply (push_subst_problem_exp) with (S := [exp_assign X s]) in HinP.
             eapply (push_subst_problem_exp) with (S := [sexp_assign Y I]) in HinP.
             rewrite (proj1 vacous_subst_same) with (S:=[exp_assign X s]) in HinP.
             rewrite (proj1 vacous_subst_same) with (S:=[sexp_assign Y I]) in HinP. 
             apply HinP; trivial.
             apply (set_nocommon_forall_inter). intros.
             unfold dom_rec in H2. simpl in H2. destruct (var_eqdec Y Y); try contradiction.
             destruct (sexp_eqdec I (VarSExp Y)); try contradiction. simpl in H2. destruct H2; try contradiction. now rewrite <- H2.
             apply (set_nocommon_forall_inter). intros.
             unfold dom_rec in H2. simpl in H2. destruct (var_eqdec X X); try contradiction.
             destruct (exp_eqdec s (VarExp X)); try contradiction. simpl in H2. destruct H2; try contradiction. now rewrite <- H2.
             trivial. apply σmin_equiv_refl.
   - admit.
   - subst.
     unfold subs_equiv.
     exists (sub_comp ([exp_assign X s]) (sub_comp ([sexp_assign Y I]) S'')).
     split; intros.
     
     specialize (HEq3 X0).
     rewrite <- subst_comp_assoc_exp in HEq3.
     now rewrite <-  subst_comp_assoc_exp in HEq3.

     specialize (HEq3' X0).
     rewrite <- subst_comp_assoc_sexp in HEq3'.
     now rewrite <-  subst_comp_assoc_sexp in HEq3'.     
Qed.      


Lemma match_step_validity : forall T T', smatch T T' -> valid_tuple T -> valid_tuple T'.
Proof.
  intros T T' H H'.
  unfold valid_tuple in H'.  
  destruct H; intros; simpl in H'; unfold valid_tuple; repeat split; simpl;apply set_nocommon_forall_inter; intros.
  1,2:  destruct X as [X | Y];
    (eapply set_nocommon_inter_forall in H'; revgoals;
    [apply H0 | intro; apply H'; eapply problem_var_remove_one_mem; eauto]).
  -   eapply set_nocommon_inter_forall in H'. 2: apply H0.
       intro. apply H'.
       apply problem_var_remove_one_mem in H1.
       apply problem_var_ext_vars in H1.
       apply problem_var_ext_vars in H1.
       apply H1.
       simpl. intro.
       apply H'. apply set_union_elim in H2.
       destruct H2.
       apply in_left_problem_then_in_problem.
       eapply in_exp_then_in_left_problem. 2: apply H.
       simpl. now apply set_union_intro1.
       apply in_right_problem_then_in_problem.
       eapply in_exp_then_in_right_problem; swap 1 2.
       apply H. simpl. now apply set_union_intro1.

       simpl. intro. apply H'. apply set_union_elim in H2. destruct H2.
       apply in_left_problem_then_in_problem.
       eapply in_exp_then_in_left_problem. 2: apply H.
       simpl. now apply set_union_intro2.
       apply in_right_problem_then_in_problem.
       eapply in_exp_then_in_right_problem; swap 1 2.
       apply H. simpl. now apply set_union_intro2.       
  -  eapply set_nocommon_inter_forall in H'. 2: apply H0.
     intro. apply H'.
     apply problem_var_remove_one_mem in H1.
     apply problem_var_ext_vars in H1.
     contradiction.
     intro. apply H'.
     apply set_union_elim in H2. destruct H2.
     apply in_left_problem_then_in_problem.     
     eapply in_exp_then_in_left_problem. 2: apply H.
     now simpl.
     apply in_right_problem_then_in_problem.     
     eapply in_exp_then_in_right_problem. 2: apply H.
     now simpl.


  -  eapply set_nocommon_inter_forall in H'. 2: apply H0.
       intro. apply H'.
       apply problem_var_remove_one_mem in H1.
       apply problem_var_ext_vars in H1.
       apply problem_var_ext_vars in H1.
       apply H1.
       simpl. intro.
       apply H'. apply set_union_elim in H2.
       destruct H2.
       apply in_left_problem_then_in_problem.
       eapply in_exp_then_in_left_problem. 2: apply H.
       simpl. now apply set_union_intro1.
       apply in_right_problem_then_in_problem.
       eapply in_exp_then_in_right_problem; swap 1 2.
       apply H. simpl. now apply set_union_intro1.

       simpl. intro. apply H'. apply set_union_elim in H2. destruct H2.
       apply in_left_problem_then_in_problem.
       eapply in_exp_then_in_left_problem. 2: apply H.
       simpl. now apply set_union_intro2.
       apply in_right_problem_then_in_problem.
       eapply in_exp_then_in_right_problem; swap 1 2.
       apply H. simpl. now apply set_union_intro2.       
   - eapply set_nocommon_inter_forall in H'. 2: apply H0.
       intro. apply H'.
       apply problem_var_remove_one_mem in H1.
       apply problem_var_ext_vars in H1.
       apply problem_var_ext_vars in H1.
       apply H1.
       simpl. intro.
       apply H'. apply set_union_elim in H2.
       destruct H2.
       apply in_left_problem_then_in_problem.
       eapply in_sexp_then_in_left_problem. 2: apply H.
       simpl. now apply set_union_intro1.
       apply in_right_problem_then_in_problem.
       eapply in_sexp_then_in_right_problem; swap 1 2.
       apply H. simpl. now apply set_union_intro1.

       simpl. intro. apply H'. apply set_union_elim in H2. destruct H2.
       apply in_left_problem_then_in_problem.
       eapply in_sexp_then_in_left_problem. 2: apply H.
       simpl. now apply set_union_intro2.
       apply in_right_problem_then_in_problem.
       eapply in_sexp_then_in_right_problem; swap 1 2.
       apply H. simpl. now apply set_union_intro2.       

   -   eapply set_nocommon_inter_forall in H'. 2: apply H0.
       intro. apply H'.
       apply problem_var_remove_one_mem in H1.
       apply problem_var_ext_vars in H1.
       apply problem_var_ext_vars in H1.
       apply H1.
       simpl. intro.
       apply H'. apply set_union_elim in H2.
       destruct H2.
       apply in_left_problem_then_in_problem.
       eapply in_sexp_then_in_left_problem. 2: apply H.
       simpl. now apply set_union_intro1.
       apply in_right_problem_then_in_problem.
       eapply in_sexp_then_in_right_problem; swap 1 2.
       apply H. simpl. now apply set_union_intro1.

       simpl. intro. apply H'. apply set_union_elim in H2. destruct H2.
       apply in_left_problem_then_in_problem.
       eapply in_sexp_then_in_left_problem. 2: apply H.
       simpl. now apply set_union_intro2.
       apply in_right_problem_then_in_problem.
       eapply in_sexp_then_in_right_problem; swap 1 2.
       apply H. simpl. now apply set_union_intro2.       
      
   
      
   -    eapply set_nocommon_inter_forall in H'. 2: apply H0.
         intro. apply H'.
         apply problem_var_remove_one_mem in H1.
         apply problem_var_ext_vars in H1. contradiction.
         simpl. intro. apply H'.
         apply set_union_elim in H2. destruct H2.

         apply in_left_problem_then_in_problem.
         eapply in_exp_then_in_left_problem; swap 1 2.
         apply H. simpl.
         apply set_union_elim in H2. destruct H2.
         now apply set_union_intro1.
         now repeat apply set_union_intro2.

         apply in_right_problem_then_in_problem.
         eapply in_exp_then_in_right_problem; swap 1 2.
         apply H. simpl.
         apply set_union_elim in H2. destruct H2.
         now apply set_union_intro1.
         now repeat apply set_union_intro2.

     
  -     eapply set_nocommon_inter_forall in H'. 2: apply H0.
         intro. apply H'.
         apply problem_var_remove_one_mem in H1.
         apply problem_var_ext_vars in H1. contradiction.
         simpl. intro. apply H'.
         apply set_union_elim in H2. destruct H2.

         apply in_left_problem_then_in_problem.
         eapply in_sexp_then_in_left_problem; swap 1 2.
         apply H. simpl.
         apply set_union_elim in H2. destruct H2.
         apply set_union_elim in H2. destruct H2.
         now apply set_union_intro1.
         apply set_union_intro2. apply set_union_intro1.
         now repeat apply set_union_intro2.
         now repeat apply set_union_intro2.

         apply in_right_problem_then_in_problem.
         eapply in_sexp_then_in_right_problem; swap 1 2.
         apply H. simpl.
         apply set_union_elim in H2. destruct H2.
         now apply set_union_intro1.
         now repeat apply set_union_intro2.
  

         
  -     eapply set_nocommon_inter_forall in H'. 2: apply H0.
         intro. apply H'.
         apply problem_var_remove_one_mem in H1.
         apply problem_var_ext_vars in H1. contradiction.
         simpl. intro. apply H'.
         apply set_union_elim in H2. destruct H2.

         apply in_left_problem_then_in_problem.
         eapply in_sexp_then_in_left_problem; swap 1 2.
         apply H. simpl. apply set_union_elim in H2.
         destruct H2. apply set_union_elim in H2.
         destruct H2. now repeat apply set_union_intro1.
         apply set_union_intro2. now apply set_union_intro1.
         now repeat apply set_union_intro2.
       
         apply in_right_problem_then_in_problem.
         eapply in_sexp_then_in_right_problem; swap 1 2.
         apply H. simpl.
         apply set_union_elim in H2. destruct H2.
         now apply set_union_intro1.
         now repeat apply set_union_intro2.

    
  -  eapply set_nocommon_inter_forall in H'. 2: apply H0.
         intro. apply H'.
         apply problem_var_remove_one_mem in H1.
         apply problem_var_ext_vars in H1. contradiction.
         simpl. intro. apply H'.
         apply set_union_elim in H2. destruct H2.

         apply in_left_problem_then_in_problem.
         eapply in_exp_then_in_left_problem; swap 1 2.
         apply H. simpl. apply set_union_elim in H2.
         destruct H2. rewrite set_union_assoc. now apply set_union_intro1.
         now repeat apply set_union_intro2.

         apply in_right_problem_then_in_problem.
         eapply in_exp_then_in_right_problem; swap 1 2.
         apply H. simpl.
         apply set_union_elim in H2. destruct H2.
         now apply set_union_intro1.
         now repeat apply set_union_intro2.


   -     eapply set_nocommon_inter_forall in H'. 2: apply H0.
         intro. apply H'.
         apply problem_var_remove_one_mem in H1.
         apply problem_var_ext_vars in H1. contradiction.
         simpl. intro. apply H'.
         apply set_union_elim in H2. destruct H2.

         apply in_left_problem_then_in_problem.
         eapply in_exp_then_in_left_problem; swap 1 2.
         apply H. simpl. apply set_union_elim in H2.
         destruct H2. apply set_union_elim in H2.
         destruct H2.  now repeat apply set_union_intro1.
         apply set_union_intro2. now apply set_union_intro1.
         now repeat apply set_union_intro2.

         apply in_right_problem_then_in_problem.
         eapply in_exp_then_in_right_problem; swap 1 2.
         apply H. now simpl. 
        
    
  - destruct X0 as [X' | Y']; subst.
    + destruct (var_eqdec X X') as [Eq | nEq]; intros; subst.
      *  apply problem_X_clear; trivial.
         split; intro.
         simpl in H1. apply H. eapply in_exp_then_in_left_problem. apply H1. apply H0.
         apply H. eapply problem_lhvar_remove_one_mem. apply H1.         
         
      * apply sub_comp_var_diff_left in H2; simpl; try congruence.
        intro. apply problem_vars_desubst in H1; simpl; try congruence.
        apply problem_var_remove_one_mem in H1.
        apply set_nocommon_inter_forall with (X:= exp_var X') in H'; eauto.
        apply set_nocommon_inter_forall with (X:= exp_var X') in H'; eauto.
        intro. apply H'. apply in_left_problem_then_in_problem.
        eapply in_exp_then_in_left_problem. apply H3. apply H0.
 
    + apply sub_comp_var_diff_left in H2; simpl; try congruence.
      intro. apply problem_vars_desubst in H1; simpl; try congruence.
      apply problem_var_remove_one_mem in H1.
      apply set_nocommon_inter_forall with (X:= sexp_var Y') in H'; eauto.
      apply set_nocommon_inter_forall with (X:= sexp_var Y') in H'; eauto.
      intro. apply H'. apply in_left_problem_then_in_problem.
      eapply in_exp_then_in_left_problem. apply H3. apply H0.
  - destruct X as [X' | Y']; subst.
    + apply sub_comp_var_diff_left in H2; simpl; try congruence.
      intro. apply problem_vars_desubst in H1; simpl; try congruence.
      apply problem_var_remove_one_mem in H1.
      apply set_nocommon_inter_forall with (X:= exp_var X') in H'; eauto.
      apply set_nocommon_inter_forall with (X:= exp_var X') in H'; eauto.
      intro. apply H'. apply in_left_problem_then_in_problem.
      eapply in_sexp_then_in_left_problem. apply H3. apply H0.
    + destruct (var_eqdec Y Y') as [Eq | nEq]; intros; subst.
      *  apply problem_X_clear; trivial.
         split; intro.
         simpl in H1. apply H. eapply in_sexp_then_in_left_problem. apply H1. apply H0.
         apply H. eapply problem_lhvar_remove_one_mem. apply H1.         
      * apply sub_comp_var_diff_left in H2; simpl; try congruence.
        intro. apply problem_vars_desubst in H1; simpl; try congruence.
        apply problem_var_remove_one_mem in H1.
        apply set_nocommon_inter_forall with (X:= sexp_var Y') in H'; eauto.
        apply set_nocommon_inter_forall with (X:= sexp_var Y') in H'; eauto.
        intro. apply H'. apply in_left_problem_then_in_problem.
        eapply in_sexp_then_in_left_problem. apply H3. apply H0.
 
Qed.    



Lemma match_step_lhvar_dom_preservation : forall T T' Sl, smatch T T' ->
                                                     set_inter sortedvar_eqdec  (lhvars_Probl (snd T)) (dom_rec Sl) = [] ->
                                                     set_inter sortedvar_eqdec  (lhvars_Probl (snd T')) (dom_rec Sl) = [].

Proof.
  intros.
  destruct H; simpl in H0; apply set_nocommon_forall_inter;  intros.
  - simpl in H1.
    eapply set_nocommon_inter_forall in H0. apply H0.
    eapply problem_lhvar_remove_one_mem. apply H1.
  - simpl in H1.
    eapply set_nocommon_inter_forall in H0. apply H0.
    eapply problem_lhvar_remove_one_mem. apply H1.
  - simpl in H1.
    apply problem_lhvar_remove_one_mem in H1.
    apply lhvar_ext_vars in H1.
    apply lhvar_ext_vars in H1.
    eapply set_nocommon_inter_forall in H0. apply H0. apply H1.
    simpl. intros. eapply in_exps_then_in_left_problem; swap 1 2.
    apply H.  simpl. now apply set_union_intro1.
    simpl. intros. eapply in_exps_then_in_left_problem with (e:= equ (App s t) (App s' t')); swap 1 2.
    apply set_add_intro. now right.
    simpl. now apply set_union_intro2.
  -  simpl in H1.
    apply problem_lhvar_remove_one_mem in H1.
    apply lhvar_ext_vars in H1.
    eapply set_nocommon_inter_forall in H0. apply H0. apply H1.
    simpl. intros. eapply in_exps_then_in_left_problem; swap 1 2. 
    apply H. now simpl. 
  - simpl in H1.
    apply problem_lhvar_remove_one_mem in H1.
    apply lhvar_ext_vars in H1.
    apply lhvar_ext_vars in H1.
    eapply set_nocommon_inter_forall in H0. apply H0. apply H1.
    simpl. intros. eapply in_exps_then_in_left_problem; swap 1 2.
    apply H.  simpl. now apply set_union_intro1.
    simpl. intros. eapply in_exps_then_in_left_problem with (e:= equ (s[σ]) (s'[σ'])); swap 1 2.
    apply set_add_intro. now right.
    simpl. now apply set_union_intro2.
  - simpl in H1.
    apply problem_lhvar_remove_one_mem in H1.
    apply lhvar_ext_vars in H1.
    apply lhvar_ext_vars in H1.
    eapply set_nocommon_inter_forall in H0. apply H0. apply H1.
    simpl. intros. eapply in_exps_then_in_left_problem; swap 1 2.
    apply H.  simpl. now apply set_union_intro1.
    simpl. intros. eapply in_exps_then_in_left_problem with (e:= equ_s (s .: σ) (s' .: σ')); swap 1 2.
    apply set_add_intro. now right.
    simpl. now apply set_union_intro2.
 - simpl in H1.
    apply problem_lhvar_remove_one_mem in H1.
    apply lhvar_ext_vars in H1.
    apply lhvar_ext_vars in H1.
    eapply set_nocommon_inter_forall in H0. apply H0. apply H1.
    simpl. intros. eapply in_exps_then_in_left_problem; swap 1 2.
    apply H.  simpl. now apply set_union_intro1.
    simpl. intros. eapply in_exps_then_in_left_problem with (e:= equ_s (σ >> τ) (σ' >> τ')); swap 1 2.
    apply set_add_intro. now right.
    simpl. now apply set_union_intro2.
 -  simpl in H1.
    apply problem_lhvar_remove_one_mem in H1.
    apply lhvar_ext_vars in H1.
    eapply set_nocommon_inter_forall in H0. apply H0. apply H1. 
    intros. eapply in_exp_then_in_left_problem; swap 1 2. apply H. simpl.
    simpl in H2. apply set_union_elim in H2. destruct H2.
    now apply set_union_intro1.
    now repeat apply set_union_intro2.
    
 -  simpl in H1.
    apply problem_lhvar_remove_one_mem in H1.
    apply lhvar_ext_vars in H1.
    eapply set_nocommon_inter_forall in H0. apply H0. apply H1.
    intros. eapply in_sexp_then_in_left_problem; swap 1 2. apply H. simpl.
    simpl in H2. now rewrite set_union_assoc. 

    

 -  simpl in H1.
    apply problem_lhvar_remove_one_mem in H1.
    apply lhvar_ext_vars in H1.
    eapply set_nocommon_inter_forall in H0. apply H0. apply H1.
    intros. eapply in_sexp_then_in_left_problem; swap 1 2. apply H. simpl.
    simpl in H2. apply set_union_elim in H2. destruct H2.
    apply set_union_elim in H2. destruct H2.
    now repeat apply set_union_intro1.
    apply set_union_intro2. now apply set_union_intro1.
    now repeat apply set_union_intro2.

  -  simpl in H1.
    apply problem_lhvar_remove_one_mem in H1.
    apply lhvar_ext_vars in H1.
    eapply set_nocommon_inter_forall in H0. apply H0. apply H1.
    intros. eapply in_exp_then_in_left_problem; swap 1 2. apply H. simpl.
    simpl in H2. now rewrite set_union_assoc.

   - simpl in H1.
    apply problem_lhvar_remove_one_mem in H1.
    apply lhvar_ext_vars in H1.
    eapply set_nocommon_inter_forall in H0. apply H0. apply H1.
    intros. eapply in_exp_then_in_left_problem; swap 1 2. apply H. simpl.
    simpl in H2. apply set_union_elim in H2. destruct H2.
    apply set_union_elim in H2. destruct H2.
    now repeat apply set_union_intro1.
    apply set_union_intro2. now apply set_union_intro1.
    now repeat apply set_union_intro2.


   
 -  simpl in H3.
    destruct X0 as [X' | Y'].
    + destruct (var_eqdec X X') as [ | HnEq]; subst.
      intro. apply in_left_problem_then_in_problem in H3. revert H3.
      eapply problem_X_clear; repeat split; eauto.
      simpl. intro. apply H. eapply in_exps_then_in_left_problem; swap 1 2.
      apply H1. simpl. apply H3.
      intro.  apply problem_lhvar_remove_one_mem in H3.
      contradiction.   
     apply lhvars_desubst in H3; eauto.
     apply problem_lhvar_remove_one_mem in H3.
     eapply set_nocommon_inter_forall in H3; eauto.
    +  apply lhvars_desubst in H3; eauto.
     apply problem_lhvar_remove_one_mem in H3.
     eapply set_nocommon_inter_forall in H3; eauto.
 - simpl in H3.
    destruct X as [X' | Y'].
    + apply lhvars_desubst in H3; eauto.
     apply problem_lhvar_remove_one_mem in H3.
     eapply set_nocommon_inter_forall in H3; eauto.
    +  destruct (var_eqdec Y Y') as [ | HnEq]; subst.
      intro. apply in_left_problem_then_in_problem in H3. revert H3.
      eapply problem_X_clear; repeat split; eauto.
      simpl. intro. apply H. eapply in_exps_then_in_left_problem; swap 1 2.
      apply H1. simpl. apply H3.
      intro.  apply problem_lhvar_remove_one_mem in H3.
      contradiction.   
     apply lhvars_desubst in H3; eauto.
     apply problem_lhvar_remove_one_mem in H3.
     eapply set_nocommon_inter_forall in H3; eauto.
Qed.


Lemma soundness_match : forall Sl T T',

      valid_tuple T ->

       set_inter sortedvar_eqdec (dom_rec Sl)  (lhvars_Probl (snd T)) = [] -> 

      star smatch T T' ->

      match_sol Sl T' -> match_sol Sl T.
Proof.
  intros.
  induction H1; intros.
  - assumption.
  - apply match_sol_preservation with (T' := y); eauto.
    apply IHstar; eauto.
    eapply match_step_validity; eauto.
    rewrite set_nocommon_3_4. eapply match_step_lhvar_dom_preservation. apply H1.
    now rewrite set_nocommon_3_4.   
Qed.    
