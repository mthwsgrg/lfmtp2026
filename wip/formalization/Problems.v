Require Export Substs.

Inductive Equation : Set :=
| equ : exp -> exp -> Equation
| equ_s : sexp -> sexp -> Equation.

Definition left_eqn_vars (eq: Equation) : set SortedVar :=
  match eq with
  | equ s t => vars_of_exp s
  | equ_s σ τ => vars_of_sexp σ
  end.

Definition right_eqn_vars (eq: Equation) : set SortedVar :=
  match eq with
  | equ s t => vars_of_exp t
  | equ_s σ τ => vars_of_sexp τ
  end.




Definition Problem := set Equation.   
Definition Tuple := (Subst * Problem).


Fixpoint subs_Problem_right (P : Problem) (S : Subst) : Problem :=
  match P with
    | [] => []
    | (equ s t )::P0 => (equ s (sub t S))::(subs_Problem_right P0 S)
    | (equ_s σ τ )::P0 => (equ_s σ (sub_s τ S))::(subs_Problem_right P0 S) 
  end.


Lemma Equation_eqdec : forall (e1 e2: Equation), {e1 = e2} + {e1 <> e2}.
Proof.
  intros.
  destruct e1.
  - destruct e2.
    case (exp_eqdec e e1); intros.
    case (exp_eqdec e0 e2); intros.
    rewrite e3. rewrite e4. now left.
    rewrite e3. right. unfold not in *. intros. inversion H. eauto. 
    unfold not in *. right. intros. inversion H; eauto.

    right. unfold not. intros. inversion H.
  - destruct e2.
    right. unfold not. intros. inversion H.
    case (sexp_eqdec s s1); intros.
    case (sexp_eqdec s0 s2); intros.
    rewrite e. rewrite e0. now left.
    rewrite e. right. unfold not in *. intros. inversion H. eauto.
    unfold not in *. right. intros. inversion H; eauto.
Defined.    


Definition eqn_vars (eq: Equation) : set SortedVar :=
  match eq with
  | equ s t => set_union sortedvar_eqdec (vars_of_exp s) (vars_of_exp t)
  | equ_s σ τ => set_union sortedvar_eqdec (vars_of_sexp σ) (vars_of_sexp τ)
  end.


Fixpoint lhvars_Probl (P : Problem) : set SortedVar :=
  match P with
  | [] => []
  | (equ s t) :: P0 => set_union sortedvar_eqdec (vars_of_exp s) (lhvars_Probl P0)
  | (equ_s σ τ) :: P0 => set_union sortedvar_eqdec (vars_of_sexp σ) (lhvars_Probl P0)                     
  end.  

Fixpoint rhvars_Probl (P : Problem) : set SortedVar :=
  match P with
  | [] => []
  | (equ s t) :: P0 => set_union sortedvar_eqdec (vars_of_exp t) (rhvars_Probl P0)
  | (equ_s σ τ) :: P0 => set_union sortedvar_eqdec (vars_of_sexp τ) (rhvars_Probl P0)                     
  end.  


Fixpoint Problem_vars (P : Problem) : set SortedVar :=
  match P with
    | [] => []
    | (equ s t)::P0 => set_union sortedvar_eqdec (vars_of_exp s)
                     (set_union sortedvar_eqdec (vars_of_exp t) (Problem_vars P0))
    | (equ_s σ τ)::P0 => set_union sortedvar_eqdec (vars_of_sexp σ)
                       (set_union sortedvar_eqdec (vars_of_sexp τ) (Problem_vars P0))               
  end.

Notation "P \ u" := (set_remove Equation_eqdec u P) (at level 67).
Notation "P |+ u" := (set_add Equation_eqdec u P) (at level 67).
Notation "P |^^ S" := (subs_Problem_right P S) (at level 67).


Lemma in_exp_then_in_left_problem : forall P s t V, set_In V (vars_of_exp s) ->
                                               set_In (equ s t) P -> 
                                               set_In V (lhvars_Probl P).
Proof.
  intro P.
  induction P; intros.
  - now simpl in *.
  - simpl in *.
    destruct V as [X | Y]; destruct a as [s' t' | σ τ].
     1,3 : destruct H0;
           [inversion H0; subst;
            now apply set_union_intro1 |
            apply set_union_intro2;
            eapply IHP; eauto].
     1,2 : destruct H0;
           [ inversion H0 |
             apply set_union_intro2;
             eapply IHP; eauto].
Qed.

Lemma in_sexp_then_in_left_problem : forall P σ τ V, set_In V (vars_of_sexp σ) ->
                                               set_In (equ_s σ τ) P -> 
                                               set_In V (lhvars_Probl P).
Proof.
  intro P.
  induction P; intros.
  - now simpl in *.
  - simpl in *.
    destruct V as [X | Y]; destruct a as [s t | σ' τ'].
    1,3 : destruct H0;
           [ inversion H0 |
             apply set_union_intro2;
             eapply IHP; eauto].
    1,2 :  destruct H0;
           [inversion H0; subst;
            now apply set_union_intro1 |
            apply set_union_intro2;
            eapply IHP; eauto].
Qed.

Lemma in_exps_then_in_left_problem : forall P V e, set_In V (left_eqn_vars e) ->
                                              set_In e P ->
                                              set_In V (lhvars_Probl P).
Proof.
  intros.
  destruct e as [s t | σ τ].
  - simpl in H. eapply in_exp_then_in_left_problem. apply H. apply H0.
  - simpl in H. eapply in_sexp_then_in_left_problem. apply H. apply H0.
Qed.

Lemma in_left_problem_then_in_problem : forall P V, set_In V (lhvars_Probl P) ->
                                               set_In V (Problem_vars P).
Proof.
  intros P.
  induction P; intros; simpl in *; trivial.
  destruct V as [X | Y]; destruct a as [s t | σ τ].
   all :apply set_union_elim in H; destruct H;
       [now apply set_union_intro1 |
       apply set_union_intro2; apply set_union_intro2; now apply IHP].
Qed.



Lemma in_exp_then_in_right_problem : forall P s t V, set_In V (vars_of_exp t) ->
                                               set_In (equ s t) P -> 
                                               set_In V (rhvars_Probl P).
Proof.
  intro P.
  induction P; intros.
  - now simpl in *.
  - simpl in *.
    destruct V as [X | Y]; destruct a as [s' t' | σ τ].
     1,3 : destruct H0;
           [inversion H0; subst;
            now apply set_union_intro1 |
            apply set_union_intro2;
            eapply IHP; eauto].
     1,2 : destruct H0;
           [ inversion H0 |
             apply set_union_intro2;
             eapply IHP; eauto].
Qed.


  

Lemma in_sexp_then_in_right_problem : forall P σ τ V, set_In V (vars_of_sexp τ) ->
                                               set_In (equ_s σ τ) P -> 
                                               set_In V (rhvars_Probl P).
Proof.
  intro P.
  induction P; intros.
  - now simpl in *.
  - simpl in *.
    destruct V as [X | Y]; destruct a as [s t | σ' τ'].
    1,3 : destruct H0;
           [ inversion H0 |
             apply set_union_intro2;
             eapply IHP; eauto].
    1,2 :  destruct H0;
           [inversion H0; subst;
            now apply set_union_intro1 |
            apply set_union_intro2;
            eapply IHP; eauto].
Qed.




Lemma in_right_problem_then_in_problem : forall P V, set_In V (rhvars_Probl P) ->
                                               set_In V (Problem_vars P).
Proof.
  intros P.
  induction P; intros; simpl in *; trivial.
  destruct V as [X | Y]; destruct a as [s t | σ τ].
   all :apply set_union_elim in H; destruct H;
       [apply set_union_intro2; now apply set_union_intro1 |
       apply set_union_intro2; apply set_union_intro2; now apply IHP].
Qed.





Lemma push_subst_problem_exp : forall s t S P, set_In (equ s t) P -> set_In (equ s (sub t S)) (P |^^ S).
Proof.
  intros.
  induction P.
  - destruct H.
  - simpl in *; subst.
    destruct H.
    + rewrite H.
      simpl. now left.
    + destruct a; simpl; right; now apply IHP.
Qed.     

Lemma push_subst_problem_sexp : forall σ τ S P, set_In (equ_s σ τ) P -> set_In (equ_s σ (sub_s τ S)) (P |^^ S).
Proof.
  intros.
  induction P.
  - destruct H.
  - simpl in *; subst.
    destruct H.
    + rewrite H.
      simpl. now left.
    + destruct a; simpl; right; now apply IHP.
Qed.


    
    
   
Lemma problem_vars_desubst : forall P V A,  set_In V (Problem_vars (P |^^ ([A])%list)) ->
                                         V <> assign_sort_var A ->
                                         ~ set_In V (any_exp_vars (assign_sort_exp A)) ->
                                         set_In V (Problem_vars P).
Proof.
  intro P.
  induction P; intros;
  destruct V as [X' | Y']; destruct A as [X'' | Y'']; simpl in *; trivial;
  destruct a as [s' t' | σ' τ']; simpl in H.  
  - assert (nEq : X' <> X'') by congruence. 
    apply set_union_elim in H.
    destruct H. now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. apply set_union_intro2. apply set_union_intro1.
    eapply (proj1 exp_sexp_desubst). apply H. now simpl. now simpl.
    repeat apply set_union_intro2.
    eapply IHP. apply H. now simpl. now simpl.
  - assert (nEq : X' <> X'') by congruence. 
    apply set_union_elim in H.
    destruct H. now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. apply set_union_intro2. apply set_union_intro1.
    eapply (proj2 exp_sexp_desubst). apply H. now simpl. now simpl.
    repeat apply set_union_intro2.
    eapply IHP. apply H. now simpl. now simpl.
 -  apply set_union_elim in H.
    destruct H. now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. apply set_union_intro2. apply set_union_intro1.
    eapply (proj1 exp_sexp_desubst). apply H. now simpl. now simpl.
    repeat apply set_union_intro2.
    eapply IHP. apply H. now simpl. now simpl.
 -  apply set_union_elim in H.
    destruct H. now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. apply set_union_intro2. apply set_union_intro1.
    eapply (proj2 exp_sexp_desubst). apply H. now simpl. now simpl.
    repeat apply set_union_intro2.
    eapply IHP. apply H. now simpl. now simpl.
 -  apply set_union_elim in H.
    destruct H. now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. apply set_union_intro2. apply set_union_intro1.
    eapply (proj1 exp_sexp_desubst). apply H. now simpl. now simpl.
    repeat apply set_union_intro2.
    eapply IHP. apply H. now simpl. now simpl.
 -  apply set_union_elim in H.
    destruct H. now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. apply set_union_intro2. apply set_union_intro1.
    eapply (proj2 exp_sexp_desubst). apply H. now simpl. now simpl.
    repeat apply set_union_intro2.
    eapply IHP. apply H. now simpl. now simpl.
 -  assert (nEq : Y' <> Y'') by congruence. 
    apply set_union_elim in H.
    destruct H. now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. apply set_union_intro2. apply set_union_intro1.
    eapply (proj1 exp_sexp_desubst). apply H. now simpl. now simpl.
    repeat apply set_union_intro2.
    eapply IHP. apply H. now simpl. now simpl.
  -  assert (nEq : Y' <> Y'') by congruence. 
    apply set_union_elim in H.
    destruct H. now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. apply set_union_intro2. apply set_union_intro1.
    eapply (proj2 exp_sexp_desubst). apply H. now simpl. now simpl.
    repeat apply set_union_intro2.
    eapply IHP. apply H. now simpl. now simpl.
Qed.  


Lemma lhvars_desubst : forall P V A, set_In V (lhvars_Probl (P |^^ ([A])%list))
                                     ->    set_In V (lhvars_Probl P)
.
Proof.
  intro P.
  induction P; intros; destruct V as [X | Y]; try now simpl in *.
  - destruct a as [s' t' | σ' τ'].
    + simpl in *.
      apply set_union_elim in H.
      destruct H. now apply set_union_intro1.
      apply set_union_intro2. eapply IHP; eauto.
    + simpl in *.
      apply set_union_elim in H.
      destruct H. now apply set_union_intro1.
      apply set_union_intro2. eapply IHP; eauto.
   - destruct a as [s' t' | σ' τ'].
    + simpl in *.
      apply set_union_elim in H.
      destruct H. now apply set_union_intro1.
      apply set_union_intro2. eapply IHP; eauto.
    + simpl in *.
      apply set_union_elim in H.
      destruct H. now apply set_union_intro1.
      apply set_union_intro2. eapply IHP; eauto.
Qed. 
    

Lemma problem_var_remove_one_mem : forall P e V, set_In V (Problem_vars (P \ e)) -> set_In V (Problem_vars P).
Proof.
  intro P.
  induction P; intros; destruct V as [X' | Y']; simpl in *; destruct e as [s t | σ τ]; trivial;
  destruct a as [s' t' | σ' τ'].
  - destruct (Equation_eqdec (equ s t) (equ s' t')) as [Heq | Hneq]; subst.
    now repeat apply set_union_intro2.
    simpl in H. apply set_union_elim in H. destruct H.
    now apply set_union_intro1.
    apply set_union_elim in H. destruct H.
    apply set_union_intro2. now apply set_union_intro1.
    repeat apply set_union_intro2. eapply IHP. apply H.
  - destruct (Equation_eqdec (equ s t) (equ_s σ' τ')) as [Heq | Hneq]; subst.
    now repeat apply set_union_intro2.
    simpl in H. apply set_union_elim in H. destruct H.
    now apply set_union_intro1.
    apply set_union_elim in H. destruct H.
    apply set_union_intro2. now apply set_union_intro1.
    repeat apply set_union_intro2. eapply IHP. apply H.
  - destruct (Equation_eqdec (equ_s σ τ) (equ s' t')) as [Heq | Hneq]; subst.
    now repeat apply set_union_intro2.
    simpl in H. apply set_union_elim in H. destruct H.
    now apply set_union_intro1.
    apply set_union_elim in H. destruct H.
    apply set_union_intro2. now apply set_union_intro1.
    repeat apply set_union_intro2. eapply IHP. apply H.
  - destruct (Equation_eqdec (equ_s σ τ) (equ_s σ' τ')) as [Heq | Hneq]; subst.
    now repeat apply set_union_intro2.
    simpl in H. apply set_union_elim in H. destruct H.
    now apply set_union_intro1.
    apply set_union_elim in H. destruct H.
    apply set_union_intro2. now apply set_union_intro1.
    repeat apply set_union_intro2. eapply IHP. apply H.
  - destruct (Equation_eqdec (equ s t) (equ s' t')) as [Heq | Hneq]; subst.
    now repeat apply set_union_intro2.
    simpl in H. apply set_union_elim in H. destruct H.
    now apply set_union_intro1.
    apply set_union_elim in H. destruct H.
    apply set_union_intro2. now apply set_union_intro1.
    repeat apply set_union_intro2. eapply IHP. apply H.
   - destruct (Equation_eqdec (equ s t) (equ_s σ' τ')) as [Heq | Hneq]; subst.
    now repeat apply set_union_intro2.
    simpl in H. apply set_union_elim in H. destruct H.
    now apply set_union_intro1.
    apply set_union_elim in H. destruct H.
    apply set_union_intro2. now apply set_union_intro1.
    repeat apply set_union_intro2. eapply IHP. apply H.
  - destruct (Equation_eqdec (equ_s σ τ) (equ s' t')) as [Heq | Hneq]; subst.
    now repeat apply set_union_intro2.
    simpl in H. apply set_union_elim in H. destruct H.
    now apply set_union_intro1.
    apply set_union_elim in H. destruct H.
    apply set_union_intro2. now apply set_union_intro1.
    repeat apply set_union_intro2. eapply IHP. apply H.
    - destruct (Equation_eqdec (equ_s σ τ) (equ_s σ' τ')) as [Heq | Hneq]; subst.
    now repeat apply set_union_intro2.
    simpl in H. apply set_union_elim in H. destruct H.
    now apply set_union_intro1.
    apply set_union_elim in H. destruct H.
    apply set_union_intro2. now apply set_union_intro1.
    repeat apply set_union_intro2. eapply IHP. apply H.
Qed.    


Lemma problem_lhvar_remove_one_mem : forall P e V , set_In V (lhvars_Probl (P \ e)) -> set_In V (lhvars_Probl P).
Proof.
  intro P.
  induction P; intros; destruct V as [X' | Y']; simpl in *; destruct e as [s t | σ τ]; trivial;
  destruct a as [s' t' | σ' τ'].
  - destruct (Equation_eqdec (equ s t) (equ s' t')) as [Eq | nEq].
    now apply set_union_intro2.
    simpl in H. apply set_union_intro.
    apply set_union_elim in H. destruct H.
    now left. right. eapply IHP. apply H.
  - destruct (Equation_eqdec (equ s t) (equ_s σ' τ')) as [Eq | nEq].
    now apply set_union_intro2.
    simpl in H. apply set_union_intro.
    apply set_union_elim in H. destruct H.
    now left. right. eapply IHP. apply H.
  - destruct (Equation_eqdec (equ_s σ τ) (equ s' t')) as [Eq | nEq].
    now apply set_union_intro2.
    simpl in H. apply set_union_intro.
    apply set_union_elim in H. destruct H.
    now left. right. eapply IHP. apply H.
  - destruct (Equation_eqdec (equ_s σ τ) (equ_s σ' τ')) as [Eq | nEq].
    now apply set_union_intro2.
    simpl in H. apply set_union_intro.
    apply set_union_elim in H. destruct H.
    now left. right. eapply IHP. apply H.
  - destruct (Equation_eqdec (equ s t) (equ s' t')) as [Eq | nEq].
    now apply set_union_intro2.
    simpl in H. apply set_union_intro.
    apply set_union_elim in H. destruct H.
    now left. right. eapply IHP. apply H.
  - destruct (Equation_eqdec (equ s t) (equ_s σ' τ')) as [Eq | nEq].
    now apply set_union_intro2.
    simpl in H. apply set_union_intro.
    apply set_union_elim in H. destruct H.
    now left. right. eapply IHP. apply H.
  - destruct (Equation_eqdec (equ_s σ τ) (equ s' t')) as [Eq | nEq].
    now apply set_union_intro2.
    simpl in H. apply set_union_intro.
    apply set_union_elim in H. destruct H.
    now left. right. eapply IHP. apply H.
  - destruct (Equation_eqdec (equ_s σ τ) (equ_s σ' τ')) as [Eq | nEq].
    now apply set_union_intro2.
    simpl in H. apply set_union_intro.
    apply set_union_elim in H. destruct H.
    now left. right. eapply IHP. apply H.
Qed.


  



Lemma problem_X_clear : forall P V A, ~set_In V (any_exp_vars (assign_sort_exp A)) /\
                                  ~set_In V (lhvars_Probl P) ->
                                 V = assign_sort_var A ->
                                 ~set_In V (Problem_vars (P|^^([A])%list)).
Proof.
  intro P.
  induction P; intros; destruct V as [X' | Y']; destruct A as [X'' s | Y'' σ]; simpl in *; destruct H as [H_1 H_2];  trivial; try destruct a as [s' t' | σ' τ']; simpl in *.
  - injection H0; intros; subst.
    intro.  apply set_union_elim in H.
    destruct H. apply H_2.
    now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. revert H. now apply (proj1 exps_X_clear).
    revert H. eapply IHP. split; eauto.
    intro. apply H_2. now apply set_union_intro2.
    now simpl.
  - injection H0; intros; subst.
    intro.  apply set_union_elim in H.
    destruct H. apply H_2.
    now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. revert H. now apply (proj2 exps_X_clear).
    revert H. eapply IHP. split; eauto.
    intro. apply H_2. now apply set_union_intro2.
    now simpl.
 - inversion H0.
 - inversion H0.
 - inversion H0.
 - inversion H0.
 -  injection H0; intros; subst.
    intro.  apply set_union_elim in H.
    destruct H. apply H_2.
    now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. revert H. now apply (proj1 exps_X_clear).
    revert H. eapply IHP. split; eauto.
    intro. apply H_2. now apply set_union_intro2.
    now simpl.

 - injection H0; intros; subst.
    intro.  apply set_union_elim in H.
    destruct H. apply H_2.
    now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. revert H. now apply (proj2 exps_X_clear).
    revert H. eapply IHP. split; eauto.
    intro. apply H_2. now apply set_union_intro2.
    now simpl.
Qed.

Lemma problem_var_ext_vars: forall P e V, set_In V (Problem_vars (P |+ e)) ->
                                     ~ set_In V (eqn_vars e) ->
                                     set_In V (Problem_vars P).
Proof.
  induction P; intros; destruct e as [s t | σ τ]; destruct V as [Xv | Yv]; trivial;
  try now simpl in *;
          apply set_union_elim in H;
          destruct H; apply H0 ; [now apply set_union_intro1 | now apply set_union_intro2].   
  - destruct a as [s' t' | σ' τ'].
    destruct (Equation_eqdec (equ s t) (equ s' t')) as [HEq | HnEq].
    rewrite HEq in H.
    rewrite set_list_app_eq in H. assumption.
    rewrite set_list_app_neq in H; eauto.
    simpl in *. apply set_union_elim in H.
    destruct H. now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. apply set_union_intro2.
    now apply set_union_intro1.
    apply set_union_intro2.
    apply set_union_intro2.
    eapply IHP; eauto.

    destruct (Equation_eqdec (equ s t) (equ_s σ' τ')) as [HEq | HnEq].
    rewrite HEq in H.
    rewrite set_list_app_eq in H. assumption.
    rewrite set_list_app_neq in H; eauto.
    simpl in *. apply set_union_elim in H.
    destruct H. now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. apply set_union_intro2.
    now apply set_union_intro1.
    apply set_union_intro2.
    apply set_union_intro2.
    eapply IHP; eauto.
  - destruct a as [s' t' | σ' τ'].
    destruct (Equation_eqdec (equ s t) (equ s' t')) as [HEq | HnEq].
    rewrite HEq in H.
    rewrite set_list_app_eq in H. assumption.
    rewrite set_list_app_neq in H; eauto.
    simpl in *. apply set_union_elim in H.
    destruct H. now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. apply set_union_intro2.
    now apply set_union_intro1.
    apply set_union_intro2.
    apply set_union_intro2.
    eapply IHP; eauto.

    destruct (Equation_eqdec (equ s t) (equ_s σ' τ')) as [HEq | HnEq].
    rewrite HEq in H.
    rewrite set_list_app_eq in H. assumption.
    rewrite set_list_app_neq in H; eauto.
    simpl in *. apply set_union_elim in H.
    destruct H. now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. apply set_union_intro2.
    now apply set_union_intro1.
    apply set_union_intro2.
    apply set_union_intro2.
    eapply IHP; eauto.

   - destruct a as [s' t' | σ' τ'].
     destruct (Equation_eqdec (equ_s σ τ) (equ s' t')) as [HEq | HnEq].
    rewrite HEq in H.
    rewrite set_list_app_eq in H. assumption.
    rewrite set_list_app_neq in H; eauto.
    simpl in *. apply set_union_elim in H.
    destruct H. now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. apply set_union_intro2.
    now apply set_union_intro1.
    apply set_union_intro2.
    apply set_union_intro2.
    eapply IHP; eauto.

    destruct (Equation_eqdec (equ_s σ τ) (equ_s σ' τ')) as [HEq | HnEq].
    rewrite HEq in H.
    rewrite set_list_app_eq in H. assumption.
    rewrite set_list_app_neq in H; eauto.
    simpl in *. apply set_union_elim in H.
    destruct H. now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. apply set_union_intro2.
    now apply set_union_intro1.
    apply set_union_intro2.
    apply set_union_intro2.
    eapply IHP; eauto.

- destruct a as [s' t' | σ' τ'].
     destruct (Equation_eqdec (equ_s σ τ) (equ s' t')) as [HEq | HnEq].
    rewrite HEq in H.
    rewrite set_list_app_eq in H. assumption.
    rewrite set_list_app_neq in H; eauto.
    simpl in *. apply set_union_elim in H.
    destruct H. now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. apply set_union_intro2.
    now apply set_union_intro1.
    apply set_union_intro2.
    apply set_union_intro2.
    eapply IHP; eauto.

    destruct (Equation_eqdec (equ_s σ τ) (equ_s σ' τ')) as [HEq | HnEq].
    rewrite HEq in H.
    rewrite set_list_app_eq in H. assumption.
    rewrite set_list_app_neq in H; eauto.
    simpl in *. apply set_union_elim in H.
    destruct H. now apply set_union_intro1.
    apply set_union_elim in H.
    destruct H. apply set_union_intro2.
    now apply set_union_intro1.
    apply set_union_intro2.
    apply set_union_intro2.
    eapply IHP; eauto.
Qed.
    
    
   
Lemma lhvar_vars_add : forall P e V, set_In V (lhvars_Probl (P |+ e)) ->
                                set_In V (set_union sortedvar_eqdec (lhvars_Probl P) (lhvars_Probl ([e])%list)) .
Proof.
  intro P.
  induction P; intros; destruct e as [s t | σ τ]; destruct V as [Xv | Yv];
   try now simpl in *; now apply set_union_intro2.
  - specialize (IHP (equ s t)). simpl in IHP.
    destruct a as [s' t' | σ' τ'].
    + destruct (Equation_eqdec (equ s t) (equ s' t')) as [HEq | HnEq].
      simpl. rewrite HEq in H.
      rewrite set_list_app_eq in H. simpl in H.
      apply set_union_elim in H.
      destruct H. now repeat apply set_union_intro1.
      apply set_union_intro1. now apply set_union_intro2.
      rewrite set_list_app_neq in H; eauto. simpl in H .
      simpl. eapply set_union_assoc.
      apply set_union_elim in H.
      destruct H.
      now apply set_union_intro1.
      apply set_union_intro2. now apply IHP.
    + destruct (Equation_eqdec (equ s t) (equ_s σ' τ')) as [HEq | HnEq]; subst.
      inversion HEq.
      rewrite set_list_app_neq in H; eauto. simpl in H.
      simpl. eapply set_union_assoc.
      apply set_union_elim in H.
      destruct H. now apply set_union_intro1.
      apply set_union_intro2. eapply IHP; eauto.

  - specialize (IHP (equ s t)). simpl in IHP.
    destruct a as [s' t' | σ' τ'].
    + destruct (Equation_eqdec (equ s t) (equ s' t')) as [HEq | HnEq].
      simpl. rewrite HEq in H.
      rewrite set_list_app_eq in H. simpl in H.
      apply set_union_elim in H.
      destruct H. now repeat apply set_union_intro1.
      apply set_union_intro1. now apply set_union_intro2.
      rewrite set_list_app_neq in H; eauto. simpl in H .
      simpl. eapply set_union_assoc.
      apply set_union_elim in H.
      destruct H.
      now apply set_union_intro1.
      apply set_union_intro2. now apply IHP.
    + destruct (Equation_eqdec (equ s t) (equ_s σ' τ')) as [HEq | HnEq]; subst.
      inversion HEq.
      rewrite set_list_app_neq in H; eauto. simpl in H.
      simpl. eapply set_union_assoc.
      apply set_union_elim in H.
      destruct H. now apply set_union_intro1.
      apply set_union_intro2. eapply IHP; eauto.
 
  - specialize (IHP (equ_s σ τ)). simpl in IHP.
    destruct a as [s' t' | σ' τ'].
    + destruct (Equation_eqdec (equ_s σ τ) (equ s' t')) as [HEq | HnEq].
      inversion HEq.
      rewrite set_list_app_neq in H; eauto. simpl in H.
      simpl. eapply set_union_assoc.
      apply set_union_elim in H.
      destruct H. now apply set_union_intro1.
      apply set_union_intro2. eapply IHP; eauto.
    + destruct (Equation_eqdec (equ_s σ τ) (equ_s σ' τ')) as [HEq | HnEq]; subst.
      simpl. rewrite HEq in H.
      rewrite set_list_app_eq in H. simpl in H.
      apply set_union_elim in H.
      destruct H. now repeat apply set_union_intro1.
      apply set_union_intro1. now apply set_union_intro2.
      rewrite set_list_app_neq in H; eauto. simpl in H .
      simpl. eapply set_union_assoc.
      apply set_union_elim in H.
      destruct H.
      now apply set_union_intro1.
      apply set_union_intro2. now apply IHP.

   - specialize (IHP (equ_s σ τ)). simpl in IHP.
    destruct a as [s' t' | σ' τ'].
    + destruct (Equation_eqdec (equ_s σ τ) (equ s' t')) as [HEq | HnEq].
      inversion HEq.
      rewrite set_list_app_neq in H; eauto. simpl in H.
      simpl. eapply set_union_assoc.
      apply set_union_elim in H.
      destruct H. now apply set_union_intro1.
      apply set_union_intro2. eapply IHP; eauto.
    + destruct (Equation_eqdec (equ_s σ τ) (equ_s σ' τ')) as [HEq | HnEq]; subst.
      simpl. rewrite HEq in H.
      rewrite set_list_app_eq in H. simpl in H.
      apply set_union_elim in H.
      destruct H. now repeat apply set_union_intro1.
      apply set_union_intro1. now apply set_union_intro2.
      rewrite set_list_app_neq in H; eauto. simpl in H .
      simpl. eapply set_union_assoc.
      apply set_union_elim in H.
      destruct H.
      now apply set_union_intro1.
      apply set_union_intro2. now apply IHP.
Qed.


Lemma lhvar_ext_vars : forall P e V, set_In V (lhvars_Probl (P |+ e)) ->
                                  (forall U, set_In U (left_eqn_vars e) -> set_In U (lhvars_Probl P)) ->
                                  set_In V (lhvars_Probl P).
Proof.
  intros.
  apply lhvar_vars_add in H.
  destruct e as [s t | σ τ].
  all: simpl in H; apply set_union_elim in H; destruct H; eauto.
Qed.    
