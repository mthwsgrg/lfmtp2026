Require Export Problems.


Definition lift (σ: sexp) :=  Zero .: σ >> ↑.

(** Equivalence with respect to σmin-rules *)

Unset Elimination Schemes.
Inductive σmin_equiv : exp -> exp -> Prop :=
| σmin_subst_app (s t : exp) (σ : sexp) :  σmin_equiv ((App s t)[σ]) (App s[σ] t[σ])
| σmin_subst_lam (s : exp) (σ : sexp) :  σmin_equiv  ((Lam s)[σ])  (Lam (s[Zero .: (σ >> ↑)]))
| σmin_subst_comp (s: exp) (σ τ: sexp) : σmin_equiv (s[σ])[τ] s[σ >> τ]
| σmin_id_exp (s: exp) : σmin_equiv s[I] s 

                                
| σmin_equiv_refl (s : exp) :  σmin_equiv s s
| σmin_equiv_sym (s t : exp) :  σmin_equiv s t -> σmin_equiv t s
| σmin_equiv_trans (s t u : exp) :  σmin_equiv s t -> σmin_equiv t u -> σmin_equiv s u
| σmin_equiv_app (s1 s2 t1 t2 : exp) :  σmin_equiv s1 s2 -> σmin_equiv t1 t2 -> σmin_equiv (App s1 t1) (App s2 t2)
| σmin_equiv_lam (s1 s2 : exp) :  σmin_equiv s1 s2 -> σmin_equiv (Lam s1) (Lam s2)
| σmin_equiv_subst (s1 s2 : exp) (σ τ : sexp) :  σmin_equiv s1 s2 -> σmin_equivs σ τ -> σmin_equiv s1[σ] s2[τ]
with σmin_equivs : sexp -> sexp -> Prop :=
| σmin_comp_cons (s : exp) (σ τ : sexp) :  σmin_equivs  ((s .: σ) >> τ) (s[τ] .: (σ >> τ)) 
| σmin_comp_assoc (σ τ θ : sexp) :  σmin_equivs ((σ >> τ) >> θ) (σ >> (τ >> θ))
| σmin_lift (σ τ : sexp) (s: exp) : σmin_equivs (lift σ >> (s .: τ)) (s .: (σ >> τ))              

| σmin_equivs_refl (σ : sexp) :  σmin_equivs σ σ
| σmin_equivs_sym (σ τ : sexp) :  σmin_equivs σ τ -> σmin_equivs τ σ
| σmin_equivs_trans (σ τ θ : sexp) :  σmin_equivs σ τ -> σmin_equivs τ θ -> σmin_equivs σ θ
| σmin_equivs_cons (s1 s2 : exp) (σ τ : sexp) :  σmin_equiv s1 s2 -> σmin_equivs σ τ -> σmin_equivs (s1 .: σ) (s2 .: τ)
| σmin_equivs_comp (σ1 σ2 τ1 τ2 : sexp) :  σmin_equivs σ1 σ2 -> σmin_equivs τ1 τ2 ->  σmin_equivs (σ1 >> τ1) (σ2 >> τ2).
Set Elimination Schemes.  
Scheme σmin_equiv_ind := Induction for σmin_equiv Sort Prop
with  σmin_equivs_ind := Induction for σmin_equivs Sort Prop.
Combined Scheme σmin_eqs_ind from σmin_equiv_ind, σmin_equivs_ind.

Notation "S ~:c S'" := (subs_equiv σmin_equiv σmin_equivs S S') (at level 67).


Inductive smatch : Tuple -> Tuple -> Prop := 
| smatch_refl_1 : forall S P s, set_In (equ s s) P -> smatch (S,P) (S,P\(equ s s))
| smatch_refl_2 : forall S P σ, set_In (equ_s σ σ) P -> smatch (S,P) (S, P\(equ_s σ σ))
                    
| smatch_App : forall S P s t s' t', set_In (equ (App s t) (App s' t')) P ->
                                smatch (S,P) (S, (P |+ (equ s s') |+ (equ t t'))\ (equ (App s t) (App s' t') ))
| smatch_Lam : forall S P s s', set_In (equ (Lam s) (Lam s')) P ->
                           smatch (S,P) (S, P |+ (equ s s') \ (equ (Lam s) (Lam s')))
| smatch_Inst : forall S P s σ s' σ', set_In (equ (s[σ]) (s'[σ'])) P ->
                                 smatch (S,P) (S, P |+ (equ s s') |+ (equ_s σ σ') \ (equ (s[σ]) (s'[σ'])))
| smatch_Cons : forall S P s σ s' σ', set_In (equ_s (s .: σ) (s' .: σ')) P ->
                                 smatch (S,P) (S, P |+ (equ s s') |+ (equ_s σ σ') \ (equ_s (s .: σ) (s' .: σ')))
| smatch_Comp : forall S P σ σ' τ τ', set_In (equ_s (σ >> τ) (σ' >> τ')) P ->
                                 smatch (S,P) (S, P |+ (equ_s σ σ') |+ (equ_s τ τ') \ (equ_s (σ >> τ) (σ' >> τ')))
| smatch_Lift : forall S P s σ s' σ', set_In (equ (Lam (s[Zero .: (σ >> ↑)])) (s'[σ'])) P ->
                                 smatch (S,P) (S, P |+ (equ (Lam s)[σ] s'[σ']) \ (equ (Lam (s[Zero .: (σ >> ↑)])) (s'[σ'])))

| smatch_Assoc : forall S P σ τ ρ σ' τ', set_In (equ_s (σ >> τ >> ρ)  (σ' >> τ')) P  ->
                                    smatch (S,P) (S, P |+ (equ_s ((σ >> τ) >> ρ) (σ' >> τ')) \ (equ_s (σ >> τ >> ρ)  (σ' >> τ')))
| smatch_Conslaw : forall S P s σ τ σ' τ', set_In (equ_s (s[τ] .: (σ >> τ)) (σ' >> τ')) P ->
                                      smatch (S,P) (S, P |+ (equ_s ((s .: σ) >> τ) (σ' >> τ')) \ (equ_s (s[τ] .: (σ >> τ)) (σ' >> τ') ))
| smatch_Complaw : forall S P s s' σ τ ρ, set_In (equ s[σ >> τ] s'[ρ]) P ->
                                     smatch (S, P) (S, (P |+ (equ s[σ][τ] s'[ρ])) \ (equ s[σ >> τ] s'[ρ]))

| smatch_Appdist : forall S P s t s' σ σ', set_In (equ (App s[σ] t[σ]) s'[σ']) P ->
                                      smatch (S, P) (S, (P |+ (equ (App s t)[σ] s'[σ'])) \ (equ (App s[σ] t[σ]) s'[σ']))
                                        
| smatch_inst_exp : forall S S' P X s, (~ set_In (exp_var X) (lhvars_Probl P)) ->
                           (set_In (equ s (VarExp X)) P) ->
                           S' = sub_comp S ( [exp_assign X s])  -> 
                           smatch (S,P)
                             (S',(P\(equ s (VarExp X)))|^^[exp_assign X s])
| smatch_inst_sexp : forall S S' P Y σ, (~ set_In (sexp_var Y) (lhvars_Probl P)) ->
                                   set_In (equ_s σ (VarSExp Y)) P ->
                                   S' = sub_comp S ([sexp_assign Y σ]) ->
                                   smatch (S,P)
                                     (S', (P\(equ_s σ (VarSExp Y)))|^^[sexp_assign Y σ])

| smatch_inst_id_exp_both: forall S S' P s X Y, (~ set_In (exp_var X) (lhvars_Probl P)) /\
                                        (~ set_In (sexp_var Y) (lhvars_Probl P)) ->
                                   set_In (equ s (VarExp X)[VarSExp Y]) P ->
                                   S' = sub_comp (sub_comp S ([exp_assign X s])) ([sexp_assign Y I]) ->
                                   smatch (S,P)
                                   (S',((P\(equ s (VarExp X)[VarSExp Y]))|^^[exp_assign X s]) |^^ [sexp_assign Y I])


(*  this is straight forward to add not including now to keep it simple                                  
| smatch_inst_id_exp_left : forall S S' P s X, (~ set_In (exp_var X) (lhvars_Probl P)) ->
                                   set_In (equ s (VarExp X)[I]) P ->
                                   S' = sub_comp S ([exp_assign X s]) ->
                                   smatch (S,P)
                                   (S',(P\(equ s (VarExp X)[I]))|^^[exp_assign X s])
| smatch_inst_id_exp_right : forall S S' P s Y, (~ set_In (sexp_var Y) (lhvars_Probl P)) ->
                                   set_In (equ s s[VarSExp Y]) P ->
                                   S' = sub_comp S ([sexp_assign Y I]) ->
                                   smatch (S,P)
                                   (S',(P\(equ s s[VarSExp Y]))|^^[sexp_assign Y I]) *)
                                   
| smatch_inst_lift : forall S S' P s t σ X , (~ set_In (exp_var X) (lhvars_Probl P)) ->
                                   set_In (equ s[t .: σ] (VarExp X)[t .: I]) P ->
                                   S' = sub_comp S ([exp_assign X s[lift σ]]) ->
                                   smatch (S,P)
                                   (S',(P\(equ s[t .: σ] (VarExp X)[t .: I]))|^^[exp_assign X s[lift σ]]).                                                    


                            




(* Properties about σmin *)


Lemma not_in_dom_same : (forall s S, (forall X, set_In (exp_var X) (vars_of_exp s) ->
                                           σmin_equiv (look_up_exp X S) (VarExp X)) /\
                                     (forall Y, set_In (sexp_var Y) (vars_of_exp s) ->
                                            σmin_equivs (look_up_sexp Y S) (VarSExp Y))
                                             -> σmin_equiv  s (sub s S)) /\
                               (forall σ S, (forall X, set_In (exp_var X) (vars_of_sexp σ) ->
                                             σmin_equiv (look_up_exp X S) (VarExp X)) /\
                                       (forall Y, set_In (sexp_var Y) (vars_of_sexp σ) ->
                                             σmin_equivs (look_up_sexp Y S) (VarSExp Y)) ->
                                             σmin_equivs σ (sub_s σ S)).
Proof.
  apply sigma_ind2; intros; simpl in *; try now constructor.
  - destruct H1. apply σmin_equiv_app. 
    apply H; split; intros.
    apply H1; intros; now apply set_union_intro1.
    apply H2; intros; now apply set_union_intro1.
    apply H0; split; intros.
    apply H1; intros; now apply set_union_intro2.
    apply H2; intros; now apply set_union_intro2.   
  - destruct H0. apply σmin_equiv_lam.
    apply H; split; intros. now apply H0. now apply H1. 
  - destruct H1. apply σmin_equiv_subst.
    apply H; split; intros.
    apply H1; intros; now apply set_union_intro1.
    apply H2; intros; now apply set_union_intro1.
    apply H0; split; intros.
    apply H1; intros; now apply set_union_intro2.
    apply H2; intros; now apply set_union_intro2.   
  - destruct H. apply σmin_equiv_sym. now apply H; left.
  - destruct H1. apply σmin_equivs_cons. 
    apply H; split; intros.
    apply H1; intros; now apply set_union_intro1.
    apply H2; intros; now apply set_union_intro1.
    apply H0; split; intros.
    apply H1; intros; now apply set_union_intro2.
    apply H2; intros; now apply set_union_intro2.   
  - destruct H1. apply σmin_equivs_comp. 
    apply H; split; intros.
    apply H1; intros; now apply set_union_intro1.
    apply H2; intros; now apply set_union_intro1.
    apply H0; split; intros.
    apply H1; intros; now apply set_union_intro2.
    apply H2; intros; now apply set_union_intro2.   
  - destruct H. apply σmin_equivs_sym. now apply H0; left.
Qed.
    
Lemma σmin_comp_prop_exp : forall X S S' Sl,  ~set_In (exp_var X) (dom_rec S)  ->
                                        ~set_In (exp_var X) (dom_rec Sl) ->
                                        (sub_comp S S') ~:c Sl ->
                                        σmin_equiv (look_up_exp X S') (VarExp X).
Proof.
  intros.
  unfold subs_equiv in H1; destruct H1 as [H1 H1'].
  simpl in H1.
  erewrite <- not_in_dom_lookup_same_exp; eauto.
  erewrite <- in_subcomp_second_arg_exp; eauto.
Qed.

Lemma σmin_comp_prop_sexp : forall Y S S' Sl,  ~set_In (sexp_var Y) (dom_rec S)  ->
                                          ~set_In (sexp_var Y) (dom_rec Sl) ->
                                          (sub_comp S S') ~:c Sl ->
                                          σmin_equivs (look_up_sexp Y S') (VarSExp Y).
Proof.
  intros.
  unfold subs_equiv in H1; destruct H1 as [H1 H1'].
  simpl in H1.
  erewrite <- not_in_dom_lookup_same_sexp; eauto.
  erewrite <- in_subcomp_second_arg_sexp; eauto.
Qed.


Lemma σmin_subst_ext : (forall s S S', S ~:c S' -> σmin_equiv (sub s S) (sub s S')) /\
                         (forall σ S S', S ~:c S' -> σmin_equivs (sub_s σ S) (sub_s σ S')).
Proof.
  apply sigma_ind2; intros; simpl.
  - apply σmin_equiv_refl.
  - apply σmin_equiv_app; eauto.
  - apply σmin_equiv_lam; eauto.
  - apply σmin_equiv_subst; eauto.
  - unfold subs_equiv in H. destruct H.
    specialize (H X). now simpl in H.
  - constructor.
  - constructor.
  - apply σmin_equivs_cons; eauto.
  - apply σmin_equivs_comp; eauto.
  - unfold subs_equiv in H. destruct H.
    specialize (H0 Y). now simpl in H0.
Qed.  

(* count comp right associatively *)
Fixpoint count_comp (σ: sexp) : nat :=
  match σ with
  | σ >> τ => 1 + count_comp τ
  | _ => 0
  end.     


Definition σmin_rhs_form_exp (s: exp) : nat :=
  match s with
  | Lam s[Zero .: σ >> ↑] => 1 + count_comp σ
  | App s[σ] t[τ] => if sexp_eqdec σ τ then 1 + count_comp σ else 0
  | s[σ >> τ] => 1 + count_comp τ
  | _ => 0
  end.

Definition σmin_rhs_form_sexp (σ: sexp) : nat :=
  match σ with
  | σ >> τ >> ρ => 1 + count_comp ρ
  | s[τ] .: σ >> ρ => if sexp_eqdec τ ρ then  1 + count_comp τ else 0
  | _ => 0
  end.        



Fixpoint σmin_steps_possible (P: Problem) : nat :=
  match P with
  | [] => 0
  | (equ_s σ τ) :: P0 => σmin_rhs_form_sexp σ + σmin_steps_possible P0
  | (equ s t) :: P0 => σmin_rhs_form_exp s + σmin_steps_possible P0
  end.

Definition lEqn_σmin_steps (E: Equation) : nat :=
  match E with
  | equ_s σ τ => σmin_rhs_form_sexp σ
  | equ s t => σmin_rhs_form_exp s
  end.

Lemma σmin_steps_neq_nil : forall e P, set_In e P -> σmin_steps_possible P >= σmin_steps_possible ([e]).
Proof.
  intros. induction P; intros. simpl in H. contradiction.
  simpl in H. destruct H.
  + rewrite H. destruct e.
    simpl. lia.
    simpl. lia.
  + destruct e.
    destruct a.
    simpl. simpl in IHP.
    specialize (IHP H). lia.
    simpl. simpl in IHP. specialize (IHP H). lia.
    simpl. destruct a; simpl in IHP; specialize (IHP H); lia.  
Qed.  


Lemma σmin_steps_remove : forall P e, set_In e P ->
                                 σmin_steps_possible (P\e) =  σmin_steps_possible P - lEqn_σmin_steps e.
Proof.
   intros. induction P. simpl in H. contradiction.
  simpl in H. destruct H.
   +  rewrite H. clear H.
      simpl. case (Equation_eqdec e e); intro H. clear H.
      destruct e. unfold lEqn_σmin_steps. lia.
      unfold lEqn_σmin_steps. lia.
      contradiction.
   + simpl. destruct a as [s t | σ τ].
     destruct e as [s' t' | σ' τ'].
     * case (Equation_eqdec (equ s' t') (equ s t)); intro H0.
       inversion H0; subst. unfold lEqn_σmin_steps. lia.  
       simpl. unfold lEqn_σmin_steps in IHP. rewrite IHP; trivial.
       assert (Q : σmin_steps_possible P >= σmin_steps_possible ([equ s' t'])).
       apply σmin_steps_neq_nil; trivial.
       simpl in Q. lia.
    * case (Equation_eqdec (equ_s σ' τ') (equ s t)); intro H0.
       inversion H0; subst.
       simpl. unfold lEqn_σmin_steps in IHP. rewrite IHP; trivial.
       assert (Q : σmin_steps_possible P >= σmin_steps_possible ([equ_s σ' τ'])).
       apply σmin_steps_neq_nil; trivial.
       simpl in Q. lia.
    * destruct e as [s' t' | σ' τ'].
       case (Equation_eqdec (equ s' t') (equ_s σ τ)); intro H0.
       inversion H0; subst.
       simpl. unfold lEqn_σmin_steps in IHP. rewrite IHP; trivial.
       assert (Q : σmin_steps_possible P >= σmin_steps_possible ([equ s' t'])).
       apply σmin_steps_neq_nil; trivial.
       simpl in Q. lia.
       case (Equation_eqdec (equ_s σ' τ') (equ_s σ τ)); intro H0.
       inversion H0; subst. unfold lEqn_σmin_steps. lia.  
       simpl. unfold lEqn_σmin_steps in IHP. rewrite IHP; trivial.
       assert (Q : σmin_steps_possible P >= σmin_steps_possible ([equ_s σ' τ'])).
       apply σmin_steps_neq_nil; trivial.
       simpl in Q. lia.
Qed.   

Lemma σmin_steps_add : forall P e,  σmin_steps_possible P + σmin_steps_possible ([e]) >= σmin_steps_possible (P |+ e).
Proof.
  intros. induction P. simpl; lia.
  simpl in *|-*. destruct e; destruct a.
  case (Equation_eqdec (equ e e0) (equ e1 e2)); intro H; simpl; try lia.
  case (Equation_eqdec (equ e e0) (equ_s s s0)); intro H; simpl; try lia.
  case (Equation_eqdec (equ_s s s0) (equ e e0)); intro H; simpl; try lia.
  case (Equation_eqdec (equ_s s s0) (equ_s s1 s2)); intro H; simpl; try lia.
Qed.

Lemma σmin_rhs_form_app_case : forall s t σ, σmin_rhs_form_exp (App s[σ] t[σ]) = S (count_comp σ).
Proof.
  intros. simpl.
  destruct (sexp_eqdec σ σ) as [HEq | nHeq]; try congruence.
Qed.


Lemma σmin_rhs_form_cons_case : forall s σ τ, σmin_rhs_form_sexp (s[τ] .: σ >> τ) = S (count_comp τ).
Proof.
  intros. simpl.
  destruct (sexp_eqdec τ τ) as [HEq | nHeq]; try congruence.
Qed.

Lemma σmin_lam_step_less : forall s σ, σmin_rhs_form_exp (Lam s[Zero .: σ >> ↑]) > σmin_rhs_form_exp  (Lam s)[σ].
Proof.
  intros.
  simpl.
  destruct σ; try lia.
  simpl. lia.
Qed.

Lemma σmin_lam_step_one_less : forall s σ, σmin_rhs_form_exp (Lam s[Zero .: σ >> ↑]) = S (σmin_rhs_form_exp  (Lam s)[σ]).
Proof.
  intros.
  simpl.
  destruct σ; try now simpl.
Qed.


Lemma σmin_monad_step_less : forall s σ τ, σmin_rhs_form_exp (s[σ >> τ]) > σmin_rhs_form_exp (s[σ])[τ].
Proof.
  intros.
  simpl.
  destruct τ; try lia.
  simpl. lia.
Qed.

Lemma σmin_app_step_less : forall s t σ, σmin_rhs_form_exp (App s[σ] t[σ]) > σmin_rhs_form_exp (App s t)[σ].
Proof.
  intros.
  simpl. destruct (sexp_eqdec σ σ); try contradiction.
  destruct σ; try lia.
  simpl. lia.
Qed.

Lemma σmin_cons_step_less : forall s σ τ, σmin_rhs_form_sexp (s[τ] .: σ >> τ) > σmin_rhs_form_sexp ( (s .: σ) >> τ).
Proof.
  intros.
  simpl.  simpl. destruct (sexp_eqdec τ τ); try contradiction.
  destruct τ; try lia.
  simpl. lia.
Qed.


Lemma σmin_assoc_step_less : forall σ τ ρ, σmin_rhs_form_sexp (σ >> τ >> ρ) > σmin_rhs_form_sexp ( (σ >> τ) >> ρ).
Proof.
  intros.
  simpl. 
  destruct ρ; try lia.
  simpl. lia.
Qed.


Lemma σmin_step_lam_gt_0 : forall P s σ t, set_In (equ (Lam s [Zero .: σ >> ↑]) t) P -> σmin_steps_possible P > 0.
Proof.
  intro.
  induction P.
  - intros. simpl in H. contradiction.
  - intros. simpl in H.
    destruct H.
    rewrite H. simpl. lia.

    destruct a.
    simpl. specialize (IHP _ _ _ H).
    lia.

    simpl. specialize (IHP _ _ _ H).
    lia.
Qed.


Lemma σmin_step_assoc_gt_0 : forall P σ τ ρ ρ', set_In (equ_s (σ >> τ >> ρ) ρ') P ->
                                        σmin_steps_possible P > 0.
Proof.
  intro.
  induction P.
  - intros. simpl in H. contradiction.
  - intros. simpl in H.
    destruct H.
    rewrite H. simpl. lia.

    destruct a.
    simpl. specialize (IHP _ _ _ _ H).
    lia.

    simpl. specialize (IHP _ _ _ _ H).
    lia.
Qed.

Lemma σmin_step_monad_gt_0 : forall P s σ τ t, set_In (equ s[σ >> τ] t)  P ->
                                          σmin_steps_possible P > 0.
 
Proof.
  intro.
  induction P.
  - intros. simpl in H. contradiction.
  - intros. simpl in H.
    destruct H.
    rewrite H. simpl. lia.

    destruct a.
    simpl. specialize (IHP _ _ _ _ H).
    lia.

    simpl. specialize (IHP _ _ _  _ H).
    lia.
Qed.

Lemma σmin_step_cons_gt_0 : forall P s σ τ ρ, set_In (equ_s (s[τ] .: σ >> τ) ρ)  P ->
                                          σmin_steps_possible P > 0.
 
Proof.
  intro.
  induction P.
  - intros. simpl in H. contradiction.
  - intros. simpl in H.
    destruct H.
    rewrite H. simpl.
    destruct (sexp_eqdec τ τ); try contradiction.
    lia.

    destruct a.
    simpl. specialize (IHP _ _ _ _ H).
    lia.

    simpl. specialize (IHP _ _ _  _ H).
    lia.
Qed.

Lemma σmin_step_app_gt_0 : forall P s s' t σ, set_In (equ  (App s[σ] t[σ]) s' ) P-> σmin_steps_possible P > 0.
Proof.
  intro.
  induction P.
  - intros. simpl in H. contradiction.
  - intros. simpl in H.
    destruct H.
    rewrite H. simpl.
    destruct (sexp_eqdec σ σ); try contradiction.
    lia.

    destruct a.
    simpl. specialize (IHP _ _ _ _ H).
    lia.

    simpl. specialize (IHP _ _ _ _ H).
    lia.
Qed.
