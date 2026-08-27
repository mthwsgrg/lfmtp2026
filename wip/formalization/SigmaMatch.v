Require Export Problems.


(** Equivalence with respect to σmin-rules *)

Unset Elimination Schemes.
Inductive σmin_equiv : exp -> exp -> Prop :=
| σmin_subst_app (s t : exp) (σ : sexp) :  σmin_equiv ((App s t)[σ]) (App s[σ] t[σ])
| σmin_subst_lam (s : exp) (σ : sexp) :  σmin_equiv  ((Lam s)[σ])  (Lam (s[Zero .: (σ >> ↑)]))
| σmin_subst_comp (s: exp) (σ τ: sexp) : σmin_equiv (s[σ])[τ] s[σ >> τ]
                                               
| σmin_equiv_refl (s : exp) :  σmin_equiv s s
| σmin_equiv_sym (s t : exp) :  σmin_equiv s t -> σmin_equiv t s
| σmin_equiv_trans (s t u : exp) :  σmin_equiv s t -> σmin_equiv t u -> σmin_equiv s u
| σmin_equiv_app (s1 s2 t1 t2 : exp) :  σmin_equiv s1 s2 -> σmin_equiv t1 t2 -> σmin_equiv (App s1 t1) (App s2 t2)
| σmin_equiv_lam (s1 s2 : exp) :  σmin_equiv s1 s2 -> σmin_equiv (Lam s1) (Lam s2)
| σmin_equiv_subst (s1 s2 : exp) (σ τ : sexp) :  σmin_equiv s1 s2 -> σmin_equivs σ τ -> σmin_equiv s1[σ] s2[τ]
with σmin_equivs : sexp -> sexp -> Prop :=
| σmin_comp_cons (s : exp) (σ τ : sexp) :  σmin_equivs  ((s .: σ) >> τ) (s[τ] .: (σ >> τ)) 
| σmin_comp_assoc (σ τ θ : sexp) :  σmin_equivs ((σ >> τ) >> θ) (σ >> (τ >> θ))

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
| smatch_Conslaw : forall S P s σ τ σ' τ', set_In (equ_s (s[σ] .: (σ >> τ)) (σ' >> τ')) P ->
                                      smatch (S,P) (S, P |+ (equ_s ((s .: σ) >> τ) (σ' >> τ')) \ (equ_s (s[τ] .: (σ >> τ)) (σ' >> τ') ))
| smatch_Complaw : forall S P s s' σ τ ρ, set_In (equ s[σ >> τ] s'[ρ]) P ->
                                     smatch (S, P) (S, (P |+ (equ s[σ][τ] s'[ρ])) \ (equ s[σ >> τ] s'[ρ]))
                                        
| smatch_inst_exp : forall S S' P X s, (~ set_In (exp_var X) (lhvars_Probl P)) ->
                           (set_In (equ s (VarExp X)) P) ->
                           S' = sub_comp S ( [exp_assign X s])  -> 
                           smatch (S,P)
                             (S',(P\(equ s (VarExp X)))|^^[exp_assign X s])
| smatch_inst_sexp : forall S S' P Y σ, (~ set_In (sexp_var Y) (lhvars_Probl P)) ->
                                   set_In (equ_s σ (VarSExp Y)) P ->
                                   S' = sub_comp S ([sexp_assign Y σ]) ->
                                   smatch (S,P)
                                        (S', (P\(equ_s σ (VarSExp Y)))|^^[sexp_assign Y σ]).
                            




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

Definition σmin_rhs_form_exp (s: exp) : nat :=
  match s with
  | Lam s[Zero .: σ >> ↑] => 1
  | App s[σ] t[τ] => if sexp_eqdec σ τ then 1 else 0
  | s[σ >> τ] => 1
  | _ => 0
  end.

Definition σmin_rhs_form_sexp (σ: sexp) : nat :=
  match σ with
  | σ >> τ >> ρ => 1
  | (s .: σ)>> τ => 1
  | _ => 0
  end.        

Fixpoint σmin_steps_possible (P: Problem) : nat :=
  match P with
  | [] => 0
  | (equ_s σ τ) :: P0 => σmin_rhs_form_sexp σ + σmin_steps_possible P0
  | (equ s t) :: P0 => σmin_rhs_form_exp s + σmin_steps_possible P0
  end.
