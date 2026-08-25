Require Export Exps.

Open Scope type_scope.

Inductive Assignment : Set :=
| exp_assign : Var -> exp -> Assignment
| sexp_assign : Var -> sexp -> Assignment.

Definition Subst := set Assignment.


Definition assign_sort_var (A: Assignment) : SortedVar :=
  match A with
  | exp_assign X _ => exp_var X
  | sexp_assign Y _ => sexp_var Y
  end.

Definition assign_sort_exp (A: Assignment) : SortedExp :=
  match A with
  | exp_assign _ s => Exp s
  | sexp_assign _ σ => SExp σ
  end.


Fixpoint look_up_exp (X: Var) (S: Subst) {struct S} : exp :=
 match S with
 | [] => VarExp X
 | mp :: S0 => match mp with
             | exp_assign Y t => if var_eqdec Y X then t else (look_up_exp X S0)
             | _ => look_up_exp X S0
             end
 end.

Fixpoint look_up_sexp (X: Var) (S: Subst) {struct S} : sexp :=
 match S with
 | [] => VarSExp X
 | mp :: S0 => match mp with
             | sexp_assign Y σ => if var_eqdec Y X then σ else (look_up_sexp X S0)
             | _ => look_up_sexp X S0
             end
end.

Fixpoint sub (s: exp) (S: Subst) : exp :=
match s with
  | Zero => Zero
  | App s t => App (sub s S) (sub t S)
  | Lam s => Lam (sub s S) 
  | Inst s σ => Inst (sub s S) (sub_s σ S)
  | VarExp X => look_up_exp X S
end
with sub_s (σ: sexp) (S: Subst) : sexp :=
 match σ with
 | I => I      
 | Shift => Shift
 | Cons s σ => Cons (sub s S) (sub_s σ S)  
 | Comp σ τ => Comp (sub_s σ S) (sub_s τ S)
 | VarSExp Y => look_up_sexp Y S
 end.


Fixpoint alist_rec (S1 S2: Subst) 
                   (F: Assignment -> Subst -> Subst -> Subst) : Subst :=
 match S1 with 
    | []          =>  S2
    | asmnt ::S0  =>  F asmnt S2 (alist_rec S0 S2 F)
 end.

Definition F_rec (S1: Subst) (asmnt : Assignment) (S2 S3: Subst) :=
  match asmnt with
  | exp_assign X t => (exp_assign X (sub t S1)) :: S3
  | sexp_assign Y σ => (sexp_assign Y (sub_s σ S1)) ::  S3
  end.

Definition sub_comp (S1 S2: Subst) := alist_rec S1 S2 (F_rec S2). 

Fixpoint subst_dom_vars (S : Subst) : set SortedVar :=
  match S with
    | [] => []   
    | asmnt :: S0 => match asmnt with
                   | exp_assign X t => set_add sortedvar_eqdec (exp_var X) (subst_dom_vars S0)
                   | sexp_assign Y σ => set_add sortedvar_eqdec (sexp_var Y) (subst_dom_vars S0)
                   end                 
   end.


Fixpoint dom_rec_aux (S : Subst) (St : set SortedVar) : set SortedVar :=
  match St with
    | [] => []
    | V::St0 => match V with
              | exp_var X => if (exp_eqdec (sub (VarExp X) S) (VarExp X)) then
                               (dom_rec_aux S St0) else
                               (set_add sortedvar_eqdec (exp_var X) (dom_rec_aux S St0))
              | sexp_var Y => if (sexp_eqdec (sub_s (VarSExp Y) S) (VarSExp Y)) then
                                (dom_rec_aux S St0) else
                                (set_add sortedvar_eqdec (sexp_var Y) (dom_rec_aux S St0))
              end
   end.                  


Definition dom_rec (S : Subst) := dom_rec_aux S (subst_dom_vars S).


Fixpoint im_rec_aux (S : Subst) (St : set SortedVar) : set SortedExp :=
  match St with
    | [] => []  
    | V::St0 => match V with
              | exp_var X => Exp (sub (VarExp X) S) :: (im_rec_aux S St0)
              | sexp_var Y => SExp (sub_s (VarSExp Y) S) :: (im_rec_aux S St0)
              end
  end.


Definition im_rec (S : Subst) := im_rec_aux S (dom_rec S).

Definition any_exp_vars (e: SortedExp) : set SortedVar :=
  match e with
  | Exp s => vars_of_exp s
  | SExp σ => vars_of_sexp σ
  end.
    
Fixpoint exps_set_vars (E: set SortedExp) : set SortedVar :=
  match E with
    | [] => []
    | sσ ::T0 => match sσ with
             | Exp s => set_union sortedvar_eqdec (vars_of_exp s) (exps_set_vars T0)
             | SExp σ => set_union sortedvar_eqdec (vars_of_sexp σ) (exps_set_vars T0)
             end
  end.



Definition In_dom_exp (X: Var) (S: Subst) := (sub (VarExp X) S) <> VarExp X.
Definition In_dom_sexp (Y: Var) (S: Subst) := (sub_s (VarSExp Y) S) <> VarSExp Y.



Definition subs_equiv (R1 : exp -> exp -> Prop) (R2: sexp -> sexp -> Prop) (S1 S2 : Subst) := (forall X, R1 (sub (VarExp X) S1) (sub (VarExp X) S2)) /\
                                                                                        (forall X, R2 (sub_s (VarSExp X) S1) (sub_s (VarSExp X) S2)).



Lemma dom_rec_aux_to_In_dom_exp : forall X S St, set_In (exp_var X) (dom_rec_aux S St) -> In_dom_exp X S.
Proof.
  intros. unfold In_dom_exp. simpl.
  induction St; simpl in H; try contradiction.
  destruct a as [X' | Y'].
  - destruct (exp_eqdec (look_up_exp X' S) (VarExp X')); subst; eauto.
    apply set_add_elim in H.
    destruct H. injection H as H; subst. trivial.
    now apply IHSt. 
  - destruct (sexp_eqdec (look_up_sexp Y' S) (VarSExp Y')); subst; eauto.
    apply set_add_elim in H.
    destruct H. inversion H.
    now apply IHSt.
Qed.

Lemma dom_rec_aux_to_In_dom_sexp : forall X S St, set_In (sexp_var X) (dom_rec_aux S St) -> In_dom_sexp X S.
Proof.
  intros. unfold In_dom_exp. simpl.
  induction St; simpl in H; try contradiction.
  destruct a as [X' | Y'].
  - destruct (exp_eqdec (look_up_exp X' S) (VarExp X')); subst; eauto.
    apply set_add_elim in H.
    destruct H. inversion H. now apply IHSt.
  - destruct (sexp_eqdec (look_up_sexp Y' S) (VarSExp Y')); subst; eauto.
    apply set_add_elim in H.
    destruct H. injection H as H; subst. trivial.
    now apply IHSt. 
Qed.


Lemma In_dom_to_dom_rec_aux_exp : forall X S St, In_dom_exp X S -> set_In (exp_var X) St -> set_In (exp_var X) (dom_rec_aux S St).
  intros. unfold In_dom_exp in H.
  simpl in H. induction St; simpl in H0|-*; try contradiction.
  destruct a as [X' | Y'].
  - case (exp_eqdec (look_up_exp  X' S) (VarExp X')); intro H1.
    + destruct H0. injection H0 as H0. rewrite H0 in H1. contradiction.
      now apply IHSt.
    + destruct H0. apply set_add_intro2. symmetry in H0. trivial.
      apply set_add_intro1. now apply IHSt.
  - case (sexp_eqdec (look_up_sexp Y' S) (VarSExp Y')); intro H1.
    + destruct H0. inversion H0. now apply IHSt.
    + destruct H0. inversion H0. apply set_add_intro1. now apply IHSt. 
Qed.

Lemma In_dom_to_dom_rec_aux_sexp : forall X S St, In_dom_sexp X S -> set_In (sexp_var X) St -> set_In (sexp_var X) (dom_rec_aux S St).
  intros. unfold In_dom_exp in H.
  simpl in H. induction St; simpl in H0|-*; try contradiction.
  destruct a as [X' | Y'].
   - case (exp_eqdec (look_up_exp X' S) (VarExp X')); intro H1.
    + destruct H0. inversion H0. now apply IHSt.
    + destruct H0. inversion H0. apply set_add_intro1. now apply IHSt. 
  - case (sexp_eqdec (look_up_sexp  Y' S) (VarSExp Y')); intro H1.
    + destruct H0. injection H0 as H0. rewrite H0 in H1. contradiction.
      now apply IHSt.
    + destruct H0. apply set_add_intro2. symmetry in H0. trivial.
      apply set_add_intro1. now apply IHSt.
Qed.



Lemma In_dom_to_subst_dom_vars_exp : forall X S,
    In_dom_exp X S -> set_In (exp_var X) (subst_dom_vars S).
Proof.
  intros. unfold In_dom_exp in H.
  simpl in H. induction S; simpl in *|-*.
  - apply H; trivial.
  - revert H.
    destruct a as [X' | Y'].
     +  case (var_eqdec X' X); intros H0 H.
       rewrite H0. apply set_add_intro2. trivial.
       apply set_add_intro1. apply IHS; trivial.
     + intro. apply set_add_intro1. now apply IHS.
Qed.


Lemma In_dom_to_subst_dom_vars_sexp : forall X S,
    In_dom_sexp X S -> set_In (sexp_var X) (subst_dom_vars S).
Proof.
  intros. unfold In_dom_sexp in H.
  simpl in H. induction S; simpl in *|-*.
  - apply H; trivial.
  - revert H.
    destruct a as [X' | Y'].
     + intro. apply set_add_intro1. now apply IHS.
     + case (var_eqdec Y' X); intros H0 H.
       rewrite H0. apply set_add_intro2. trivial.
       apply set_add_intro1. apply IHS; trivial.
Qed.


(* Jumping between two notion of expressing variable in domain *)
Lemma In_dom_eq_dom_rec_exp : forall X S, In_dom_exp X S <-> set_In (exp_var X) (dom_rec S).
Proof.
  intros. split; intro H.
  apply In_dom_to_dom_rec_aux_exp; trivial.
  apply In_dom_to_subst_dom_vars_exp; trivial.
  apply dom_rec_aux_to_In_dom_exp in H; trivial.
Qed.  

Lemma In_dom_eq_dom_rec_sexp : forall X S, In_dom_sexp X S <-> set_In (sexp_var X) (dom_rec S).
Proof.
  intros. split; intro H.
  apply In_dom_to_dom_rec_aux_sexp; trivial.
  apply In_dom_to_subst_dom_vars_sexp; trivial.
  apply dom_rec_aux_to_In_dom_sexp in H; trivial.
Qed.  


Lemma In_dom_eq_dom_flip_exp : forall X S, ~ In_dom_exp X S <-> ~ set_In (exp_var X) (dom_rec S).
Proof.
  intros.
  destruct (In_dom_eq_dom_rec_exp X S) as [H1 H2].
  assert (forall (P Q: Prop), (P -> Q) -> (~Q -> ~P)) as contrap. {
    eauto. }
  split.
  -  intros.
     specialize (contrap _ _ H2); eauto.
  -  intros.
     specialize (contrap _ _ H1); eauto.
Qed. 

Lemma In_dom_eq_dom_flip_sexp : forall X S, ~ In_dom_sexp X S <-> ~ set_In (sexp_var X) (dom_rec S).
Proof.
  intros.
  destruct (In_dom_eq_dom_rec_sexp X S) as [H1 H2].
  assert (forall (P Q: Prop), (P -> Q) -> (~Q -> ~P)) as contrap. {
    eauto. }
  split.
  -  intros.
     specialize (contrap _ _ H2); eauto.
  -  intros.
     specialize (contrap _ _ H1); eauto.
Qed. 


Lemma not_In_dom_lookup_exp : forall X S, ~ In_dom_exp X S -> look_up_exp X S = (VarExp X).
  intros.
  unfold In_dom_exp in H. simpl in H.
  unfold not in H.
  case (exp_eqdec (look_up_exp X S) (VarExp X)); intros.
  assumption. contradiction.
Qed.

Lemma not_In_dom_lookup_sexp : forall X S, ~ In_dom_sexp X S -> look_up_sexp X S = (VarSExp X).
  intros.
  unfold In_dom_sexp in H. simpl in H.
  unfold not in H.
  case (sexp_eqdec (look_up_sexp X S) (VarSExp X)); intros.
  assumption. contradiction.
Qed.


Lemma not_In_dom_lookup_flip_exp : forall X S,  look_up_exp X S = (VarExp X) -> ~ In_dom_exp X S.
Proof.
  now trivial. 
Qed.

Lemma not_In_dom_lookup_flip_sexp : forall X S,  look_up_sexp X S = (VarSExp X) -> ~ In_dom_sexp X S.
Proof.
  now trivial. 
Qed.



Lemma not_in_dom_lookup_same_exp : forall S X, ~set_In (exp_var X) (dom_rec S) -> look_up_exp X S = VarExp X.
Proof.
  intros.
  apply not_In_dom_lookup_exp.
  now apply In_dom_eq_dom_flip_exp.
Qed.  


Lemma not_in_dom_lookup_same_sexp : forall S X, ~set_In (sexp_var X) (dom_rec S) -> look_up_sexp X S = VarSExp X.
Proof.
  intros.
  apply not_In_dom_lookup_sexp.
  now apply In_dom_eq_dom_flip_sexp.
Qed.  




Lemma subst_comp_id_left : forall S, (sub_comp ([]) S) = S.
Proof.
  intros.  unfold sub_comp. simpl; trivial.
Qed.


(* look_up_ can be pushed inside a composition *)
Lemma look_up_sub_comp_exp: forall S S' X, look_up_exp X (sub_comp S S') = sub (look_up_exp X S) S'.
Proof.
  intros. induction S; simpl.
  rewrite subst_comp_id_left; trivial.
  destruct a. simpl.
  case (var_eqdec v X); intro H; trivial.
  simpl. apply IHS.
Qed.

Lemma look_up_sub_comp_sexp: forall S S' X, look_up_sexp X (sub_comp S S') = sub_s (look_up_sexp X S) S'.
Proof.
  intros. induction S; simpl.
  rewrite subst_comp_id_left; trivial.
  destruct a. simpl. apply IHS.
  simpl. case (var_eqdec v X); intro H; trivial.
Qed.


Lemma subst_comp_expand : (forall s S1 S2, sub s (sub_comp S1 S2) = sub (sub s S1) S2) /\
                           (forall σ S1 S2, sub_s σ (sub_comp S1 S2) = sub_s (sub_s σ S1) S2 ).
Proof.
  apply sigma_ind2; intros; simpl in *.
  - reflexivity.
  - rewrite H. now rewrite H0.
  - now rewrite H.
  - rewrite H. now rewrite H0.
  - now rewrite look_up_sub_comp_exp.
  - now simpl.
  - now simpl.
  - rewrite H. now rewrite H0.
  - rewrite H. now rewrite H0.
  - now rewrite look_up_sub_comp_sexp.
Qed.

Lemma subst_comp_assoc_exp: forall S1 S2 S3 t, sub t (sub_comp S1 (sub_comp S2 S3)) =
                                       sub t  (sub_comp (sub_comp S1 S2) S3).

Proof.
  intros. rewrite 4 (proj1 subst_comp_expand); trivial.
Qed.

Lemma subst_comp_assoc_sexp: forall S1 S2 S3 σ, sub_s σ (sub_comp S1 (sub_comp S2 S3)) =
                                           sub_s σ  (sub_comp (sub_comp S1 S2) S3).

Proof.
  intros. rewrite 4 (proj2 subst_comp_expand); trivial.
Qed.


Lemma in_subcomp_second_arg_exp : forall X S S', ~set_In (exp_var X) (dom_rec S) ->
                                        look_up_exp X (sub_comp S S') = look_up_exp X S'.
Proof.
  intros.
  rewrite look_up_sub_comp_exp.
  rewrite not_in_dom_lookup_same_exp; eauto.
Qed.  

Lemma in_subcomp_second_arg_sexp : forall X S S', ~set_In (sexp_var X) (dom_rec S) ->
                                             look_up_sexp X (sub_comp S S') = look_up_sexp X S'.
Proof.
  intros.
  rewrite look_up_sub_comp_sexp.
  rewrite not_in_dom_lookup_same_sexp; eauto.
Qed.  


Lemma vacous_subst_same : (forall s S, set_inter sortedvar_eqdec (dom_rec S) (vars_of_exp s) = [] ->
                                  sub s S = s) /\
                            (forall σ S, set_inter sortedvar_eqdec (dom_rec S) (vars_of_sexp σ) = [] ->
                                  sub_s σ S = σ).
Proof.
  apply sigma_ind2; intros; simpl in *; trivial. 
  - rewrite H. rewrite H0. trivial.
    apply set_nocommon_forall_inter_flip; intros.
    eapply set_nocommon_inter_forall_flip in H1 ; [ apply H1 | now apply set_union_intro2].
    apply set_nocommon_forall_inter_flip; intros.
    eapply set_nocommon_inter_forall_flip in H1 ; [ apply H1 | now apply set_union_intro1].
  - now rewrite H.
  - rewrite H. rewrite H0. trivial.
    apply set_nocommon_forall_inter_flip; intros.
    eapply set_nocommon_inter_forall_flip in H1 ; [ apply H1 | now apply set_union_intro2].
    apply set_nocommon_forall_inter_flip; intros.
    eapply set_nocommon_inter_forall_flip in H1 ; [ apply H1 | now apply set_union_intro1].
  - eapply set_nocommon_inter_forall_flip in H.
    eapply not_in_dom_lookup_same_exp in H. apply H.
    now left.
  - rewrite H. rewrite H0. trivial.
    apply set_nocommon_forall_inter_flip; intros.
    eapply set_nocommon_inter_forall_flip in H1 ; [ apply H1 | now apply set_union_intro2].
    apply set_nocommon_forall_inter_flip; intros.
    eapply set_nocommon_inter_forall_flip in H1 ; [ apply H1 | now apply set_union_intro1].
  - rewrite H. rewrite H0. trivial.
    apply set_nocommon_forall_inter_flip; intros.
    eapply set_nocommon_inter_forall_flip in H1 ; [ apply H1 | now apply set_union_intro2].
    apply set_nocommon_forall_inter_flip; intros.
    eapply set_nocommon_inter_forall_flip in H1 ; [ apply H1 | now apply set_union_intro1].
  - eapply set_nocommon_inter_forall_flip in H.
    eapply not_in_dom_lookup_same_sexp in H. apply H.
    now left.
Qed.    


Lemma sub_comp_var_diff_left: forall S V A, set_In V (dom_rec (sub_comp S ([A])%list )) ->
                                           V <> assign_sort_var A ->
                                           set_In V (dom_rec S).

Proof.
  intro S.
  induction S; intros; simpl in *;
    destruct V as [X | Y];
    destruct A as [X' | Y']; simpl in *.
    
  - apply In_dom_eq_dom_rec_exp in H.
    unfold In_dom_exp in H. simpl in H.
    destruct (var_eqdec X' X) as [Eq | nEq]; subst; contradiction. 
  - apply In_dom_eq_dom_rec_exp in H. unfold In_dom_exp in H.
    simpl in H. contradiction.
  - apply In_dom_eq_dom_rec_sexp in H.  
    unfold In_dom_sexp in H. simpl in H. contradiction.
  - apply In_dom_eq_dom_rec_sexp in H.
    unfold In_dom_sexp in H. simpl in H.
    destruct (var_eqdec Y' Y) as [Eq | nEq]; subst; contradiction. 
  - apply In_dom_eq_dom_rec_exp. unfold In_dom_exp. simpl.
    destruct a as [X'' | Y''].
    apply In_dom_eq_dom_rec_exp in H. unfold In_dom_exp in H. simpl in H.
    destruct (var_eqdec X'' X) as [Eq | nEq]; subst.
    assert (H0' : X <> X') by congruence. clear H0.
    intro. apply H. rewrite H0. simpl.
    destruct (var_eqdec X' X) as [Eq | nEq]; [symmetry in Eq; contradiction | reflexivity].
    specialize (IHS (exp_var X) (exp_assign X' e)).
    repeat rewrite <- In_dom_eq_dom_rec_exp in IHS.
    repeat unfold In_dom_exp in IHS.
    simpl in IHS. apply IHS; eauto.
    apply In_dom_eq_dom_rec_exp in H. unfold In_dom_exp in H. simpl in H.
    specialize (IHS (exp_var X) (exp_assign X' e)).
    repeat rewrite <- In_dom_eq_dom_rec_exp in IHS.
    repeat unfold In_dom_exp in IHS.
    simpl in IHS. apply IHS; eauto.
  - apply In_dom_eq_dom_rec_exp. unfold In_dom_exp. simpl.
    destruct a as [X'' | Y''].
    rewrite <-In_dom_eq_dom_rec_exp in H. unfold In_dom_exp in H. simpl in H.
    destruct (var_eqdec X'' X); subst.
    intro. apply H.  rewrite H1. now simpl.
    specialize (IHS (exp_var X) (sexp_assign Y' s)).
    repeat rewrite <- In_dom_eq_dom_rec_exp in IHS.
    repeat unfold In_dom_exp in IHS. simpl in IHS.
    apply IHS; eauto.
    apply In_dom_eq_dom_rec_exp in H. unfold In_dom_exp in H. simpl in H. 
    specialize (IHS (exp_var X) (sexp_assign Y' s)).
    repeat rewrite <- In_dom_eq_dom_rec_exp in IHS.
    repeat unfold In_dom_exp in IHS. simpl in IHS.
    apply IHS; eauto.
  - apply In_dom_eq_dom_rec_sexp. unfold In_dom_sexp. simpl.
    destruct a as [X'' | Y''].
    rewrite <-In_dom_eq_dom_rec_sexp in H. unfold In_dom_sexp in H. simpl in H.
    specialize (IHS (sexp_var Y) (exp_assign X' e)).
    repeat rewrite <- In_dom_eq_dom_rec_sexp in IHS.
    repeat unfold In_dom_sexp in IHS. simpl in IHS.
    apply IHS; eauto.
    rewrite <-In_dom_eq_dom_rec_sexp in H. unfold In_dom_sexp in H. simpl in H.
    destruct (var_eqdec Y'' Y); subst.
    intro. apply H.  rewrite H1. now simpl.
    specialize (IHS (sexp_var Y) (exp_assign X' e)).
    repeat rewrite <- In_dom_eq_dom_rec_sexp in IHS.
    repeat unfold In_dom_sexp in IHS. simpl in IHS.
    apply IHS; eauto.
  - apply In_dom_eq_dom_rec_sexp. unfold In_dom_sexp. simpl.
    destruct a as [X'' | Y''].
    apply In_dom_eq_dom_rec_sexp in H. unfold In_dom_sexp in H. simpl in H.
    specialize (IHS (sexp_var Y) (sexp_assign Y' s)).
    repeat rewrite <- In_dom_eq_dom_rec_sexp in IHS.
    repeat unfold In_dom_sexp in IHS.
    simpl in IHS. apply IHS; eauto.
 
    apply In_dom_eq_dom_rec_sexp in H. unfold In_dom_sexp in H. simpl in H.
    destruct (var_eqdec Y'' Y) as [Eq | nEq]; subst.
    assert (H0' : Y <> Y') by congruence. clear H0.
    intro. apply H. rewrite H0. simpl.
    destruct (var_eqdec Y' Y) as [Eq | nEq]; [symmetry in Eq; contradiction | reflexivity].
    specialize (IHS (sexp_var Y) (sexp_assign Y' s)).
    repeat rewrite <- In_dom_eq_dom_rec_sexp in IHS.
    repeat unfold In_dom_sexp in IHS.
    simpl in IHS. apply IHS; eauto.
Qed.  



Lemma exp_sexp_desubst : (forall t V A, set_In V (vars_of_exp (sub t ([A])%list)) ->
                                   V <> assign_sort_var A ->
                                   ~set_In V (any_exp_vars (assign_sort_exp A)) ->
                                   set_In V (vars_of_exp t)) /\
                             (forall σ  V A, set_In V (vars_of_sexp (sub_s σ ([A])%list)) ->
                                        V <> assign_sort_var A ->
                                        ~set_In V (any_exp_vars (assign_sort_exp A)) ->
                                         set_In V (vars_of_sexp σ)).
Proof.
  apply sigma_ind2; intros; simpl in *;
  destruct V as [X' | Y']; destruct A as [X'' | Y'']; simpl in *; trivial;
  try first [(apply set_union_elim in H1;
    destruct H1; [
    apply set_union_intro1;  eapply H;
    [apply H1 | now simpl| now simpl] | 
    apply set_union_intro2; eapply H0;
    [apply H1 | now simpl | now simpl]]) |
    eapply H ; [apply H0 | now simpl | now simpl] |
    destruct (var_eqdec X'' X); subst; try contradiction;
    simpl in H; assumption |
    destruct (var_eqdec Y'' Y); subst; try contradiction;
    simpl in H; assumption].          
Qed.


Lemma exps_X_clear : (forall t V A, ~set_In V (any_exp_vars (assign_sort_exp A)) ->
                                    V= assign_sort_var A ->  
                                   ~set_In V (vars_of_exp (sub t ([A])%list)))

                         /\ (forall σ V A, ~set_In V (any_exp_vars (assign_sort_exp A)) ->
                                     V= assign_sort_var A -> 
                                     ~set_In V (vars_of_sexp (sub_s σ ([A])%list))).
Proof.
    apply sigma_ind2; intros; simpl in *; 
    destruct V as [X' | Y']; destruct A as [X'' | Y'']; simpl in *;intro; trivial;
      
    try now first [apply set_union_elim in H3; destruct H3;
    [ eapply H; revgoals;  [apply H3 | now simpl | now simpl] |
      eapply H0; revgoals; [apply H3 | now simpl | now simpl]] |
     congruence |
     eapply H; revgoals; [apply H2 | now simpl | now simpl]].

    - injection H0; intro HEq;
      destruct (var_eqdec X'' X); [contradiction |
      simpl in H1; destruct H1 ;[congruence | trivial]].
    - destruct H1; [congruence | trivial].
    - destruct H1; [congruence | trivial].
    - injection H0; intro HEq;
      destruct (var_eqdec Y'' Y); [contradiction |
      simpl in H1; destruct H1 ;[congruence | trivial]].
Qed.
    
