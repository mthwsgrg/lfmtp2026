Require Import List ListSet.
Unset Elimination Schemes.
Import ListNotations.



Definition Var := nat.

Lemma var_eqdec : forall (m n: Var), {m = n} + {m <> n}.
  decide equality.
Defined.


(** σ-expressions

It corresponds to the following syntax:

s,t ::= 0 | s t | λ.s | s[σ] | X
σ,τ ::= ↑ | I | s .: σ | s >> t  

- VarExp is the term expression variables
- Expressions don't have substitution variables (for now).


*)

Inductive exp := Zero
               | App (s t: exp) : exp
               | Lam (s: exp): exp
               | Inst (s: exp) (σ: sexp): exp
               | VarExp (X: Var) : exp
with sexp :=    I : sexp
                | Shift : sexp
                | Cons (s: exp) (σ: sexp) : sexp
                | Comp (σ τ: sexp) : sexp.
Set Elimination Schemes.
Scheme exp_ind := Induction for exp Sort Type
with  sexp_ind := Induction for sexp Sort Type.
Combined Scheme sigma_ind from exp_ind, sexp_ind.

Scheme exp_ind2 := Induction for exp Sort Prop
with sexp_ind2 := Induction for sexp Sort Prop.
Combined Scheme sigma_ind2 from exp_ind2, sexp_ind2.

Scheme exp_ind3 := Induction for exp Sort Prop.
Scheme sexp_ind3 := Induction for sexp Sort Prop.

Notation "s [ σ ]" := (Inst s σ).
Notation "σ >> τ" := (Comp σ τ) (at level 56, right associativity).
Notation "s .: σ" := (Cons s σ) (at level 58).
Notation "↑" := Shift.



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
| σmin_equiv_asubst (s1 s2 : exp) (σ τ : sexp) :  σmin_equiv s1 s2 -> σmin_equivs σ τ -> σmin_equiv s1[σ] s2[τ]
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



(**  An Equation is either a term equation or substitution equation  *)

Inductive Equation : Set :=
| equ : exp -> exp -> Equation
| equ_s : sexp -> sexp -> Equation.


Open Scope type_scope.

(** Definition of Substitution, Problem, and Tuple where Tuple describe the change of state after each smatch steps*)

Definition Subst := set (Var * exp).
Definition Problem := set Equation.   
Definition Tuple := (Subst * Problem).


(** Definition of instantiation of a term/substitution with a Subst *)

Fixpoint look_up (X : Var) (S : Subst) {struct S}: exp :=
match S with
 | []         => VarExp X
 | (Y,t)::S0  => if var_eqdec Y X then t else (look_up X S0)
end.

Fixpoint sub (s: exp) (S: Subst) : exp :=
match s with
  | Zero => Zero
  | App s t => App (sub s S) (sub t S)
  | Lam s => Lam (sub s S) 
  | Inst s σ => Inst (sub s S) (sub_s σ S)
  | VarExp X => look_up X S
end
with sub_s (σ: sexp) (S: Subst) : sexp :=
 match σ with
 | I => I      
 | Shift => Shift
 | Cons s σ => Cons (sub s S) (sub_s σ S)  
 | Comp σ τ => Comp (sub_s σ S) (sub_s τ S)
 end.



(** Expressions, and Equations have decidable equality *)

Lemma expression_eqdec : (forall s t : exp, {s = t} + {s <> t}) *
                           (forall σ τ : sexp, {σ = τ} + {σ <> τ}).
  apply sigma_ind; intros.
  - destruct t; (try (right; discriminate)).
    + left. reflexivity.
  - destruct t0; (try (right; discriminate)).
    + specialize (H t0_1). specialize (H0 t0_2).
      destruct H.
      * destruct H0.
        ** rewrite e. rewrite e0. left. reflexivity.
        ** rewrite e. right. unfold not in *. intros. inversion H; eauto.
      * destruct H0.
        **  rewrite e. right. unfold not in *. intros. inversion H; eauto.
        **  right. unfold not in *. intros. inversion H; eauto.
  - destruct t; (try (right; discriminate)).
    case (H t); intros.
    rewrite e. now left.
    unfold not in *. right; intros.  inversion H0; eauto.
  - destruct t; (try (right; discriminate)).
    case (H t); intros.
    case (H0 σ0); intros.
    rewrite e. rewrite e0. now left.
    unfold not in *. right. intros. inversion H1; eauto.
    unfold not in *. right. intros. inversion H1; eauto.
  - destruct t; (try (right; discriminate)).  
    case (var_eqdec X X0); intros; eauto.
    unfold not in *. right. intros. inversion H; eauto.
  - destruct τ; (try (right; discriminate)).
    now left.
  - destruct τ; (try (right; discriminate)).
    now left.
  - destruct τ; (try (right; discriminate)).
    case (H s0); intros.
    case (H0 τ); intros.
    rewrite e. rewrite e0. now left.
    rewrite e. unfold not in *. right; intros. inversion H1; eauto.
    unfold not in *.  right; intros. inversion H1; eauto.
  - destruct τ0; (try (right; discriminate)).
    case (H τ0_1); intros.
    case (H0 τ0_2); intros.
    rewrite e. rewrite e0. now left.
    unfold not in *. right; intros. inversion H1; eauto.
    unfold not in *. right; intros. inversion H1; eauto.
Defined.

Lemma exp_eqdec : forall s t: exp, {s=t} + {s <> t}.
  intros.
  pose proof expression_eqdec.
  destruct H.
  exact (s0 s t).
Defined.

Lemma sexp_eqdec : forall σ τ: sexp, {σ=τ} + {σ <> τ}.
  intros.
  pose proof expression_eqdec.
  destruct H.
  exact (s0 σ τ).
Defined.


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

  


(** Some Helper functions *)

Fixpoint alist_rec (S1 S2: Subst) 
                   (F: Var -> exp -> Subst -> Subst -> Subst) : Subst :=
 match S1 with 
    | []          =>  S2
    | (X,t)::S0  =>  F X t S2 (alist_rec S0 S2 F)
 end.

Definition F_rec (S1: Subst) (X:Var) (t:exp) (S2 S3: Subst) := (X, sub t S1)::S3.


Definition sub_comp (S1 S2: Subst) := alist_rec S1 S2 (F_rec S2). 



(** subs_Problem applies a subtitution to a generic problem *)

Fixpoint subs_Problem (P : Problem) (S : Subst) : Problem :=
  match P with
    | [] => []
    | (equ s t )::P0 => (equ (sub s S) (sub t S))::(subs_Problem P0 S)
    | (equ_s σ τ )::P0 => (equ_s (sub_s σ S) (sub_s τ S))::(subs_Problem P0 S) 
  end.

(** subs_Problem applies a subtitution to right hand side of a generic problem *)

Fixpoint subs_Problem_right (P : Problem) (S : Subst) : Problem :=
  match P with
    | [] => []
    | (equ s t )::P0 => (equ s (sub t S))::(subs_Problem_right P0 S)
    | (equ_s σ τ )::P0 => (equ_s σ (sub_s τ S))::(subs_Problem_right P0 S) 
  end.



Fixpoint exp_vars (s : exp) {struct s} : set Var := 
match s with
 | Zero     => empty_set _
 | App s t  => set_union var_eqdec (exp_vars s) (exp_vars t)
 | Lam s => exp_vars s                      
 | Inst s σ => set_union var_eqdec (exp_vars s) (exp_vars_s σ)
 | VarExp X => set_add var_eqdec X (empty_set _)
end
with exp_vars_s (σ: sexp) {struct σ} : set Var :=
 match σ with
 | I  => empty_set _
 | Shift => empty_set _
 | Comp σ τ => set_union var_eqdec (exp_vars_s σ) (exp_vars_s τ)
 | Cons s σ => set_union var_eqdec (exp_vars s) (exp_vars_s σ)                      
end.


Fixpoint lhvars_Probl (P : Problem) :=
  match P with
  | [] => []
  | (equ s t) :: P0 => set_union var_eqdec (exp_vars s) (lhvars_Probl P0)
  | (equ_s σ τ) :: P0 => set_union var_eqdec (exp_vars_s σ) (lhvars_Probl P0)                       
  end.  


Fixpoint Problem_vars (P : Problem) : set Var :=
  match P with
    | [] => []
    | (equ s t)::P0 => set_union var_eqdec (exp_vars s)
                   (set_union var_eqdec (exp_vars t) (Problem_vars P0))
    | (equ_s σ τ)::P0 => set_union var_eqdec (exp_vars_s σ)
                       (set_union var_eqdec (exp_vars_s τ) (Problem_vars P0))               
  end.


(** subst_dom_vars extracts the variables that contains the substitution domain *)

Fixpoint subst_dom_vars (S : Subst) : set Var :=
  match S with
    | [] => []   
    | (X,t)::S0 => set_add var_eqdec X (subst_dom_vars S0)
  end.  



(** dom_rec_aux is a auxiliar function to build the correct domain of a substitution *)

Fixpoint dom_rec_aux (S : Subst) (St : set Var) : set Var :=
  match St with
    | [] => []
    | X::St0 => if (exp_eqdec (sub (VarExp X) S) (VarExp X)) then
                   (dom_rec_aux S St0) else
                   (set_add var_eqdec X (dom_rec_aux S St0))
  end.                  

(** dom_rec is the recursive function that gives the domain of a substitution *)

Definition dom_rec (S : Subst) := dom_rec_aux S (subst_dom_vars S).

(** im_rec_aux is a auxiliar function to build the correct image of a substitution *)

Fixpoint im_rec_aux (S : Subst) (St : set Var) : set exp :=
  match St with
    | [] => []  
    | X::St0 => (sub (VarExp X) S)::(im_rec_aux S St0) 
  end.

(** im_rec is the recursive function that gives the image of a substitution *)

Definition im_rec (S : Subst) := im_rec_aux S (dom_rec S).



(** exps_set_vars gives the set of variables that occur in a set of expression *)

Fixpoint exps_set_vars (T: set exp) : set Var :=
  match T with
    | [] => []
    | s::T0 => set_union var_eqdec (exp_vars s) (exps_set_vars T0)        
  end.

(** im_vars gives the set of variables that occur in the image of a substiturion *)

Definition im_vars (S : Subst) := exps_set_vars (im_rec S). 


Notation "P \ u" := (set_remove Equation_eqdec u P) (at level 67).

(*Notation "P |^^ S" := (subs_Problem P S) (at level 67). *)

Notation "P |^^ S" := (subs_Problem_right P S) (at level 67). 
Notation "P |+ u" := (set_add Equation_eqdec u P) (at level 67).

Definition In_dom (X : Var) (S : Subst) :=  (sub (VarExp X) S) <> VarExp X . 
Notation "X € S" := (In_dom X S) (at level 67).

Definition subs_equiv (E : exp -> exp -> Prop) (S S' : Subst) := forall X,  E (sub (VarExp X) S)                                                                                     (sub (VarExp X) S'). 

Notation "S ~:c S'" := (subs_equiv σmin_equiv S S') (at level 67).


(** Unit tests 

Definition S1 := (1, VarExp 2) :: nil.
Definition S2 := (1, App Zero Zero) :: nil.
Compute (sub_comp S1 S2).
Compute (sub (VarExp 1) (sub_comp S1 S2)).
Compute dom_rec (sub_comp S1 S2).
*)



(** Inductive definition of σmin-procedure *)
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
                                        
| smatch_inst : forall S S' P X s, (~ set_In X (lhvars_Probl P)) ->
                           (set_In (equ s (VarExp X)) P) ->
                           S' = sub_comp S ((X,s) :: nil)  -> 
                           smatch (S,P)
                                   (S',((P\(equ s (VarExp X))|^^((X,s)::nil)))).




Definition valid_tuple (T : Tuple) :=
  let S := (fst T) in
  let P := (snd T) in
  ( set_inter var_eqdec (dom_rec S) (Problem_vars P) = [] ) /\
  ( set_inter var_eqdec (dom_rec S) (im_vars S) = [] ) .


(** A substitution is a solution to a σmin-matching problem if it satisfies this predicate *)
Definition match_sol (S' :Subst) (T : Tuple) :=
  let S := (fst T) in
  let P := (snd T) in
  ( forall s t, set_In (equ s t) P ->  σmin_equiv s (sub t S') ) /\
  ( forall σ τ, set_In (equ_s σ τ) P -> σmin_equivs σ (sub_s τ S')) /\  
  ( exists S'', (sub_comp S S'') ~:c S' ) /\
  set_inter var_eqdec (lhvars_Probl P) (dom_rec S') = []. 




(*
Lemma sub_comp_left_op_preced (S : Subst) (X: Var) : forall S', set_In X (dom_rec S) ->
                                                           looksub_comp X (sub_comp S S') = look_up X S   
*)

Lemma subst_sub_σmin_gen : (forall s S S', S ~:c S'  -> σmin_equiv (sub s S)
                                                        (sub s S')) /\
                    (forall σ S S', S ~:c S' -> σmin_equivs (sub_s σ S)
                                                     (sub_s σ S')).
Proof.  
  apply sigma_ind2; intros; simpl.
  - constructor.
  - apply σmin_equiv_app; eauto.
  - apply σmin_equiv_lam; eauto.
  - apply σmin_equiv_asubst; eauto.
  - unfold subs_equiv in H.
    specialize (H X). now simpl in H.
  - constructor.
  - constructor.
  - apply σmin_equivs_cons; eauto.
  - apply σmin_equivs_comp; eauto.
Qed. 


Lemma subst_sub_σmin_gen_left : (forall s S S', S ~:c S'  -> σmin_equiv (sub s S)
                                                         (sub s S')).
Proof.
  apply subst_sub_σmin_gen.
Qed.

Lemma subst_sub_σmin_gen_right : (forall σ S S', S ~:c S' -> σmin_equivs (sub_s σ S)
                                                     (sub_s σ S')).
Proof.
  apply subst_sub_σmin_gen.
Qed.


Lemma subst_sub_σmin : (forall s t t' X, σmin_equiv t t' -> σmin_equiv (sub s ((X,t) :: nil))
                                                        (sub s ((X,t') :: nil))) /\
                    (forall σ t t' X, σmin_equiv t t' -> σmin_equivs (sub_s σ ((X,t) :: nil))
                                                     (sub_s σ ((X,t') :: nil))).
Proof.  
  apply sigma_ind2; intros; simpl.
  - constructor.
  - apply σmin_equiv_app; eauto.
  - apply σmin_equiv_lam; eauto.
  - apply σmin_equiv_asubst; eauto.
  - case (var_eqdec X0 X); intros.
    + assumption.
    + constructor.
  - constructor.
  - constructor.
  - apply σmin_equivs_cons; eauto.
  - apply σmin_equivs_comp; eauto.
Qed.  



(** INFRASTRUCTURE LEMMAS START *)

(** SET RELATTED INFRA LEMMAS START *)


Lemma set_nocommon_1_2 : forall S S', (forall (X: Var), set_In X S -> ~set_In X S') <-> (forall (X: Var), set_In X S' -> ~set_In X S) .
  intros.
  split ; intros; unfold not in *; intros;now specialize (H _ H1). 
Qed.

Lemma set_nocommon_1_3: forall S S', (forall X, set_In X S -> ~set_In X S') <-> set_inter var_eqdec S S' = [].
  intros.
  split.
  -  revert S'. induction S; intros.
     +  now simpl.
     +  simpl.
        specialize (H a) as H_a.
        simpl in H_a. specialize (H_a (or_introl eq_refl)).
        apply (set_mem_complete2 var_eqdec) in H_a.
        rewrite H_a.
        apply IHS; intros.
        apply H. simpl. now right.     
  - revert S'.
    induction S; intros.
    + destruct H0.
    + simpl in *.
      destruct H0.
      * subst.
        destruct (set_mem var_eqdec X S') eqn: HEqn.
        inversion H.
        now apply (set_mem_complete1 var_eqdec).
      * apply IHS; eauto.
        destruct (set_mem var_eqdec a S').
        inversion H.
        assumption.      
Qed.


Lemma set_nocommon_1_3_for: forall S S', (forall X, set_In X S -> ~set_In X S') -> set_inter var_eqdec S S' = [].
Proof.
  apply set_nocommon_1_3.
Qed.

Lemma set_nocommon_1_3_back: forall S S', set_inter var_eqdec S S' = [] -> (forall X, set_In X S -> ~set_In X S').
Proof.
  apply set_nocommon_1_3.
Qed.


Lemma set_nocommon_3_4 : forall S S', set_inter var_eqdec S S' = [] <-> set_inter var_eqdec S' S = [].
Proof.
  intros S S'.
  split; intros; apply set_nocommon_1_3; apply set_nocommon_1_2;    now apply set_nocommon_1_3.  
Qed.


  
Lemma not_in_if_inter_empty : forall X S S',   set_In X S ->
                                          set_inter var_eqdec S S' = [] ->
                                          ~ set_In X S'.
  
Proof.
  intros.
  destruct (set_nocommon_1_3 S S') as [H1 H2]; eauto.
Qed.


Lemma comm_empty_inter : forall S S', set_inter var_eqdec S S' = [] ->
                                 set_inter var_eqdec S' S = [].
Proof.
  apply set_nocommon_3_4.
Qed.


(** SET INFRA LEMMAS END *)


(** DOM/SUBST/EXP INFRA LEMMAS START *)

Lemma push_subst_problem : forall s t S P, set_In (equ s t) P -> set_In (equ s (sub t S)) (P |^^ S).
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

Lemma dom_rec_aux_to_In_dom : forall X S St, set_In X (dom_rec_aux S St) -> X € S.
Proof.
  intros. unfold In_dom. simpl.
  induction St; simpl in H; try contradiction.
  destruct (exp_eqdec (look_up a S) (VarExp a)); subst; eauto.
  apply set_add_elim in H.
  destruct H. rewrite H. trivial.
  apply IHSt. apply H.
Qed.

Lemma In_dom_to_dom_rec_aux : forall X S St,                             
    X € S -> set_In X St -> set_In X (dom_rec_aux S St).
  intros. unfold In_dom in H.
  simpl in H. induction St; simpl in H0|-*; try contradiction.
  case (exp_eqdec (look_up a S) (VarExp a)); intro H1.
  - destruct H0. rewrite H0 in H1. contradiction.
    apply IHSt; trivial.
  - destruct H0. rewrite H0. apply set_add_intro2; trivial.
    apply set_add_intro1. now apply IHSt.
Qed.

Lemma In_dom_to_subst_dom_vars : forall X S,
    X € S -> set_In X (subst_dom_vars S).
Proof.
  intros. unfold In_dom in H.
  simpl in H. induction S; simpl in *|-*.
  - apply H; trivial.
  - revert H.
    destruct a.
    case (var_eqdec v X); intros H0 H.
    rewrite H0. apply set_add_intro2. trivial.
    apply set_add_intro1. apply IHS; trivial.
Qed.

Lemma In_dom_eq_dom_rec : forall X S, X € S <-> set_In X (dom_rec S).
Proof.
  intros. split; intro H.
  apply In_dom_to_dom_rec_aux; trivial.
  apply In_dom_to_subst_dom_vars; trivial.
  apply dom_rec_aux_to_In_dom in H; trivial.
Qed.  
  
Lemma In_dom_eq_dom_flip : forall X S, ~ In_dom X S <-> ~ set_In X (dom_rec S).
Proof.
  intros.
  destruct (In_dom_eq_dom_rec X S) as [H1 H2].
  assert (forall (P Q: Prop), (P -> Q) -> (~Q -> ~P)) as contrap. {eauto.}.
  split.
  -  intros.
     specialize (contrap _ _ H2); eauto.
  -  intros.
     specialize (contrap _ _ H1); eauto.
Qed. 

 
Lemma not_In_dom_lookup : forall X S, ~ In_dom X S -> look_up X S = (VarExp X).
  intros.
  unfold In_dom in H. simpl in H.
  unfold not in H.
  case (exp_eqdec (look_up X S) (VarExp X)); intros.
  assumption. contradiction.
Qed.


Lemma not_In_dom_lookup_flip : forall X S,  look_up X S = (VarExp X) -> ~ In_dom X S.
  intros.
  unfold In_dom. simpl.
  unfold not in *.
  now intros.
Qed.


Lemma not_in_dom_lookup_same : forall S X, ~set_In X (dom_rec S) -> look_up X S = VarExp X.
Proof.
  intros.
  apply not_In_dom_lookup.
  now apply In_dom_eq_dom_flip.
Qed.  

Lemma not_in_dom_lookup_rev : forall S X, look_up X S = VarExp X -> ~set_In X (dom_rec S).
Proof.
  intros.
  apply In_dom_eq_dom_flip.
  now apply not_In_dom_lookup_flip.
Qed.  






Lemma subst_same_var_nocommon_both : (forall s S, set_inter var_eqdec (exp_vars s) (dom_rec S) = [] -> sub s S = s) /\
                                     (forall σ S, set_inter var_eqdec (exp_vars_s σ) (dom_rec S) = [] -> sub_s σ S = σ).
Proof.
  apply sigma_ind2; intros.
  - simpl. trivial.
  - simpl. rewrite H. rewrite H0.
    + trivial.
    + apply set_nocommon_1_3.
      intros.
      apply (set_nocommon_1_3_back (exp_vars (App s t)) (dom_rec S)) with (X:=X) in H1.
      apply H1. simpl.
      now apply set_union_intro2.
    + apply set_nocommon_1_3.
      intros.
      apply (set_nocommon_1_3_back (exp_vars (App s t)) (dom_rec S)) with (X:=X) in H1.
      apply H1. simpl.
      now apply set_union_intro1.
  - simpl. rewrite H.
    + trivial.
    + apply set_nocommon_1_3.
      intros.
      apply (set_nocommon_1_3_back (exp_vars (Lam s)) (dom_rec S)) with (X:=X) in H1; eauto.
  - simpl. rewrite H. rewrite H0.
    + trivial.
    + apply set_nocommon_1_3; intros.
      apply (set_nocommon_1_3_back (exp_vars (s[σ])) (dom_rec S)) with (X:=X) in H1; eauto.
      simpl.
      now apply set_union_intro2.
    + apply set_nocommon_1_3; intros.
      apply (set_nocommon_1_3_back (exp_vars (s[σ])) (dom_rec S)) with (X:=X) in H1; eauto.
      simpl.
      now apply set_union_intro1.
  - simpl. 
    apply (set_nocommon_1_3_back (exp_vars (VarExp X)) (dom_rec S)) with (X:=X) in H.
    now apply not_in_dom_lookup_same.
    simpl. now left.
  -  now simpl.
  -  now simpl.
  -  simpl. rewrite H. rewrite H0.
     + trivial.
     + apply set_nocommon_1_3; intros.
       apply (set_nocommon_1_3_back (exp_vars_s (s .: σ))) with (X:=X) in H1; eauto.
       simpl. now apply set_union_intro2.
     + apply set_nocommon_1_3; intros.
       apply (set_nocommon_1_3_back (exp_vars_s (s .: σ))) with (X:=X) in H1; eauto.
       simpl. now apply set_union_intro1.
  - simpl. rewrite H. rewrite H0.
    + trivial.
    + apply set_nocommon_1_3; intros.
      apply (set_nocommon_1_3_back (exp_vars_s (σ >> τ))) with (X:=X) in H1; eauto.
      simpl. now apply set_union_intro2.
    + apply set_nocommon_1_3; intros.
      apply (set_nocommon_1_3_back (exp_vars_s (σ >> τ))) with (X:=X) in H1; eauto.
      simpl. now apply set_union_intro1.
Qed.

Lemma subst_same_var_nocommon :forall s S, set_inter var_eqdec (exp_vars s) (dom_rec S) = [] ->  sub s S = s.
Proof.
  apply subst_same_var_nocommon_both.
Qed.

Lemma subst_same_var_nocommon_sexp : forall σ S, set_inter var_eqdec (exp_vars_s σ) (dom_rec S) = [] ->
                                       sub_s σ S = σ.
Proof.
  apply subst_same_var_nocommon_both.
Qed.



Lemma inter_dom_term_vars_iff : forall t S,
      set_inter var_eqdec (exp_vars t) (dom_rec S) = [] <-> sub t S = t.
Proof.
(** Only prove this if not_occurs need it *)  
Admitted.



Lemma not_occurs : forall X t1 t2, (~ set_In X (exp_vars t1)) -> sub t1 ((X,t2) :: nil) = t1.
Proof.
  intros.
  apply subst_same_var_nocommon.
  apply set_nocommon_1_3; intros.
  apply not_in_dom_lookup_rev. simpl.
  destruct (var_eqdec) eqn:Heqn.
  rewrite <- e in H0. contradiction. trivial.
Qed.
    
  
Lemma not_occurs_sexp : forall X σ s, (~ set_In X (exp_vars_s σ)) -> sub_s σ ((X,s) :: nil) = σ.
Proof.
 intros.
 apply subst_same_var_nocommon_sexp.
 apply set_nocommon_1_3; intros.
 apply not_in_dom_lookup_rev. simpl.
 destruct (var_eqdec) eqn: Heqn.
 rewrite <- e in H0. contradiction. trivial.
Qed.



Lemma look_up_sub_comp: forall S S' X, look_up X (sub_comp S S') = sub (look_up X S) S'.
(** in Substs.v, 424 *)
  Admitted.

Lemma subst_comp_expand : forall s S1 S2, sub s (sub_comp S1 S2) = sub (sub s S1) S2.
 (** in Substs.v line 431 *) 
Admitted.

Lemma subst_comp_expand_sexp : forall σ S1 S2, sub_s σ (sub_comp S1 S2) = sub_s (sub_s σ S1) S2.
Proof.
Admitted.


Lemma subst_comp_assoc: forall S1 S2 S3 t, sub t (sub_comp S1 (sub_comp S2 S3)) =
                                       sub t  (sub_comp (sub_comp S1 S2) S3).

Proof.
 Admitted.
(** in 441 substs.v *)




  
Lemma in_subcomp_second_arg : forall X S S', ~set_In X (dom_rec S) ->
                                        look_up X (sub_comp S S') = look_up X S'.
Proof.
  intros.
  rewrite look_up_sub_comp.
  rewrite not_in_dom_lookup_same; eauto.
Qed.  


Lemma set_ext_not_in_domain : forall X X0 S s , ~ set_In X (dom_rec S) ->
                                  X <> X0 ->
                                  ~ set_In X (dom_rec (sub_comp S ((X0, s) :: nil))).
Proof.
  intros.
  apply In_dom_eq_dom_flip.
  apply not_In_dom_lookup_flip.
  rewrite look_up_sub_comp.
  apply In_dom_eq_dom_flip in H.
  apply not_In_dom_lookup in H.
  rewrite H. simpl.
  destruct (var_eqdec X0 X).
  - symmetry in e. contradiction.
  - reflexivity.
Qed.  



Lemma look_up_sub_comp_not_in_first : forall S S' X, ~set_In X (dom_rec S) ->
                                                look_up X (sub_comp S S') = look_up X S'.
Proof.
  intros.
  now apply in_subcomp_second_arg.
Qed.  


Lemma s_noteq_app : forall s t, s = App s t -> False.
  intro s.
  induction s using exp_ind3; intros; try (discriminate H).
  injection H as H_l H_r. eauto.
Qed.

Lemma t_noteq_app : forall t s, t = App s t -> False.
  intro t.
  induction t using exp_ind3; intros; try (discriminate H).
  injection H as H_l H_r. eauto.
Qed.

Lemma s_noteq_lam : forall s, s = Lam s -> False.
Proof.
  intro s.
  induction s using exp_ind3; intros; try (discriminate H).
  injection H as H_'. eauto.
Qed.
  
Lemma s_noteq_inst : forall s σ, s = Inst s σ -> False.
Proof.
  intro s.
  induction s using exp_ind3; intros; try (discriminate H).
  injection H as H_l H_r. eauto.
Qed.  

Lemma σ_noteq_cons : forall σ s, σ = Cons s σ -> False.
Proof.
  intro σ.
  induction σ using sexp_ind3; intros; try (discriminate H).
  injection H as H_l H_r. eauto.
Qed.  


Lemma σ_noteq_comp : forall σ τ, σ = σ >> τ -> False.
Proof.
  intro σ.
  induction σ using sexp_ind3; intros; (try (discriminate H)).
  injection H as H_l H_r. eauto.
Qed.

Lemma τ_noteq_comp : forall τ σ, τ = σ >> τ -> False.
Proof.
  intro τ.
  induction τ using sexp_ind3; intros; (try (discriminate H)).
  injection H as H_l H_r. eauto.
Qed.



(** DOM/SUBST/EXP INFRA LEMMAS END *)


(** σmin INFRA LEMMAS START *)

Lemma not_in_dom_same_both : (forall s S, (forall X, set_In X (exp_vars s) -> σmin_equiv (look_up X S) (VarExp X)) -> σmin_equiv  s (sub s S))
                             /\
                               (forall σ S, (forall X, set_In X (exp_vars_s σ) -> σmin_equiv (look_up X S) (VarExp X)) -> σmin_equivs σ (sub_s σ S)).
  apply sigma_ind2; intros.
  -  simpl. apply σmin_equiv_refl.
  -  simpl. apply σmin_equiv_app.
     + apply H. intros.
       simpl in H1. apply H1.
       apply set_union_intro. left. assumption.
     + apply H0. intros.
       simpl in H1. apply H1.
       apply set_union_intro. right. assumption.
  -  simpl. apply σmin_equiv_lam.
     apply H. intros.
     simpl in H0. apply H0; eauto.
  -  simpl. apply σmin_equiv_asubst.
     + apply H. intros.
       simpl in H1. apply H1.
       apply set_union_intro. left. assumption. 
     + apply H0. intros.
       simpl in H1. apply H1.
       apply set_union_intro. right. assumption.
  - simpl. simpl in H.
    specialize (H X).
    apply σmin_equiv_sym.
    apply H. left. reflexivity.
  - simpl. apply σmin_equivs_refl.
  - simpl. apply σmin_equivs_refl.
  - simpl. apply σmin_equivs_cons.
    + apply H. intros.
       simpl in H1. apply H1.
       apply set_union_intro. left. assumption.
     + apply H0. intros.
       simpl in H1. apply H1.
       apply set_union_intro. right. assumption.
  - simpl. apply σmin_equivs_comp.
    + apply H. intros.
       simpl in H1. apply H1.
       apply set_union_intro. left. assumption.
     + apply H0. intros.
       simpl in H1. apply H1.
       apply set_union_intro. right. assumption.
Qed.

Lemma not_in_dom_same_exp : forall s S, (forall X, set_In X (exp_vars s) -> σmin_equiv (look_up X S) (VarExp X)) -> σmin_equiv  s (sub s S).
Proof.
  apply not_in_dom_same_both.
Qed.  


Lemma σmin_comp_prop1 : forall X S S' Sl,  ~set_In X (dom_rec S)  ->
                                      ~set_In X (dom_rec Sl) ->
                                      (sub_comp S S') ~:c Sl ->
                                      σmin_equiv (look_up X S') (VarExp X).
Proof.
  intros.
  unfold subs_equiv in H1; specialize (H1 X); simpl in H1.
  rewrite <- (not_in_dom_lookup_same Sl _); eauto.
  rewrite <- (in_subcomp_second_arg _ S S'); eauto.
Qed.
  

(** σmin INFRA LEMMAS END *)


(** MATCHING INFRA LEMMAS START *)

Lemma problem_eqn_lhvar_in : forall P s t X, set_In (equ s t) P -> set_In X (exp_vars s) -> set_In X (lhvars_Probl P).
Proof.  
  induction P; intros.
  - destruct H.
  - simpl in *.
    destruct H.
    +  rewrite H.
       apply set_union_intro1; assumption.
    + destruct a; apply set_union_intro2; eapply IHP; eauto.
Qed.

Lemma problem_eqn_lhvar_in_sexp : forall P σ τ X, set_In (equ_s σ τ) P -> set_In X (exp_vars_s σ) -> set_In X (lhvars_Probl P).
Proof.  
  induction P; intros.
  - destruct H.
  - simpl in *.
    destruct H.
    +  rewrite H.
       apply set_union_intro1; assumption.
    + destruct a; apply set_union_intro2; eapply IHP; eauto.
Qed.


Lemma problem_eqn_lhvar: forall P Y, set_inter var_eqdec (lhvars_Probl P) Y = [] -> forall s t, set_In (equ s t) P ->
                                                                                   set_inter var_eqdec (exp_vars s) Y = [].
Proof.
  intros.
  destruct (set_nocommon_1_3 (exp_vars s) Y) as [H1 H2].
  apply H1; intros.
  destruct (set_nocommon_1_3 (lhvars_Probl P) Y) as [H4 H5].
  apply (H5 H _ (problem_eqn_lhvar_in _ _ _ _ H0 H3)).
Qed.  

Lemma problem_eqn_lhvar_sexp: forall P Y, set_inter var_eqdec (lhvars_Probl P) Y = [] -> forall σ τ, set_In (equ_s σ τ) P ->
                                                                                   set_inter var_eqdec (exp_vars_s σ) Y = [].
Proof.
  intros.
  destruct (set_nocommon_1_3 (exp_vars_s σ) Y) as [H1 H2].
  apply H1; intros.
  destruct (set_nocommon_1_3 (lhvars_Probl P) Y) as [H4 H5].
  apply (H5 H _ (problem_eqn_lhvar_in_sexp _ _ _ _ H0 H3)).
Qed.  



Lemma problem_eqn_allvar_left_in : forall P s t X, set_In (equ s t) P ->
                                                set_In X (exp_vars s) ->
                                                set_In X (Problem_vars P).
Proof.
  induction P; intros.
  - destruct H.
  -simpl in *.
   destruct H.
   + rewrite H.
     apply set_union_intro1; assumption.
   + destruct a; apply set_union_intro2; apply set_union_intro2; eapply IHP; eauto.
Qed.     
     
  
Lemma problem_eqn_allvar_left : forall P Y, set_inter var_eqdec Y (Problem_vars P) = [] ->
                                    forall s t, set_In (equ s t) P ->
                                           set_inter var_eqdec (exp_vars s) Y = [].
Proof.
 intros.
  destruct (set_nocommon_1_3 (exp_vars s) Y) as [H1 H2].
  apply H1; intros.
  destruct (set_nocommon_1_3 (Problem_vars P) Y) as [H4 H5].
  destruct (set_nocommon_3_4 Y (Problem_vars P)) as [H6 H7].
  specialize (H6 H).
  apply (H5 H6 _ (problem_eqn_allvar_left_in _ _ _ _ H0 H3)).  
Qed.  



Lemma problem_eqn_allvar_right_in : forall P s t X, set_In (equ s t) P ->
                                                set_In X (exp_vars t) ->
                                                set_In X (Problem_vars P).
Proof.
  induction P; intros.
  - destruct H.
  -simpl in *.
   destruct H.
   + rewrite H.
     apply set_union_intro2; apply set_union_intro1; assumption.
   + destruct a; apply set_union_intro2; apply set_union_intro2; eapply IHP; eauto.
Qed.     

Lemma problem_eqn_allvar_right_in_sexp : forall P σ τ X, set_In (equ_s σ τ) P ->
                                                set_In X (exp_vars_s τ) ->
                                                set_In X (Problem_vars P).
Proof.
  induction P; intros.
  - destruct H.
  -simpl in *.
   destruct H.
   + rewrite H.
     apply set_union_intro2; apply set_union_intro1; assumption.
   + destruct a; apply set_union_intro2; apply set_union_intro2; eapply IHP; eauto.
Qed.     



Lemma problem_eqn_allvar_right : forall P Y, set_inter var_eqdec Y (Problem_vars P) = [] ->
                                    forall s t, set_In (equ s t) P ->
                                           set_inter var_eqdec (exp_vars t) Y = [].
intros.
  destruct (set_nocommon_1_3 (exp_vars t) Y) as [H1 H2].
  apply H1; intros.
  destruct (set_nocommon_1_3 (Problem_vars P) Y) as [H4 H5].
  destruct (set_nocommon_3_4 Y (Problem_vars P)) as [H6 H7].
  specialize (H6 H).
  apply (H5 H6 _ (problem_eqn_allvar_right_in _ _ _ _ H0 H3)).  
Qed.  


Lemma problem_eqn_allvar_right_sexp : forall P Y, set_inter var_eqdec Y (Problem_vars P) = [] ->
                                    forall σ τ, set_In (equ_s σ τ) P ->
                                           set_inter var_eqdec (exp_vars_s τ) Y = [].
intros.
  destruct (set_nocommon_1_3 (exp_vars_s τ) Y) as [H1 H2].
  apply H1; intros.
  destruct (set_nocommon_1_3 (Problem_vars P) Y) as [H4 H5].
  destruct (set_nocommon_3_4 Y (Problem_vars P)) as [H6 H7].
  specialize (H6 H).
  apply (H5 H6 _ (problem_eqn_allvar_right_in_sexp _ _ _ _ H0 H3)).  
Qed.  

  
  


Lemma not_in_prob_lhvar_not_in_eq_left : forall X P, ~set_In X (lhvars_Probl P) ->
                                             forall s t, set_In (equ s t) P ->
                                                    ~set_In X (exp_vars s).
Proof.
  intros.
  unfold not in *.
  intros.
  apply H. eapply problem_eqn_lhvar_in; eauto.
Qed.
    
(** MATCHING INFRA LEMMAS END *)


(** INFRASTRUCTURE LEMMAS END *)



(** Statement of Preservation *)
Lemma match_sol_preservation : forall Sl T T',

      valid_tuple T ->

      set_inter var_eqdec (lhvars_Probl (snd T)) (dom_rec Sl) = [] ->

      smatch T T' ->

      match_sol Sl T' -> match_sol Sl T.
Proof.
  intros.
  induction H1.
  - unfold match_sol in *.
    simpl in *.
    destruct H2 as [H21 [H22 [H23 H24]]].
    split.
    + intros.
      case (Equation_eqdec (equ s0 t) (equ s s)); intros.
      * inversion e; subst.
        pose proof (problem_eqn_lhvar _ _  H0 _ _ H1) as HsSl.
        pose proof (subst_same_var_nocommon _ _ HsSl) as eqsSl.
        rewrite eqsSl.
        constructor.
      * apply H21. apply (set_remove_3 Equation_eqdec P H2 n).
    + split.
     *  intros.
        case (Equation_eqdec (equ_s σ τ) (equ s s)); intros.
        ** inversion e; subst.
        ** apply H22. apply (set_remove_3 Equation_eqdec); eauto. 
       
     * split; assumption.

  (* refl2 *)
   - unfold match_sol in *.
    simpl in *.
    destruct H2 as [H21 [H22 [H23 H24]]].
    split.
    + intros.
      case (Equation_eqdec (equ s t) (equ_s σ σ)); intros.
      * inversion e; subst.
      * apply H21. apply (set_remove_3 Equation_eqdec P H2 n).
    + split.
     *  intros.
        case (Equation_eqdec (equ_s σ0 τ) (equ_s σ σ)); intros.
        ** inversion e; subst.
           pose proof (problem_eqn_lhvar_sexp _ _  H0 _ _ H1) as HsSl.
           pose proof (subst_same_var_nocommon_sexp _ _ HsSl) as eqsSl.
           rewrite eqsSl.
           constructor.
        ** apply H22. apply (set_remove_3 Equation_eqdec); eauto. 
       
     * split; assumption.

       
  - unfold match_sol in *.
    simpl in *.
    destruct H2 as [H21 [H22 [H23 H24]]].
    repeat split.
    + intros.
      case (Equation_eqdec (equ s0 t0) (equ (App s t) (App s' t'))); intros.
      * inversion e; subst.
        simpl.
        apply σmin_equiv_app; apply H21.
        **  apply (set_remove_3 Equation_eqdec).
            apply set_add_intro1.
            now apply set_add_intro2.
            unfold not. intro. inversion H3; subst.
            eapply s_noteq_app. exact H5.            
        ** apply (set_remove_3 Equation_eqdec).
            now apply set_add_intro2.
            unfold not. intro. inversion H3; subst.
            eapply t_noteq_app. exact H5.            
      * apply H21.
        apply (set_remove_3 Equation_eqdec); eauto.
        apply set_add_intro1.
        apply set_add_intro1.
        apply H2.
    + intros.
      case (Equation_eqdec (equ_s σ τ) (equ (App s t) (App s' t'))); intros.
      inversion e; subst.
      apply H22.
      apply (set_remove_3 Equation_eqdec); eauto.
      now repeat apply set_add_intro1.
    + assumption.  
    + assumption.   
  (* Lam *)    
  - unfold match_sol in *.
    simpl in *.
    destruct H2 as [H21 [H22 [H23 H24]]].
    repeat split.
    + intros.
      case (Equation_eqdec (equ s0 t) (equ (Lam s) (Lam s'))); intros.
      * inversion e; subst.
        simpl. 
        apply σmin_equiv_lam; apply H21.
        apply (set_remove_3 Equation_eqdec).  
        now apply set_add_intro2.
        unfold not. intro. inversion H3; subst.
        eapply s_noteq_lam. exact H5.              
      * apply H21.
        apply (set_remove_3 Equation_eqdec); eauto.
        now apply set_add_intro1.
    +  intros.
       case (Equation_eqdec (equ_s σ τ) (equ (Lam s) (Lam s'))); intros.
       inversion e; subst.
       apply H22.
       apply (set_remove_3 Equation_eqdec); eauto.
       now repeat apply set_add_intro1.
    + assumption.
    + assumption.
  - (* inst *) 
    unfold match_sol in *.
    simpl in *.
    destruct H2 as [H21 [H22 [H23 H24]]].
    repeat split.
    + intros.
      case (Equation_eqdec (equ s0 t) (equ (s [σ]) (s' [σ']))); intros.
      * inversion e; subst.
        simpl. 
        apply σmin_equiv_asubst. 
        **  apply H21. apply (set_remove_3 Equation_eqdec).
            apply set_add_intro1.
            now apply set_add_intro2.
            unfold not. intro. inversion H3; subst.
            eapply s_noteq_inst. exact H5.            
        ** apply H22.
           apply (set_remove_3 Equation_eqdec).
            now apply set_add_intro2.
            unfold not. intro. inversion H3; subst.            
      * apply H21.
        apply (set_remove_3 Equation_eqdec); eauto.
        apply set_add_intro1.
        apply set_add_intro1.
        apply H2.
    + intros.
      case (Equation_eqdec (equ_s σ0 τ) (equ (s [σ]) (s' [σ']))); intros.
      * inversion e; subst.
      * apply H22.
        apply (set_remove_3 Equation_eqdec); eauto.
        now repeat apply set_add_intro1.
    +  assumption.
    +  assumption.

  - unfold match_sol in *.
    simpl in *.
    destruct H2 as [H21 [H22 [H23 H24]]].
    repeat split; intros.
    + case (Equation_eqdec (equ s0 t) (equ_s (s .: σ) (s' .: σ'))); intros.
      inversion e; subst.
      apply H21.
      apply (set_remove_3 Equation_eqdec); eauto.
      now repeat apply set_add_intro1.
    +  case (Equation_eqdec (equ_s σ0 τ) (equ_s (s .: σ) (s' .: σ'))); intros.
       * inversion e; subst; simpl.
         apply σmin_equivs_cons.
         ** apply H21. apply (set_remove_3 Equation_eqdec).
            apply set_add_intro1.
            now apply set_add_intro2.
            unfold not. intros.
            inversion H3; subst.
         ** apply H22. apply (set_remove_3 Equation_eqdec).
            now apply set_add_intro2.
            unfold not. intros.
            inversion H3; subst.
            eapply σ_noteq_cons. apply H5.
       * apply H22.
         apply (set_remove_3 Equation_eqdec).
         now repeat apply set_add_intro1. apply n.
    + assumption.
    + assumption.  
  - unfold match_sol in *.
    simpl in *.
    destruct H2 as [H21 [H22 [H23 H24]]].
    repeat split; intros.  
    +  case (Equation_eqdec (equ s t) (equ_s (σ >> τ) ( σ'>> τ'))); intros.
       * inversion e; subst.
       *  apply H21.
           apply (set_remove_3 Equation_eqdec); eauto.
           now repeat apply set_add_intro1.
    + case (Equation_eqdec (equ_s σ0 τ0) (equ_s (σ >> τ) (σ' >> τ'))); intros.
     *  inversion e; subst.
        simpl.
        apply σmin_equivs_comp; apply H22.
        **  apply (set_remove_3 Equation_eqdec).
            apply set_add_intro1.
            now apply set_add_intro2.
            unfold not. intro. inversion H3; subst.
            eapply σ_noteq_comp. exact H5.            
        ** apply (set_remove_3 Equation_eqdec).
            now apply set_add_intro2.
            unfold not. intro. inversion H3; subst.
            eapply τ_noteq_comp. exact H5.            
      * apply H22.
        apply (set_remove_3 Equation_eqdec); eauto.
        apply set_add_intro1.
        apply set_add_intro1.
        apply H2.
    + assumption.  
    + assumption.        
  - unfold match_sol in *.
    simpl in *.
    destruct H2 as [H21 [H22 [H23 H24]]].
    repeat split; intros.
    + case (Equation_eqdec (equ s0 t) (equ (Lam s [Zero .: σ >> ↑]) s' [σ'])); intros.
      * inversion e; subst.
        apply σmin_equiv_trans with (t := (Lam s)[σ]).
        repeat constructor.
        apply H21. apply (set_remove_3 Equation_eqdec).
        now apply (set_add_intro2). 
        unfold not. intro. inversion H3.
      * apply H21.
        apply (set_remove_3 Equation_eqdec).
        now apply (set_add_intro1). assumption.
    + case (Equation_eqdec (equ_s σ0 τ) (equ (Lam s [Zero .: σ >> ↑]) s' [σ'])); intros.
      * inversion e; subst.
      * apply H22.
        apply (set_remove_3 Equation_eqdec).
        now apply (set_add_intro1). assumption.
    + assumption.
    + assumption.
  -  unfold match_sol in *.
     simpl in *.
     destruct H2 as [H21 [H22 [H23 H24]]].
     repeat split; intros.
     + case (Equation_eqdec (equ s t) (equ_s (σ >> τ >> ρ) (σ' >> τ'))); intros.
       * inversion e; subst.
       * apply H21.
         apply (set_remove_3 Equation_eqdec).
         now apply (set_add_intro1). assumption.
     +  case (Equation_eqdec (equ_s σ0 τ0) (equ_s (σ >> τ >> ρ) (σ' >> τ'))); intros.
        * inversion e; subst.
          apply σmin_equivs_trans with (τ := (σ >> τ) >> ρ).
          repeat constructor.
          apply H22.
          apply (set_remove_3 Equation_eqdec).
          now apply (set_add_intro2).
          unfold not. intro. inversion H3.
          eapply (τ_noteq_comp). apply H6.
        *  apply H22.
           apply (set_remove_3 Equation_eqdec).
           now apply (set_add_intro1). assumption.
     + assumption.
     + assumption.
  -  unfold match_sol in *.
     simpl in *.
     destruct H2 as [H21 [H22 [H23 H24]]].
     repeat split; intros.
     + case (Equation_eqdec (equ s0 t) (equ_s (s[τ] .: σ>>τ) (σ' >> τ'))); intros.
       * inversion e; subst.
       * apply H21.
         apply (set_remove_3 Equation_eqdec).
         now apply (set_add_intro1). assumption.
     + case (Equation_eqdec (equ_s σ0 τ0) (equ_s (s[τ] .: σ >> τ) (σ' >> τ'))); intros.
       *  inversion e; subst.
          apply σmin_equivs_trans with (τ := (s .: σ) >> τ).
          repeat constructor.
          apply H22.
          apply (set_remove_3 Equation_eqdec).
          now apply (set_add_intro2).
          unfold not. intro. inversion H3.
       * apply H22.
         apply (set_remove_3 Equation_eqdec).
         now apply (set_add_intro1). assumption.
     + assumption.
     + assumption.
  - unfold match_sol in *.
    simpl in *.
    destruct H2 as [H21 [H22 [H23 H24]]].
    repeat split; intros.
    + case (Equation_eqdec (equ s0 t) (equ s[σ>>τ] s'[ρ])); intros.
      *  inversion e; subst.
         apply σmin_equiv_trans with (t := (s[σ])[τ]).
         constructor. constructor.
         apply H21.
         apply (set_remove_3 Equation_eqdec).
         now apply (set_add_intro2).
         unfold not. intro. inversion H3.
         eapply (τ_noteq_comp). apply H6.
      * apply H21.
        apply (set_remove_3 Equation_eqdec).
        now apply (set_add_intro1). assumption.
    + case (Equation_eqdec (equ_s σ0 τ0) (equ s[σ >> τ] s'[ρ])); intros.
      * inversion e; subst.
      * apply H22.
        apply (set_remove_3 Equation_eqdec).
        now apply (set_add_intro1). assumption.
    + assumption.
    + assumption.
       
  - (* This is the hardest case where all the action happens   *)
    
     unfold match_sol in *.
     simpl in *.
     destruct H2 as [H21 [H22 [H23 H24]]].
     rewrite H4 in H23.
     repeat split.
     + intros.
       case (Equation_eqdec (equ s0 t) (equ s (VarExp X))); intros.
       * inversion e; subst.
         simpl.
         unfold valid_tuple in H; simpl in H; destruct H as [H_1 H_2].
         destruct H23 as [S''].
         unfold subs_equiv in H; simpl in H.
         apply σmin_equiv_trans with (t := sub s S'').
         **  apply not_in_dom_same_exp.
             intros.
             eapply σmin_comp_prop1.
             3: unfold subs_equiv; apply H.
             case (var_eqdec X X0); intros; subst.
             pose proof (not_in_prob_lhvar_not_in_eq_left _ _ H1 _ _ H3); contradiction.
             apply set_ext_not_in_domain.
             eapply not_in_if_inter_empty.
             apply H4. eapply problem_eqn_allvar_left. apply H_1. apply H3.
             unfold not in n. unfold not. intros. symmetry in H5. contradiction.
             eapply not_in_if_inter_empty; eauto.
             eapply problem_eqn_lhvar with (P := P); eauto.
             
         ** specialize (H X).
            rewrite look_up_sub_comp in H.
  
            rewrite (look_up_sub_comp_not_in_first) in H. 
            simpl in H.
            destruct (var_eqdec X X) in H.
            assumption.
            contradiction.
            eapply not_in_if_inter_empty.
            2: pose proof (comm_empty_inter _ _ H_1) as H_1'; exact H_1'.
            eapply  problem_eqn_allvar_right_in; eauto.
            simpl. left; reflexivity. 
            
       *  unfold valid_tuple in H.
          simpl in *.
          destruct H as [H_1 H_2].
          destruct H23 as [S''].
          case (set_In_dec var_eqdec X (exp_vars t)) as [H5 | H5]; intros.
          ** apply σmin_equiv_trans with (t := (sub t  (sub_comp ((X,s) :: nil) Sl ))).
             *** apply σmin_equiv_trans with (t := (sub (sub t ((X,s)::nil)) Sl)).
                 **** apply H21.
                      apply push_subst_problem.
                      apply (set_remove_3 Equation_eqdec P H2 n).
                 **** rewrite subst_comp_expand.
                      apply σmin_equiv_refl.
             *** apply subst_sub_σmin_gen_left.
                 unfold subs_equiv; intros.
                 case (var_eqdec X X0); intros; subst.
                 **** simpl. destruct (var_eqdec X0 X0); subst.
                      ***** pose proof (problem_eqn_lhvar _ _ H0 _ _ H2).
                            pose proof (problem_eqn_lhvar _ _ H0 _ _ H3).
                            rewrite (subst_same_var_nocommon _ _ H6).
                            unfold subs_equiv in H; simpl in H.
                            apply σmin_equiv_trans with (t := sub s S'').
                            ******  apply not_in_dom_same_exp.
                                    intros.
                                    eapply σmin_comp_prop1.
                                    3: unfold subs_equiv; apply H.
                                    case (var_eqdec X X0); intros; subst.
                                    pose proof (not_in_prob_lhvar_not_in_eq_left _ _ H1 _ _ H3).
                                    contradiction.
                                    pose proof (problem_eqn_allvar_left _ _ H_1 _ _ H3).
                                    pose proof (not_in_if_inter_empty _ _ _ H7 H8).
                                    apply (set_ext_not_in_domain _ _ _ _ H9 n0).
                                    eapply not_in_if_inter_empty; eauto.                               
                            ******  specialize (H X0).
                                    rewrite look_up_sub_comp in H.
                                    rewrite (look_up_sub_comp_not_in_first) in H.
                                    simpl in H.
                                    destruct (var_eqdec X0 X0) in H.
                                    assumption.
                                    contradiction.
                                    eapply not_in_if_inter_empty.
                                    apply H5.
                                    eapply problem_eqn_allvar_right; eauto.             
                      ***** destruct n0; reflexivity.
                 **** simpl. destruct (var_eqdec X X0).
                      ***** contradiction.
                      ***** apply σmin_equiv_refl.
          ** apply H21. 
             apply (set_remove_3 Equation_eqdec) with (b:= equ s (VarExp X))  in H2.
             apply (push_subst_problem) with (S := (X,s)::nil) in H2. 2: assumption.
             simpl in H2.
             rewrite <- not_occurs with (t1 := t) (t2:= s) (X:=X).
             apply H2.
             apply H5.
     (* RUNNING SUB CASE *)
     + intros.
       case (Equation_eqdec (equ_s σ τ) (equ s (VarExp X))); intros.
       * inversion e; subst.              
       *  unfold valid_tuple in H.
          simpl in *.
          destruct H as [H_1 H_2].
          destruct H23 as [S''].
          case (set_In_dec var_eqdec X (exp_vars_s τ)) as [H5 | H5]; intros.
          ** apply σmin_equivs_trans with (τ := (sub_s τ  (sub_comp ((X,s) :: nil) Sl ))).
             *** apply σmin_equivs_trans with (τ := (sub_s (sub_s τ ((X,s)::nil)) Sl)).
                 **** apply H22.
                      apply push_subst_problem_sexp.
                      apply (set_remove_3 Equation_eqdec P H2 n).
                 **** rewrite subst_comp_expand_sexp.
                      apply σmin_equivs_refl.
             *** apply subst_sub_σmin_gen_right.
                 unfold subs_equiv; intros.
                 case (var_eqdec X X0); intros; subst.
                 **** simpl. destruct (var_eqdec X0 X0); subst.
                      ***** pose proof (problem_eqn_lhvar _ _ H0 _ _ H3).
                            pose proof (problem_eqn_lhvar _ _ H0 _ _ H3).
                            rewrite (subst_same_var_nocommon _ _ H6).
                            unfold subs_equiv in H; simpl in H.
                            apply σmin_equiv_trans with (t := sub s S'').
                            ******  apply not_in_dom_same_exp.
                                    intros.
                                    eapply σmin_comp_prop1.
                                    3: unfold subs_equiv; apply H.
                                    case (var_eqdec X X0); intros; subst.
                                    pose proof (not_in_prob_lhvar_not_in_eq_left _ _ H1 _ _ H3).
                                    contradiction.
                                    pose proof (problem_eqn_allvar_left _ _ H_1 _ _ H3).
                                    pose proof (not_in_if_inter_empty _ _ _ H7 H8).
                                    apply (set_ext_not_in_domain _ _ _ _ H9 n0).
                                    eapply not_in_if_inter_empty; eauto.                               
                            ******  specialize (H X0).
                                    rewrite look_up_sub_comp in H.
                                    rewrite (look_up_sub_comp_not_in_first) in H.
                                    simpl in H.
                                    destruct (var_eqdec X0 X0) in H.
                                    assumption.
                                    contradiction.
                                    eapply not_in_if_inter_empty.
                                    apply H5.
                                    eapply problem_eqn_allvar_right_sexp; eauto.             
                      ***** destruct n0; reflexivity.
                 **** simpl. destruct (var_eqdec X X0).
                      ***** contradiction.
                      ***** apply σmin_equiv_refl.
          ** apply H22. 
             apply (set_remove_3 Equation_eqdec) with (b:= equ s (VarExp X))  in H2.
             apply (push_subst_problem_sexp) with (S := (X,s)::nil) in H2. 2: assumption.
             simpl in H2.
             rewrite <- not_occurs_sexp with (σ := τ) (s:= s) (X:=X).
             apply H2.
             apply H5.
     
             
       
     + eauto.
       destruct H23 as [S''].
       unfold subs_equiv in *.
       exists (sub_comp ((X,s) :: nil) S'').
       intros.
       specialize (H2 X0). now rewrite <- subst_comp_assoc in H2.
    + assumption.
Qed.
