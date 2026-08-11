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
    | (equ s t )::P0 => (equ s (sub t S))::(subs_Problem P0 S)
    | (equ_s σ τ )::P0 => (equ_s σ (sub_s τ S))::(subs_Problem P0 S) 
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
| smatch_refl : forall S P s, set_In (equ s s) P -> smatch (S,P) (S,P\(equ s s))
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
                                 smatch (S,P) (S, P |+ (equ (Lam s)[σ] s'[σ]) \ (equ (Lam (s[Zero .: (σ >> ↑)])) (s'[σ'])))

| smatch_Assoc : forall S P σ τ ρ σ' τ', set_In (equ_s (σ >> τ >> ρ)  (σ' >> τ')) P  ->
                                    smatch (S,P) (S, P |+ (equ_s ((σ >> τ) >> ρ) (σ' >> τ')) \ (equ_s (σ >> τ >> ρ)  (σ' >> τ')))
| smatch_Conslaw : forall S P s σ τ σ' τ', set_In (equ_s (s[σ] .: (σ >> τ)) (σ' >> τ')) P ->
                                      smatch (S,P) (S, P |+ (equ_s ((s .: σ) >> τ) (σ' >> τ')) \ (equ_s (s[σ] .: (σ >> τ)) (σ' >> τ') ))
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
  ( exists S'', (sub_comp S S'') ~:c S' ) /\
  set_inter var_eqdec (lhvars_Probl P) (dom_rec S') = []. 


Lemma problem_lhvars_exp_empty (s: exp) (P: Problem) (S: Subst):
  forall t, set_inter var_eqdec (lhvars_Probl P) (dom_rec S) = [] -> set_In (equ s t) P -> set_inter var_eqdec (exp_vars s) (dom_rec S) = [].
Admitted.

Lemma exp_sub_dom_inter_empty (s: exp) (S: Subst) : set_inter var_eqdec (exp_vars s) (dom_rec S) = [] -> sub s S = s.
Admitted.

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
    specialize (H X).
    (*case (var_eqdec X0 X); intros.
    + assumption.
    + constructor. *) admit.
  - constructor.
  - constructor.
  - apply σmin_equivs_cons; eauto.
  - apply σmin_equivs_comp; eauto.
Admitted. 


Lemma subst_sub_σmin_gen_left : (forall s S S', S ~:c S'  -> σmin_equiv (sub s S)
                                                         (sub s S')).
Admitted.  

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

(** set_In_dec :  set_In X + ~set_In X *)

(*
Lemma eq_sub_dom_eq: forall S S', S ~
*)



(** Imprtant property of σmin_equiv that may imply preservation may not work in a bigger fragment *)

Lemma var_σmin_only_to_var : forall X s, σmin_equiv (VarExp X) s -> s = VarExp X.
  Admitted.

Lemma var_in_exp : forall X s, set_In X (exp_vars s) \/ ~set_In X (exp_vars s).
  Admitted.

Lemma not_in_dom_same : forall s S, (forall X, set_In X (exp_vars s) -> σmin_equiv (look_up X S) (VarExp X)) -> σmin_equiv  s (sub s S).
   Admitted.

Lemma look_up_sub_comp: forall S S' X, look_up X (sub_comp S S') = sub (look_up X S) S'.
  Admitted.

Lemma sub_subst_interaction : forall X s t S, sub s (sub_comp ((X,t) :: nil) S) = sub (sub s ((X,t)::nil)) S.
  Admitted.

Lemma push_subst_problem : forall s t S P, set_In (equ s t) P -> set_In (equ s (sub t S)) (P |^^ S).
  Admitted.

Lemma problem_eqn_lhvar: forall P Y, set_inter var_eqdec (lhvars_Probl P) Y = [] -> forall s t, set_In (equ s t) P ->
                                                                                   set_inter var_eqdec (exp_vars s) Y = [].
Proof.
  intros.
  induction P.
  - simpl. destruct H0.
  - admit. 
Admitted.

Lemma problem_eqn_allvar_left : forall P Y, set_inter var_eqdec Y (Problem_vars P) = [] ->
                                    forall s t, set_In (equ s t) P ->
                                           set_inter var_eqdec (exp_vars s) Y = [].
Admitted.

Lemma not_dom_look_same : forall X S, ~ set_In X (dom_rec S) -> look_up X S = (VarExp X). 
 Admitted.


Lemma not_in_if_inter_empty : forall X S S',   set_In X S ->
                                          set_inter var_eqdec S S' = [] ->
                                          ~ set_In X S'.
 Admitted.

Lemma subst_same_var_nocommon : forall s S, set_inter var_eqdec (exp_vars s) (dom_rec S) = [] ->
                                       sub s S = s.
 Admitted.  

Lemma σmin_comp_prop1 : forall X S S' Sl,  ~set_In X (dom_rec S)  ->
                                      ~set_In X (dom_rec Sl) ->
                                      (sub_comp S S') ~:c Sl ->
                                      σmin_equiv (look_up X S') (VarExp X).
  Admitted.

Lemma not_in_problem_not_in_eq_left : forall X P, ~set_In X (Problem_vars P) ->
                                             forall s t, set_In (equ s t) P ->
                                                    ~set_In X (exp_vars s).
Admitted.

 
  
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
    destruct H2 as [H21 [H22 H23]].
    split.
    + intros.
      case (Equation_eqdec (equ s0 t) (equ s s)); intros.
      * inversion e; subst.
        pose proof (problem_lhvars_exp_empty _ _ _ _ H0 H1) as HsSl.
        pose proof (exp_sub_dom_inter_empty _ _ HsSl) as eqsSl.
        rewrite eqsSl.
        constructor.
      * apply H21. apply (set_remove_3 Equation_eqdec P H2 n).         
    + split; assumption.
  - unfold match_sol in *.
    simpl in *.
    destruct H2 as [H21 [H22 H23]].
    split.
    + intros.
      case (Equation_eqdec (equ s0 t0) (equ (App s t) (App s' t'))); intros.
      * inversion e; subst.
        simpl. 
        apply σmin_equiv_app; apply H21.
        **  admit.
        **  admit.
      * apply H21. admit.         
    + split; assumption.
  - admit.
  - admit.
  - admit.
  - admit.
  - unfold match_sol in *.
    simpl in *.
    destruct H2 as [H21 [H22 H23]].
    split.
    + intros.
      case (Equation_eqdec (equ s0 t) (equ (Lam s [Zero .: σ >> ↑]) s' [σ'])); intros.
      * inversion e; subst.
        simpl.
        assert (σmin_equiv (Lam s)[σ] (sub (s'[σ']) Sl)).
        apply H21. admit.
        admit. (* can be proven by trans/symm *)
      * apply H21. admit.    
    + split; assumption.
  -  admit.
  -  admit.
  -  admit.
  -  unfold match_sol in *.
     simpl in *.
     destruct H2 as [H21 [H22 H23]].
     rewrite H4 in H22.
     split.
     + intros.
       case (Equation_eqdec (equ s0 t) (equ s (VarExp X))); intros.
       * inversion e; subst.
         simpl.
         unfold valid_tuple in H; simpl in H; destruct H as [H_1 H_2].
         destruct H22 as [S''].
         assert ((look_up X (sub_comp (sub_comp S ((X,s) :: nil)) S'' )) = s) as HSS''s.
         {
           (* 
              1. dom_rec S /\ exp s = ϕ (from H_1 and H2) 
              2. dom_rec Sl /\ exp s = ϕ (from H0 and H2)
              3. From 1 and 2, it is clear that dom_rec S'' /\ exp s = ϕ 
              4. From 4, we have ((S ∘ [(X,s)]) ∘ S'')@X = s because S'' can't modify s  
           *) admit.
         }
         admit. 
       *  unfold valid_tuple in H.
          simpl in *.
          destruct H as [H_1 H_2].
          destruct H22 as [S''].
          case (var_in_exp X t); intros.
          ** apply σmin_equiv_trans with (t := (sub t  (sub_comp ((X,s) :: nil) Sl ))).
             *** apply σmin_equiv_trans with (t := (sub (sub t ((X,s)::nil)) Sl)).
                 **** apply H21.
                      apply push_subst_problem.
                      apply (set_remove_3 Equation_eqdec P H2 n).
                 **** rewrite sub_subst_interaction.
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
                            ******  apply not_in_dom_same.
                                    intros.
                                    eapply σmin_comp_prop1.
                                    3: unfold subs_equiv; apply H.
                                    case (var_eqdec X X0); intros; subst.
                                    pose proof (
                                                                           
                                    pose proof (σmin_comp_prop1 _ _ _ _                         
                            ******  specialize (H X0).
                                    rewrite look_up_sub_comp in H.
                            
                      assert ( (forall X, set_In X (exp_vars s) ->
                                σmin_equiv (look_up X (sub_comp (sub_comp S ((X,s):: nil)) S''))
                                           (VarExp X))) as temp_4.
             
                      {
                           admit.

                      }

                       assert ( (forall X, set_In X (exp_vars s) ->
                                      σmin_equiv (look_up X S'') (VarExp X))) as temp_5.
                      {
                        admit.
                      }
                           
                      specialize (H X0).
                      rewrite look_up_sub_comp in H.
                        
                      assert (look_up X0 (sub_comp S ((X0,s) :: nil)) = s) as temp_6. {admit.}
                      rewrite temp_6 in H.
                      admit.
                      
                      ***** destruct n0; reflexivity.
                 **** simpl. destruct (var_eqdec X X0).
                      ***** admit.
                      ***** apply σmin_equiv_refl.








           (*
            assert (forall X, set_In X (exp_vars s) -> look_up X S = s) as temp_1.
             { admit.

             }
             assert ( (forall X, set_In X (exp_vars s)) ->
                      σmin_equiv (look_up X (sub_comp (sub_comp S ((X,s):: nil)) S'')) (VarExp X)                       ) as temp_2.
             
             {
               admit.

             }



             assert (set_inter var_eqdec (exp_vars s) (dom_rec S'') = []).
             { unfold subs_equiv in H.
               remember (exp_vars s) as svars.

               (* 
                  
                  - Any Y which is not in svars is not present in the domain of Sl by H.
                  - By H again, I don't have Y∈svars in domain of S.
                  - Okay, now let's say we have a Y which is not in svars in present in 
                    domain of S''. This implies S''@Y ≠ Y. But, since Sl@Y = Y this 
                    result in a contradiction  


                *)
               assert (

               admit.


             } *)
          ** assert ( σmin_equiv s (look_up X Sl)) as H_sSlX.
             {
               

               
               unfold subs_equiv in H6               
               specialize (H6 X). simpl in H6.


             }

             assert ( (sub_comp ((X,s) :: nil) Sl) ~:c Sl).
             {
               unfold subs_equiv.
               intros.
               case (var_eqdec X X0); intros; subst.
               *** simpl. 
                   destruct (var_eqdec X0 X0).
                   **** assert (sub s Sl = s).
                        {admit.}
                        rewrite H4.
                        admit. (* because of symmetry *)
                   **** destruct n0; reflexivity.
               *** simpl.
                   destruct (var_eqdec X X0); intros.
                   **** admit. (* because contradiction is there *)
                   **** admit. (* because of reflexivity *)
            }            

          (* Now it's simple use the lemma of equal subsitutions *)
            admit.


            
          ** admit.
            
          (*
            1. Two cases X∈t and X ~∈ t:
            1.1) t does have X
            1.2) t doesn't have X can be shown from H21

            proof 1.1: I can show that "sub_In (equ s0 (sub t [(X,s)])) (P \ (s, X))|^^ [X,s]". This will yield s0 =σ (sub (sub t [(X,s)]) Sl). Since s doesn't share any variable with domain of Sl, (sub (sub t [X,s]) Sl) = sub t ([X,s] ∘ Sl).
             
          Now we need to show that, sub t ([X,s] ∘ Sl) =σ sub t Sl from the assumption "look_up X Sl =σ s 
                

          *)
       + admit.
Admitted.
