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
                | Comp (σ τ: sexp) : sexp
                | VarSExp (Y: Var) : sexp.
Set Elimination Schemes.
Scheme exp_ind := Induction for exp Sort Type
with  sexp_ind := Induction for sexp Sort Type.
Combined Scheme sigma_ind from exp_ind, sexp_ind.

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
| σmin_μequivs_comp (σ1 σ2 τ1 τ2 : sexp) :  σmin_equivs σ1 σ2 -> σmin_equivs τ1 τ2 ->  σmin_equivs (σ1 >> τ1) (σ2 >> τ2).
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

Inductive Mapping : Set :=
| exp_map : Var -> exp -> Mapping
| sexp_map : Var -> sexp -> Mapping.

Definition Subst := set Mapping.
Definition Problem := set Equation.   
Definition Tuple := (Subst * Problem).


(** Definition of instantiation of a term/substitution with a Subst *)

Fixpoint look_up_exp (X: Var) (S: Subst) {struct S} : exp :=
 match S with
 | [] => VarExp X
 | mp :: S0 => match mp with
             | exp_map Y t => if var_eqdec Y X then t else (look_up_exp X S0)
             | _ => look_up_exp X S0
             end
 end.

Fixpoint look_up_sexp (X: Var) (S: Subst) {struct S} : sexp :=
 match S with
 | [] => VarSExp X
 | mp :: S0 => match mp with
             | sexp_map Y σ => if var_eqdec Y X then σ else (look_up_sexp X S0)
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
  -
(*    
Defined.
*)
Admitted.
    
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
                   (F: Mapping -> Subst -> Subst -> Subst) : Subst :=
 match S1 with 
    | []          =>  S2
    | mp::S0  =>  F mp S2 (alist_rec S0 S2 F)
 end.

Definition F_rec (S1: Subst) (mp : Mapping) (S2 S3: Subst) :=
  match mp with
  | exp_map X t => (exp_map X (sub t S1)) :: S3
  | sexp_map Y σ => (sexp_map Y (sub_s σ S1)) ::  S3
  end.



Definition sub_comp (S1 S2: Subst) := alist_rec S1 S2 (F_rec S2). 


(** subs_Problem applies a subtitution to a generic problem *)

Fixpoint subs_Problem (P : Problem) (S : Subst) : Problem :=
  match P with
    | [] => []
    | (equ s t )::P0 => (equ (sub s S) (sub t S))::(subs_Problem P0 S)
    | (equ_s σ τ )::P0 => (equ_s (sub_s σ S) (sub_s τ S))::(subs_Problem P0 S) 
  end.


Lemma varboth_eqdec : forall (v1 v2: (Var + Var)), {v1=v2} + {v1 <> v2}.
Admitted.


Fixpoint exp_vars (s : exp) {struct s} : set (Var + Var) := 
match s with
 | Zero     => empty_set _
 | App s t  => set_union varboth_eqdec (exp_vars s) (exp_vars t)
 | Lam s => exp_vars s                      
 | Inst s σ => set_union varboth_eqdec (exp_vars s) (exp_vars_s σ)
 | VarExp X => set_add varboth_eqdec (inl X) (empty_set _)
end
with exp_vars_s (σ: sexp) {struct σ} : set (Var + Var) :=
 match σ with
 | I  => empty_set _
 | Shift => empty_set _
 | Comp σ τ => set_union varboth_eqdec (exp_vars_s σ) (exp_vars_s τ)
 | Cons s σ => set_union varboth_eqdec (exp_vars s) (exp_vars_s σ)
 | VarSExp X => set_add varboth_eqdec (inr X) (empty_set _)
end.


Fixpoint lhvars_Probl (P : Problem) :=
  match P with
  | [] => []
  | (equ s t) :: P0 => set_union varboth_eqdec (exp_vars s) (lhvars_Probl P0)
  | (equ_s σ τ) :: P0 => set_union varboth_eqdec (exp_vars_s σ) (lhvars_Probl P0)                       
  end.  


Fixpoint Problem_vars (P : Problem) : set (Var + Var) :=
  match P with
    | [] => []
    | (equ s t)::P0 => set_union varboth_eqdec (exp_vars s)
                   (set_union varboth_eqdec (exp_vars t) (Problem_vars P0))
    | (equ_s σ τ)::P0 => set_union varboth_eqdec (exp_vars_s σ)
                       (set_union varboth_eqdec (exp_vars_s τ) (Problem_vars P0))               
  end.






(** subst_dom_vars extracts the variables that contains the substitution domain *)

Fixpoint subst_dom_vars (S : Subst) : set (Var + Var) :=
  match S with
    | [] => []   
    | mp::S0 => match mp with
              | exp_map X t => set_add varboth_eqdec (inl X) (subst_dom_vars S0)
              | sexp_map Y σ => set_add varboth_eqdec (inr Y) (subst_dom_vars S0)
              end                 
   end.



(** dom_rec_aux is a auxiliar function to build the correct domain of a substitution *)

Fixpoint dom_rec_aux (S : Subst) (St : set (Var + Var)) : set (Var + Var) :=
  match St with
    | [] => []
    | V::St0 => match V with
              | inl X => if (exp_eqdec (sub (VarExp X) S) (VarExp X)) then
                          (dom_rec_aux S St0) else
                          (set_add varboth_eqdec (inl X) (dom_rec_aux S St0))
              | inr Y => if (sexp_eqdec (sub_s (VarSExp Y) S) (VarSExp Y)) then
                          (dom_rec_aux S St0) else
                          (set_add varboth_eqdec (inr Y) (dom_rec_aux S St0))
              end
   end.                  


(** dom_rec is the recursive function that gives the domain of a substitution *)

Definition dom_rec (S : Subst) := dom_rec_aux S (subst_dom_vars S).

(** im_rec_aux is a auxiliar function to build the correct image of a substitution *)

Fixpoint im_rec_aux (S : Subst) (St : set (Var + Var)) : set (exp + sexp) :=
  match St with
    | [] => []  
    | V::St0 => match V with
              | inl X => inl (sub (VarExp X) S) :: (im_rec_aux S St0)
              | inr Y => inr (sub_s (VarSExp Y) S) :: (im_rec_aux S St0)
              end
  end.



(** im_rec is the recursive function that gives the image of a substitution *)

Definition im_rec (S : Subst) := im_rec_aux S (dom_rec S).


(** exps_set_vars gives the set of variables that occur in a set of exps/sexps *)

Fixpoint exps_set_vars (T: set (exp + sexp)) : set (Var + Var) :=
  match T with
    | [] => []
    | sσ ::T0 => match sσ with
             | inl s => set_union varboth_eqdec (exp_vars s) (exps_set_vars T0)
             | inr σ => set_union varboth_eqdec (exp_vars_s σ) (exps_set_vars T0)
             end
  end.



(** im_vars gives the set of variables that occur in the image of a substiturion *)

Definition im_vars (S : Subst) := exps_set_vars (im_rec S). 


Notation "P \ u" := (set_remove Equation_eqdec u P) (at level 67).
Notation "P |^^ S" := (subs_Problem P S) (at level 67).
Notation "P |+ u" := (set_add Equation_eqdec u P) (at level 67).

Definition In_dom (M: Mapping) (S : Subst) :=
  match M with
  | exp_map X _ => (sub (VarExp X) S) <> VarExp X
  | sexp_map Y _ => (sub_s (VarSExp Y) S) <> VarSExp Y
  end.
 
Notation "M € S" := (In_dom M S) (at level 67).

Definition map_equiv (E: exp -> exp -> Prop) 

Definition subs_equiv (E : exp -> exp -> Prop) (S S' : Subst) := forall V, (V € S) \/ (V € S') ->  E (sub (VarExp X) S)
                                                                                           (sub (VarExp X) S'). 

Notation "S ~:c S'" := (subs_equiv σmin_equiv S S') (at level 67).



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
                                        
| smatch_inst : forall S S' P X s, (~ set_In X (set_union var_eqdec (exp_vars s) (lhvars_Probl P))) ->
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


(** Statement of Preservation *)
Lemma match_sol_preservation : forall Sl T T',

      valid_tuple T ->

      set_inter var_eqdec (lhvars_Probl (snd T)) (dom_rec Sl) = [] ->

      smatch T T' ->

      match_sol Sl T' -> match_sol Sl T.   
Admitted.
