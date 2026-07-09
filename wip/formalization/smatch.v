Require Import List ListSet.
Unset Elimination Schemes.
Import ListNotations.



Definition Var := nat.

Lemma var_eqdec : forall (m n: Var), {m = n} + {m <> n}.
  decide equality.
Defined.


(** σ-expressions

- VarExp is the term variables trageted by unification/matching
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


Notation "s [ σ ]" := (Inst s σ).
Notation "σ >> τ" := (Comp σ τ) (at level 56, right associativity).
Notation "s .: σ" := (Cons s σ) (at level 58).
Notation "↑" := Shift.


(** Equivalence with respect to σ-rules *)
Unset Elimination Schemes.
Inductive σ_equiv : exp -> exp -> Prop :=
| σsubst_app (s t : exp) (σ : sexp) :  σ_equiv ((App s t)[σ]) (App s[σ] t[σ])
| σsubst_lam (s : exp) (σ : sexp) :  σ_equiv  ((Lam s)[σ])  (Lam (s[Zero .: (σ >> ↑)]))
| σ_varcons (s: exp) (σ: sexp) : σ_equiv  Zero[s .: σ] s
| σ_id (s: exp) : σ_equiv s[I] s

| σequiv_refl (s : exp) :  σ_equiv s s
| σequiv_sym (s t : exp) :  σ_equiv s t -> σ_equiv t s
| σequiv_trans (s t u : exp) :  σ_equiv s t -> σ_equiv t u -> σ_equiv s u
| σequiv_app (s1 s2 t1 t2 : exp) :  σ_equiv s1 s2 -> σ_equiv t1 t2 -> σ_equiv (App s1 t1) (App s2 t2)
| σequiv_lam (s1 s2 : exp) :  σ_equiv s1 s2 -> σ_equiv (Lam s1) (Lam s2)
| σequiv_asubst (s1 s2 : exp) (σ τ : sexp) :  σ_equiv s1 s2 -> σ_equivs σ τ -> σ_equiv s1[σ] s2[τ]
with σ_equivs : sexp -> sexp -> Prop :=
| σcomp_cons (s : exp) (σ τ : sexp) :  σ_equivs  ((s .: σ) >> τ) (s[τ] .: (σ >> τ)) 
| σcomp_assoc (σ τ θ : sexp) :  σ_equivs ((σ >> τ) >> θ) (σ >> (τ >> θ))
| σ_idl (σ: sexp) : σ_equivs (I >> σ) σ
| σ_idr (σ: sexp) : σ_equivs (σ >> I) σ
| σ_shiftcons (s: exp) (σ: sexp) : σ_equivs (↑ >> (s .: σ)) σ
| σ_varshift : σ_equivs (Zero .: ↑) I
| σ_scons (σ: sexp) : σ_equivs ( (Zero[σ]) .: (↑ >> σ)) σ

| σequivs_refl (σ : sexp) :  σ_equivs σ σ
| σequivs_sym (σ τ : sexp) :  σ_equivs σ τ -> σ_equivs τ σ
| σequivs_trans (σ τ θ : sexp) :  σ_equivs σ τ -> σ_equivs τ θ -> σ_equivs σ θ
| σequivs_cons (s1 s2 : exp) (σ τ : sexp) :  σ_equiv s1 s2 -> σ_equivs σ τ -> σ_equivs (s1 .: σ) (s2 .: τ)
| σequivs_comp (σ1 σ2 τ1 τ2 : sexp) :  σ_equivs σ1 σ2 -> σ_equivs τ1 τ2 ->  σ_equivs (σ1 >> τ1) (σ2 >> τ2).
Set Elimination Schemes.  
Scheme σ_equiv_ind := Induction for σ_equiv Sort Prop
with  σ_equivs_ind := Induction for σ_equivs Sort Prop.
Combined Scheme σ_eqs_ind from σ_equiv_ind, σ_equivs_ind.



Inductive Equation : Set :=
| equ : exp -> exp -> Equation
| equ_s : sexp -> sexp -> Equation.



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

  

Open Scope type_scope.


Definition Subst := set (Var * exp).
Definition Problem := set Equation.   
Definition Tuple := (Subst * Problem).

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



(** terms_set_vars gives the set of variables that occur in a set of terms *)

Fixpoint exps_set_vars (T: set exp) : set Var :=
  match T with
    | [] => []
    | s::T0 => set_union var_eqdec (exp_vars s) (exps_set_vars T0)        
  end.

(** im_vars gives the set of variables that occur in the image of a substiturion *)

Definition im_vars (S : Subst) := exps_set_vars (im_rec S). 





Notation "P \ u" := (set_remove Equation_eqdec u P) (at level 67).
Notation "P |^^ S" := (subs_Problem P S) (at level 67).
Notation "P |+ u" := (set_add Equation_eqdec u P) (at level 67).

Definition In_dom (X : Var) (S : Subst) :=  (sub (VarExp X) S) <> VarExp X . 
Notation "X € S" := (In_dom X S) (at level 67).

Definition subs_equiv (E : exp -> exp -> Prop) (S S' : Subst) := forall X, (X € S) \/ (X € S') -> E (sub (VarExp X) S)
                                                                                           (sub (VarExp X) S'). 

Notation "S ~:c S'" := (subs_equiv σ_equiv S S') (at level 67).

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




Definition match_sol (S' :Subst) (T : Tuple) :=
  let S := (fst T) in
  let P := (snd T) in
  ( forall s t, set_In (equ s t) P ->  σ_equiv s (sub s S') ) /\         
  ( exists S'', (sub_comp S S'') ~:c S' ) /\
  set_inter var_eqdec (lhvars_Probl P) (dom_rec S') = []. 

Lemma match_sol_preservation : forall Sl T T',

      valid_tuple T ->

      set_inter var_eqdec (lhvars_Probl (snd T)) (dom_rec Sl) = [] ->

      smatch T T' ->

      match_sol Sl T' -> match_sol Sl T.   
Admitted.
