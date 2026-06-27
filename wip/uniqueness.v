s[t ⋅ σ] = y[t ⋅ id]
s[t[up] ⋅ σ >> up] <- s[x ⋅ σ >> up] -> s[0 ⋅ σ >> up] 

s[σ] = x[y]

Require Import List.
Unset Elimination Schemes.
Import ListNotations.


(** σ-expressions

- VarExp is the term variables trageted by unification/matching
- Expressions don't have substitution variables
- ConstExp/ConstSExp corresponds to the bound variables (as in Dowek et al.'s definition) on which matching/unification won't affect*)
Inductive exp := Zero
               | App (s t: exp) : exp
               | Lam (s: exp): exp
               | Inst (s: exp) (σ: sexp): exp
               | VarExp (n: nat) : exp
               | ConstExp (n: nat) : exp                    
with sexp :=      I : sexp
                | Shift : sexp
                | Cons (s: exp) (σ: sexp) : sexp
                | Comp (σ τ: sexp) : sexp
                | ConstSExp (n: nat) : sexp.
Set Elimination Schemes.
Scheme exp_ind := Induction for exp Sort Prop
with  sexp_ind := Induction for sexp Sort Prop.
Combined Scheme sigma_ind from exp_ind, sexp_ind.


Notation "s [ σ ]" := (Inst s σ).
Notation "σ >> τ" := (Comp σ τ) (at level 56, right associativity).
Notation "s .: σ" := (Cons s σ) (at level 58).
Notation "↑" := Shift.

(** Instantiation of a σ-expression with θ *)
Fixpoint inst (s: exp) (θ: nat -> exp) :=
  match s with
  | Zero => Zero
  | App s t' => App (inst s θ) (inst t' θ)
  | Lam s => Lam (inst s θ)
  | Inst s σ => Inst (inst s θ) (insts σ θ)
  | VarExp n => θ n
  | s => s                
  end
with insts (σ: sexp) (θ: nat -> exp) :=
  match σ with
  | I => I
  | Shift => Shift
  | Cons s σ => Cons (inst s θ) (insts σ θ)
  | Comp σ τ => Comp (insts σ θ) (insts τ θ)
  | σ => σ
  end.

(** Computes the variables in a σ-expression *)
Fixpoint fvar (s: exp) : list nat :=
  match s with
  | Zero =>  nil
  | App s t => app (fvar s)  (fvar t)
  | Lam s => fvar s
  | Inst s σ => app (fvar s) (fvars σ)
  | VarExp n => cons n nil
  | _ => nil
  end
with fvars (σ: sexp) : list nat :=
  match σ with
  | I => nil
  | Shift => nil
  | Cons s σ => app (fvar s) (fvars σ)
  | Comp σ τ => app (fvars σ) (fvars τ)
  | _ => nil
 end.    
  

(** Equivalence with respect to σ_min-rules *)
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



(** A predicate to check if an expression has a variable *)
Fixpoint has_var (s:exp) : Prop :=
  match s with
  | Zero => False
  | App s t => (has_var s) \/ (has_var t)
  | Lam s => has_var s
  | Inst s σ => (has_var s) \/ (has_var_s σ) 
  | VarExp _ => True
  | _ => False             
  end
with has_var_s (σ: sexp) : Prop :=
  match σ with
  | I => False
  | Shift => False
  | Comp σ τ => (has_var_s σ) \/ (has_var_s τ)
  | Cons s σ => (has_var s) \/ (has_var_s σ)
  | _ => False
  end.

Definition ground s := not (has_var s).
Definition grounds σ := not (has_var_s σ).


(** A characterization of σ-normal forms *)
Inductive σ_nf : exp -> Prop :=
| nf_ze : σ_nf Zero
| nf_zeInst σ: σ_nfs σ -> σ_nf (Zero[σ])
| nf_var n:  σ_nf (VarExp n)
| nf_varInst n σ:  σ_nfs σ -> σ_nf (VarExp n)[σ]
| nf_const n : σ_nf (ConstExp n)
| nf_constInst n σ : σ_nfs σ -> σ_nf (ConstExp n)[σ]
| nf_lam s : σ_nf s -> σ_nf (Lam s)
| nf_app s t : σ_nf s -> σ_nf t -> σ_nf (App s t)
with σ_nfs : sexp -> Prop :=
| nf_id : σ_nfs I
| nf_consts n : σ_nfs (ConstSExp n)
| nf_constComp n σ: ~σ=I -> σ_nfs σ -> σ_nfs ((ConstSExp n) >> σ)
| nf_up : σ_nfs ↑
| nf_upComp σ : ~σ = I -> (forall s τ, ~ σ = s .: τ) -> σ_nfs σ -> σ_nfs (↑ >> σ) 
| nf_consSub s σ : ~s .: σ = Zero .: ↑ -> (forall τ, s .: σ = (Zero[τ]) .: (↑ >> τ) ) -> σ_nf s -> σ_nfs σ -> σ_nfs (s .: σ).



(** 

We conjecture the uniqueness for σmin-matching: 

For s and t in σ-normal form and without any substitution variables, a solution θ of "s =σmin t" is σ-equal to any other solution θ' of "s =σ t".

*)

Lemma uniqueness: (forall s t θ (H: ground s) (NF: σ_nf s /\ σ_nf t), σmin_equiv s (inst t θ) -> forall θ', σ_equiv s (inst t θ') -> (forall x, In x (fvar t) -> σ_equiv (θ x) (θ' x)) ) /\
                  (forall σ τ θ (H: grounds σ) (NF: σ_nfs σ /\ σ_nfs τ), σmin_equivs σ (insts τ θ) -> forall θ', σ_equivs σ (insts τ θ') -> (forall x, In x (fvars τ) -> σ_equiv (θ x) (θ' x)) ). 
                           
Admitted.



Inductive match_eqn :=
| exp_eqn : exp -> exp -> match_eqn
| sexp_eqn : sexp -> sexp -> match_eqn.

Definition solution := list (nat * exp).

Fixpoint sol_to_subst (sol: solution) (n: nat) : exp :=
  match sol with
  | nil => VarExp n
  | (x,e) :: sol' => if Nat.eqb x n then e
                   else (sol_to_subst sol' n)
  end.

Definition inst_sol_eqn eqn sol :=
  match eqn with
  | exp_eqn e1 e2 => exp_eqn e1 (inst e2 (sol_to_subst sol))
  | sexp_eqn e1 e2 => sexp_eqn e1 (insts e2 (sol_to_subst sol))
  end.


Open Scope list_scope.

(** Relational definition of sigma-min procedure. *)
Inductive matching : list match_eqn -> solution -> Prop :=
| var_case s x :  matching ([exp_eqn s (VarExp x)]) ([(x,s)])
| exp_eq_case (s s: exp) : matching ([exp_eqn s s]) nil
| sexp_eq_case (σ σ: sexp) : matching ([sexp_eqn σ σ]) nil
| app_case s t s' σ τ sol: matching ([exp_eqn ((App s t)[σ]) s'[τ]]) sol -> matching ([exp_eqn (App s[σ] t[σ]) s'[τ]]) sol
| app_split_case s t s' t' sol1 sol2 : matching ([exp_eqn s s']) sol1 -> matching ([exp_eqn t  (inst t' (sol_to_subst sol1))]) sol2 -> matching ([exp_eqn (App s t) (App s' t')]) (sol1++sol2) 
| lam_case s s' σ τ sol : matching ([exp_eqn (Lam s)[σ] s'[τ]]) sol -> matching ([exp_eqn (Lam (s[Zero .: (↑ >> σ)])) s'[τ]]) sol
| lam_split_case  s t sol : matching ([exp_eqn s t]) sol -> matching ([exp_eqn (Lam s) (Lam t)]) sol
| inst_split_case s t σ τ sol1 sol2  : matching ([exp_eqn s t]) sol1 -> matching ([sexp_eqn σ (insts τ (sol_to_subst sol1)) ]) sol2 -> matching ([exp_eqn s[σ] t[τ]]) (sol1 ++ sol2)
| comp_case s t σ τ θ sol: matching ([exp_eqn (s[σ])[τ] t[θ]]) sol -> matching ([exp_eqn s[σ>>τ] t[θ]]) sol   
| assoc_case σ τ θ σ' τ' sol: matching ([sexp_eqn ((σ>>τ)>>θ) (σ'>>τ')]) sol -> matching ([sexp_eqn (σ>>(τ>>θ))  (σ'>>τ')]) sol
| comp_split_case  σ τ σ' τ' sol1 sol2:  matching ([sexp_eqn σ σ']) sol1 -> matching ([sexp_eqn τ (insts τ' (sol_to_subst sol1))]) sol2 -> matching ([sexp_eqn (σ>>τ) (σ'>>τ')]) (sol1++sol2)
| mapenv_case s σ τ σ' τ' sol: matching ([sexp_eqn ((s .: σ) >> τ) (σ' >> τ')]) sol -> matching ([ sexp_eqn (s[τ] .: (σ >> τ)) (σ' >> τ')]) sol                                                                
| cons_split_case s t σ τ sol1 sol2: matching ([exp_eqn s t]) sol1 -> matching ([sexp_eqn σ (insts τ (sol_to_subst sol1))]) sol2 -> matching ([sexp_eqn (s .: σ) (t .: τ)]) (sol1++sol2)
| list_merge eqns1 eqns2 sol1 sol2: matching eqns1 sol1 -> matching (map (fun x => inst_sol_eqn x sol1) eqns2) sol2 -> matching (eqns1++eqns2) (sol1++sol2).
