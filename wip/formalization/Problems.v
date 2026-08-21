Require Export Substs.

Inductive Equation : Set :=
| equ : exp -> exp -> Equation
| equ_s : sexp -> sexp -> Equation.


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


Fixpoint lhvars_Probl (P : Problem) : set SortedVar :=
  match P with
  | [] => []
  | (equ s t) :: P0 => set_union sortedvar_eqdec (vars_of_exp s) (lhvars_Probl P0)
  | (equ_s σ τ) :: P0 => set_union sortedvar_eqdec (vars_of_sexp σ) (lhvars_Probl P0)                     
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


