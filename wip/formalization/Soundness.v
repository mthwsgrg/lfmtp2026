Require Export SigmaMatch.

(* Temp lemmas in this file start*)


(* Temp lemmas in this file end *)
 
Definition valid_tuple (T : Tuple) :=
  let S := (fst T) in
  let P := (snd T) in
  ( set_inter sortedvar_eqdec (dom_rec S) (Problem_vars P) = [] ).


Definition match_sol (S' :Subst) (T : Tuple) :=
  let S := (fst T) in
  let P := (snd T) in
  ( forall s t, set_In (equ s t) P ->  σmin_equiv s (sub t S') ) /\
  ( forall σ τ, set_In (equ_s σ τ) P -> σmin_equivs σ (sub_s τ S')) /\  
  ( exists S'', (sub_comp S S'') ~:c S' ).


Lemma match_sol_preservation : forall Sl T T',

      valid_tuple T ->

      set_inter sortedvar_eqdec (lhvars_Probl (snd T)) (dom_rec Sl) = [] ->

      smatch T T' ->

      match_sol Sl T' -> match_sol Sl T.   
Proof.
  intros Sl T T' HVl HLh HSt HSl. unfold valid_tuple in HVl.
  destruct HSt; intros; unfold match_sol in *; simpl in *;
  destruct HSl as [HEq1 [HEq2 HEq3]]; destruct HEq3 as [S'' HEq3]; repeat split;
  try (exists S''; assumption); try intros s0 t0 HinP. 
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.

  (* Inst Exp Case *)
  - unfold subs_equiv in HEq3; destruct HEq3 as [HEq3 HEq3'].   
    destruct (Equation_eqdec (equ s0 t0) (equ s (VarExp X))) as [Eq | Eq]; intros.
    + rewrite Eq in *. simpl in *.
      inversion Eq; subst. clear Eq.
      simpl. apply σmin_equiv_trans with (t := sub s S'').
      

Admitted.      
