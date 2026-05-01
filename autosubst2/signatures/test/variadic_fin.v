Require Export fintype.



Section tm.
Inductive tm (ntm : nat) : Type :=
  | var_tm : (fin) (ntm) -> tm (ntm)
  | app : forall (p : nat), tm  (ntm) -> cod (fin p) (tm  (ntm)) -> tm (ntm)
  | lam : forall (p : nat), tm  (p + ntm) -> tm (ntm).

Lemma congr_app { p : nat } { mtm : nat } { s0 : tm  (mtm) } { s1 : cod (fin p) (tm  (mtm)) } { t0 : tm  (mtm) } { t1 : cod (fin p) (tm  (mtm)) } (H1 : s0 = t0) (H2 : s1 = t1) : app (mtm) p s0 s1 = app (mtm) p t0 t1 .
Proof. congruence. Qed.

Lemma congr_lam { p : nat } { mtm : nat } { s0 : tm  (p + mtm) } { t0 : tm  (p + mtm) } (H1 : s0 = t0) : lam (mtm) p s0 = lam (mtm) p t0 .
Proof. congruence. Qed.

Definition upRenList_tm_tm (p : nat) { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (p + (m)) -> (fin) (p + (n)) :=
  upRen_p p xi.

Fixpoint ren_tm { mtm : nat } { ntm : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (s : tm (mtm)) : tm (ntm) :=
    match s return tm (ntm) with
    | var_tm (_) s => (var_tm (ntm)) (xitm s)
    | app (_) p s0 s1 => app (ntm) p ((ren_tm xitm) s0) ((cod_map (ren_tm xitm)) s1)
    | lam (_) p s0 => lam (ntm) p ((ren_tm (upRenList_tm_tm p xitm)) s0)
    end.

Definition upList_tm_tm (p : nat) { m : nat } { ntm : nat } (sigma : (fin) (m) -> tm (ntm)) : (fin) (p + (m)) -> tm (p + ntm) :=
  scons_p  p ((funcomp) (var_tm (p + ntm)) (zero_p p)) ((funcomp) (ren_tm (shift_p p)) sigma).

Fixpoint subst_tm { mtm : nat } { ntm : nat } (sigmatm : (fin) (mtm) -> tm (ntm)) (s : tm (mtm)) : tm (ntm) :=
    match s return tm (ntm) with
    | var_tm (_) s => sigmatm s
    | app (_) p s0 s1 => app (ntm) p ((subst_tm sigmatm) s0) ((cod_map (subst_tm sigmatm)) s1)
    | lam (_) p s0 => lam (ntm) p ((subst_tm (upList_tm_tm p sigmatm)) s0)
    end.

Definition upIdList_tm_tm { p : nat } { mtm : nat } (sigma : (fin) (mtm) -> tm (mtm)) (Eq : forall x, sigma x = (var_tm (mtm)) x) : forall x, (upList_tm_tm p sigma) x = (var_tm (p + mtm)) x :=
  fun n => scons_p_eta (var_tm (p + mtm)) (fun n => (ap) (ren_tm (shift_p p)) (Eq n)) (fun n => eq_refl).

Fixpoint idSubst_tm { mtm : nat } (sigmatm : (fin) (mtm) -> tm (mtm)) (Eqtm : forall x, sigmatm x = (var_tm (mtm)) x) (s : tm (mtm)) : subst_tm sigmatm s = s :=
    match s return subst_tm sigmatm s = s with
    | var_tm (_) s => Eqtm s
    | app (_) p s0 s1 => congr_app ((idSubst_tm sigmatm Eqtm) s0) ((cod_id (idSubst_tm sigmatm Eqtm)) s1)
    | lam (_) p s0 => congr_lam ((idSubst_tm (upList_tm_tm p sigmatm) (upIdList_tm_tm (_) Eqtm)) s0)
    end.

Definition upExtRen_list_tm_tm { p : nat } { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRenList_tm_tm p xi) x = (upRenList_tm_tm p zeta) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (shift_p p) (Eq n)).

Fixpoint extRen_tm { mtm : nat } { ntm : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (zetatm : (fin) (mtm) -> (fin) (ntm)) (Eqtm : forall x, xitm x = zetatm x) (s : tm (mtm)) : ren_tm xitm s = ren_tm zetatm s :=
    match s return ren_tm xitm s = ren_tm zetatm s with
    | var_tm (_) s => (ap) (var_tm (ntm)) (Eqtm s)
    | app (_) p s0 s1 => congr_app ((extRen_tm xitm zetatm Eqtm) s0) ((cod_ext (extRen_tm xitm zetatm Eqtm)) s1)
    | lam (_) p s0 => congr_lam ((extRen_tm (upRenList_tm_tm p xitm) (upRenList_tm_tm p zetatm) (upExtRen_list_tm_tm (_) (_) Eqtm)) s0)
    end.

Definition upExt_list_tm_tm { p : nat } { m : nat } { ntm : nat } (sigma : (fin) (m) -> tm (ntm)) (tau : (fin) (m) -> tm (ntm)) (Eq : forall x, sigma x = tau x) : forall x, (upList_tm_tm p sigma) x = (upList_tm_tm p tau) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (ren_tm (shift_p p)) (Eq n)).

Fixpoint ext_tm { mtm : nat } { ntm : nat } (sigmatm : (fin) (mtm) -> tm (ntm)) (tautm : (fin) (mtm) -> tm (ntm)) (Eqtm : forall x, sigmatm x = tautm x) (s : tm (mtm)) : subst_tm sigmatm s = subst_tm tautm s :=
    match s return subst_tm sigmatm s = subst_tm tautm s with
    | var_tm (_) s => Eqtm s
    | app (_) p s0 s1 => congr_app ((ext_tm sigmatm tautm Eqtm) s0) ((cod_ext (ext_tm sigmatm tautm Eqtm)) s1)
    | lam (_) p s0 => congr_lam ((ext_tm (upList_tm_tm p sigmatm) (upList_tm_tm p tautm) (upExt_list_tm_tm (_) (_) Eqtm)) s0)
    end.

Definition up_ren_ren_list_tm_tm { p : nat } { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRenList_tm_tm p tau) (upRenList_tm_tm p xi)) x = (upRenList_tm_tm p theta) x :=
  up_ren_ren_p Eq.

Fixpoint compRenRen_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (rhotm : (fin) (mtm) -> (fin) (ltm)) (Eqtm : forall x, ((funcomp) zetatm xitm) x = rhotm x) (s : tm (mtm)) : ren_tm zetatm (ren_tm xitm s) = ren_tm rhotm s :=
    match s return ren_tm zetatm (ren_tm xitm s) = ren_tm rhotm s with
    | var_tm (_) s => (ap) (var_tm (ltm)) (Eqtm s)
    | app (_) p s0 s1 => congr_app ((compRenRen_tm xitm zetatm rhotm Eqtm) s0) ((cod_comp (compRenRen_tm xitm zetatm rhotm Eqtm)) s1)
    | lam (_) p s0 => congr_lam ((compRenRen_tm (upRenList_tm_tm p xitm) (upRenList_tm_tm p zetatm) (upRenList_tm_tm p rhotm) (up_ren_ren_p Eqtm)) s0)
    end.

Definition up_ren_subst_list_tm_tm { p : nat } { k : nat } { l : nat } { mtm : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> tm (mtm)) (theta : (fin) (k) -> tm (mtm)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upList_tm_tm p tau) (upRenList_tm_tm p xi)) x = (upList_tm_tm p theta) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (_) n) (scons_p_congr (fun z => scons_p_head' (_) (_) z) (fun z => (eq_trans) (scons_p_tail' (_) (_) (xi z)) ((ap) (ren_tm (shift_p p)) (Eq z)))).

Fixpoint compRenSubst_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (tautm : (fin) (ktm) -> tm (ltm)) (thetatm : (fin) (mtm) -> tm (ltm)) (Eqtm : forall x, ((funcomp) tautm xitm) x = thetatm x) (s : tm (mtm)) : subst_tm tautm (ren_tm xitm s) = subst_tm thetatm s :=
    match s return subst_tm tautm (ren_tm xitm s) = subst_tm thetatm s with
    | var_tm (_) s => Eqtm s
    | app (_) p s0 s1 => congr_app ((compRenSubst_tm xitm tautm thetatm Eqtm) s0) ((cod_comp (compRenSubst_tm xitm tautm thetatm Eqtm)) s1)
    | lam (_) p s0 => congr_lam ((compRenSubst_tm (upRenList_tm_tm p xitm) (upList_tm_tm p tautm) (upList_tm_tm p thetatm) (up_ren_subst_list_tm_tm (_) (_) (_) Eqtm)) s0)
    end.

Definition up_subst_ren_list_tm_tm { p : nat } { k : nat } { ltm : nat } { mtm : nat } (sigma : (fin) (k) -> tm (ltm)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (theta : (fin) (k) -> tm (mtm)) (Eq : forall x, ((funcomp) (ren_tm zetatm) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRenList_tm_tm p zetatm)) (upList_tm_tm p sigma)) x = (upList_tm_tm p theta) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (_) n) (scons_p_congr (fun x => (ap) (var_tm (p + mtm)) (scons_p_head' (_) (_) x)) (fun n => (eq_trans) (compRenRen_tm (shift_p p) (upRenList_tm_tm p zetatm) ((funcomp) (shift_p p) zetatm) (fun x => scons_p_tail' (_) (_) x) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetatm (shift_p p) ((funcomp) (shift_p p) zetatm) (fun x => eq_refl) (sigma n))) ((ap) (ren_tm (shift_p p)) (Eq n))))).

Fixpoint compSubstRen_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : (fin) (mtm) -> tm (ktm)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (thetatm : (fin) (mtm) -> tm (ltm)) (Eqtm : forall x, ((funcomp) (ren_tm zetatm) sigmatm) x = thetatm x) (s : tm (mtm)) : ren_tm zetatm (subst_tm sigmatm s) = subst_tm thetatm s :=
    match s return ren_tm zetatm (subst_tm sigmatm s) = subst_tm thetatm s with
    | var_tm (_) s => Eqtm s
    | app (_) p s0 s1 => congr_app ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s0) ((cod_comp (compSubstRen_tm sigmatm zetatm thetatm Eqtm)) s1)
    | lam (_) p s0 => congr_lam ((compSubstRen_tm (upList_tm_tm p sigmatm) (upRenList_tm_tm p zetatm) (upList_tm_tm p thetatm) (up_subst_ren_list_tm_tm (_) (_) (_) Eqtm)) s0)
    end.

Definition up_subst_subst_list_tm_tm { p : nat } { k : nat } { ltm : nat } { mtm : nat } (sigma : (fin) (k) -> tm (ltm)) (tautm : (fin) (ltm) -> tm (mtm)) (theta : (fin) (k) -> tm (mtm)) (Eq : forall x, ((funcomp) (subst_tm tautm) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (upList_tm_tm p tautm)) (upList_tm_tm p sigma)) x = (upList_tm_tm p theta) x :=
  fun n => (eq_trans) (scons_p_comp' ((funcomp) (var_tm (p + ltm)) (zero_p p)) (_) (_) n) (scons_p_congr (fun x => scons_p_head' (_) (fun z => ren_tm (shift_p p) (_)) x) (fun n => (eq_trans) (compRenSubst_tm (shift_p p) (upList_tm_tm p tautm) ((funcomp) (upList_tm_tm p tautm) (shift_p p)) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tautm (shift_p p) (_) (fun x => (eq_sym) (scons_p_tail' (_) (_) x)) (sigma n))) ((ap) (ren_tm (shift_p p)) (Eq n))))).

Fixpoint compSubstSubst_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : (fin) (mtm) -> tm (ktm)) (tautm : (fin) (ktm) -> tm (ltm)) (thetatm : (fin) (mtm) -> tm (ltm)) (Eqtm : forall x, ((funcomp) (subst_tm tautm) sigmatm) x = thetatm x) (s : tm (mtm)) : subst_tm tautm (subst_tm sigmatm s) = subst_tm thetatm s :=
    match s return subst_tm tautm (subst_tm sigmatm s) = subst_tm thetatm s with
    | var_tm (_) s => Eqtm s
    | app (_) p s0 s1 => congr_app ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s0) ((cod_comp (compSubstSubst_tm sigmatm tautm thetatm Eqtm)) s1)
    | lam (_) p s0 => congr_lam ((compSubstSubst_tm (upList_tm_tm p sigmatm) (upList_tm_tm p tautm) (upList_tm_tm p thetatm) (up_subst_subst_list_tm_tm (_) (_) (_) Eqtm)) s0)
    end.

Definition rinstInst_up_list_tm_tm { p : nat } { m : nat } { ntm : nat } (xi : (fin) (m) -> (fin) (ntm)) (sigma : (fin) (m) -> tm (ntm)) (Eq : forall x, ((funcomp) (var_tm (ntm)) xi) x = sigma x) : forall x, ((funcomp) (var_tm (p + ntm)) (upRenList_tm_tm p xi)) x = (upList_tm_tm p sigma) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (var_tm (p + ntm)) n) (scons_p_congr (fun z => eq_refl) (fun n => (ap) (ren_tm (shift_p p)) (Eq n))).

Fixpoint rinst_inst_tm { mtm : nat } { ntm : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (sigmatm : (fin) (mtm) -> tm (ntm)) (Eqtm : forall x, ((funcomp) (var_tm (ntm)) xitm) x = sigmatm x) (s : tm (mtm)) : ren_tm xitm s = subst_tm sigmatm s :=
    match s return ren_tm xitm s = subst_tm sigmatm s with
    | var_tm (_) s => Eqtm s
    | app (_) p s0 s1 => congr_app ((rinst_inst_tm xitm sigmatm Eqtm) s0) ((cod_ext (rinst_inst_tm xitm sigmatm Eqtm)) s1)
    | lam (_) p s0 => congr_lam ((rinst_inst_tm (upRenList_tm_tm p xitm) (upList_tm_tm p sigmatm) (rinstInst_up_list_tm_tm (_) (_) Eqtm)) s0)
    end.

Lemma rinstInst_tm { mtm : nat } { ntm : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) : ren_tm xitm = subst_tm ((funcomp) (var_tm (ntm)) xitm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_tm xitm (_) (fun n => eq_refl) x)). Qed.

Lemma instId_tm { mtm : nat } : subst_tm (var_tm (mtm)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_tm (var_tm (mtm)) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_tm { mtm : nat } : @ren_tm (mtm) (mtm) (id) = id .
Proof. exact ((eq_trans) (rinstInst_tm ((id) (_))) instId_tm). Qed.

Lemma varL_tm { mtm : nat } { ntm : nat } (sigmatm : (fin) (mtm) -> tm (ntm)) : (funcomp) (subst_tm sigmatm) (var_tm (mtm)) = sigmatm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_tm { mtm : nat } { ntm : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) : (funcomp) (ren_tm xitm) (var_tm (mtm)) = (funcomp) (var_tm (ntm)) xitm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : (fin) (mtm) -> tm (ktm)) (tautm : (fin) (ktm) -> tm (ltm)) (s : tm (mtm)) : subst_tm tautm (subst_tm sigmatm s) = subst_tm ((funcomp) (subst_tm tautm) sigmatm) s .
Proof. exact (compSubstSubst_tm sigmatm tautm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : (fin) (mtm) -> tm (ktm)) (tautm : (fin) (ktm) -> tm (ltm)) : (funcomp) (subst_tm tautm) (subst_tm sigmatm) = subst_tm ((funcomp) (subst_tm tautm) sigmatm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_tm sigmatm tautm n)). Qed.

Lemma compRen_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : (fin) (mtm) -> tm (ktm)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (s : tm (mtm)) : ren_tm zetatm (subst_tm sigmatm s) = subst_tm ((funcomp) (ren_tm zetatm) sigmatm) s .
Proof. exact (compSubstRen_tm sigmatm zetatm (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : (fin) (mtm) -> tm (ktm)) (zetatm : (fin) (ktm) -> (fin) (ltm)) : (funcomp) (ren_tm zetatm) (subst_tm sigmatm) = subst_tm ((funcomp) (ren_tm zetatm) sigmatm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_tm sigmatm zetatm n)). Qed.

Lemma renComp_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (tautm : (fin) (ktm) -> tm (ltm)) (s : tm (mtm)) : subst_tm tautm (ren_tm xitm s) = subst_tm ((funcomp) tautm xitm) s .
Proof. exact (compRenSubst_tm xitm tautm (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (tautm : (fin) (ktm) -> tm (ltm)) : (funcomp) (subst_tm tautm) (ren_tm xitm) = subst_tm ((funcomp) tautm xitm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_tm xitm tautm n)). Qed.

Lemma renRen_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (s : tm (mtm)) : ren_tm zetatm (ren_tm xitm s) = ren_tm ((funcomp) zetatm xitm) s .
Proof. exact (compRenRen_tm xitm zetatm (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (zetatm : (fin) (ktm) -> (fin) (ltm)) : (funcomp) (ren_tm zetatm) (ren_tm xitm) = ren_tm ((funcomp) zetatm xitm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_tm xitm zetatm n)). Qed.

End tm.

Arguments var_tm {ntm}.

Arguments app {ntm}.

Arguments lam {ntm}.

Global Instance Subst_tm { mtm : nat } { ntm : nat } : Subst1 ((fin) (mtm) -> tm (ntm)) (tm (mtm)) (tm (ntm)) := @subst_tm (mtm) (ntm) .

Global Instance Ren_tm { mtm : nat } { ntm : nat } : Ren1 ((fin) (mtm) -> (fin) (ntm)) (tm (mtm)) (tm (ntm)) := @ren_tm (mtm) (ntm) .

Global Instance VarInstance_tm { mtm : nat } : Var ((fin) (mtm)) (tm (mtm)) := @var_tm (mtm) .

Notation "x '__tm'" := (var_tm x) (at level 5, format "x __tm") : subst_scope.

Notation "x '__tm'" := (@ids (_) (_) VarInstance_tm x) (at level 5, only printing, format "x __tm") : subst_scope.

Notation "'var'" := (var_tm) (only printing, at level 1) : subst_scope.

Class Up_tm X Y := up_tm : X -> Y.

Notation "↑__tm" := (up_tm) (only printing) : subst_scope.

Notation "s [ sigmatm ]" := (subst_tm sigmatm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmatm ]" := (subst_tm sigmatm) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xitm ⟩" := (ren_tm xitm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xitm ⟩" := (ren_tm xitm) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_tm,  Ren_tm,  VarInstance_tm.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_tm,  Ren_tm,  VarInstance_tm in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_tm| progress rewrite ?compComp_tm| progress rewrite ?compComp'_tm| progress rewrite ?rinstId_tm| progress rewrite ?compRen_tm| progress rewrite ?compRen'_tm| progress rewrite ?renComp_tm| progress rewrite ?renComp'_tm| progress rewrite ?renRen_tm| progress rewrite ?renRen'_tm| progress rewrite ?varL_tm| progress rewrite ?varLRen_tm| progress (unfold up_ren, upRenList_tm_tm, upList_tm_tm)| progress (cbn [subst_tm ren_tm])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_tm in *| progress rewrite ?compComp_tm in *| progress rewrite ?compComp'_tm in *| progress rewrite ?rinstId_tm in *| progress rewrite ?compRen_tm in *| progress rewrite ?compRen'_tm in *| progress rewrite ?renComp_tm in *| progress rewrite ?renComp'_tm in *| progress rewrite ?renRen_tm in *| progress rewrite ?renRen'_tm in *| progress rewrite ?varL_tm in *| progress rewrite ?varLRen_tm in *| progress (unfold up_ren, upRenList_tm_tm, upList_tm_tm in *)| progress (cbn [subst_tm ren_tm] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_tm).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_tm).

(** as_apply follows **)

Ltac  musigma gexp hexp :=
  match   gexp  with
  |  ?s  =>  unify   (gexp) (hexp)
  |  app ?p (subst_tm ?sigma0 ?s0) (cod_map (subst_tm ?sigma0) ?s1)  =>  first [ unify   (subst_tm sigma0 (app p s0 s1)) (hexp)|  musigma   (subst_tm sigma0 (app p s0 s1)) (hexp) ]
  |  lam ?p (subst_tm (scons_p ?p ((funcomp) var_tm (zero_p ?p)) ((funcomp) (ren_tm (shift_p ?p)) ?sigma0)) ?s0)  =>  first [ unify   (subst_tm sigma0 (lam p s0)) (hexp)|  musigma   (subst_tm sigma0 (lam p s0)) (hexp) ]
  |  app ?p (ren_tm ?sigma0 ?s0) (cod_map (ren_tm ?sigma0) ?s1)  =>  first [ unify   (ren_tm sigma0 (app p s0 s1)) (hexp)|  musigma   (ren_tm sigma0 (app p s0 s1)) (hexp) ]
  |  lam ?p (ren_tm (scons_p ?p (zero_p ?p) ((funcomp) (shift_p ?p) ?sigma0)) ?s0)  =>  first [ unify   (ren_tm sigma0 (lam p s0)) (hexp)|  musigma   (ren_tm sigma0 (lam p s0)) (hexp) ]
  |  ren_tm ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  ren_tm ?theta0 ?t  =>  first [ unify   (ren_tm tau0 (ren_tm sigma0 s)) (hexp)|  musigma   (ren_tm tau0 (ren_tm sigma0 s)) (hexp) ]
  end
  |  subst_tm ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  subst_tm ?theta0 ?t  =>  first [ unify   (subst_tm tau0 (ren_tm sigma0 s)) (hexp)|  musigma   (subst_tm tau0 (ren_tm sigma0 s)) (hexp) ]
  end
  |  subst_tm ((funcomp) (ren_tm ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  ren_tm ?theta0 ?t  =>  first [ unify   (ren_tm tau0 (subst_tm sigma0 s)) (hexp)|  musigma   (ren_tm tau0 (subst_tm sigma0 s)) (hexp) ]
  end
  |  subst_tm ((funcomp) (subst_tm ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  subst_tm ?theta0 ?t  =>  first [ unify   (subst_tm tau0 (subst_tm sigma0 s)) (hexp)|  musigma   (subst_tm tau0 (subst_tm sigma0 s)) (hexp) ]
  end
  |  (funcomp) (ren_tm ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_tm ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_tm tau0) ((funcomp) (ren_tm sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (ren_tm tau0) ((funcomp) (ren_tm sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_tm ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_tm ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_tm tau0) ((funcomp) (ren_tm sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (subst_tm tau0) ((funcomp) (ren_tm sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_tm ((funcomp) (ren_tm ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_tm ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_tm tau0) ((funcomp) (subst_tm sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (ren_tm tau0) ((funcomp) (subst_tm sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_tm ((funcomp) (subst_tm ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_tm ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_tm tau0) ((funcomp) (subst_tm sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (subst_tm tau0) ((funcomp) (subst_tm sigma0) sigmas)) (hexp) ]
  end
  |  (scons) (ren_tm ?sigma0 ?s) ((funcomp) (ren_tm ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (ren_tm ?tau0) ?thetah  =>  first [ unify   ((funcomp) (ren_tm sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (ren_tm sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (subst_tm ?sigma0 ?s) ((funcomp) (subst_tm ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (subst_tm ?tau0) ?thetah  =>  first [ unify   ((funcomp) (subst_tm sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (subst_tm sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  app ?p ?s0 ?s1  =>  match   hexp  with
  |  app ?p_ ?t0 ?t1  =>  musigma   (p) (p_); musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  lam ?p ?s0  =>  match   hexp  with
  |  lam ?p_ ?t0  =>  musigma   (p) (p_); musigma   (s0) (t0)
  end
  |  subst_tm ?sigma0 ?s  =>  match   hexp  with
  |  subst_tm ?tau0 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0)
  end
  |  ren_tm ?sigma0 ?s  =>  match   hexp  with
  |  ren_tm ?tau0 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0)
  end
  |  (funcomp) (subst_tm ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_tm ?tau0) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0)
  end
  |  (funcomp) (ren_tm ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_tm ?tau0) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0)
  end
  end.

Ltac  heuristics gexp hexp :=
  match   gexp  with
  |  ?s  =>  unify   (gexp) (hexp)
  |  (funcomp) (subst_tm ((funcomp) var_tm ?sigma0)) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_tm ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (subst_tm ((funcomp) var_tm sigma0)) sigma = (funcomp) (ren_tm sigma0) sigma) as eq by (renamify; reflexivity); rewrite   (eq); unify   ((funcomp) (ren_tm sigma0) sigma) (hexp); clear eq
  end
  |  subst_tm ((funcomp) var_tm ?sigma0) ?s  =>  match   hexp  with
  |  ren_tm ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (subst_tm ((funcomp) var_tm sigma0) s = ren_tm sigma0 s) as eq by (renamify; reflexivity); rewrite   (eq); unify   (ren_tm sigma0 s) (hexp); clear eq
  end
  |  (funcomp) (ren_tm ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_tm ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_tm sigma0) sigma = (funcomp) (subst_tm ((funcomp) var_tm sigma0)) sigma) as eq by (substify; reflexivity); rewrite   (eq); unify   ((funcomp) (subst_tm ((funcomp) var_tm sigma0)) sigma) (hexp); clear eq
  end
  |  ren_tm ?sigma0 ?s  =>  match   hexp  with
  |  subst_tm ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (ren_tm sigma0 s = subst_tm ((funcomp) var_tm sigma0) s) as eq by (substify; reflexivity); rewrite   (eq); unify   (subst_tm ((funcomp) var_tm sigma0) s) (hexp); clear eq
  end
  |  ?s  =>  musigma   (gexp) (hexp)
  |  subst_tm (scons_p ?p ?stm0 ((funcomp) var_tm ?sigmatm)) ?stm  =>  match   hexp  with
  |  subst_tm (scons_p ?p_ ?ttm0 var_tm) ?ttm  =>  unify   (subst_tm (scons_p p stm0 var_tm) (ren_tm (scons_p p (zero_p p) ((funcomp) (shift_p p) sigmatm)) stm)) (hexp)
  end
  |  subst_tm (scons_p ?p ?stm0 ?sigmatm) ?stm  =>  match   hexp  with
  |  subst_tm (scons_p ?p_ ?ttm0 var_tm) ?ttm  =>  unify   (subst_tm (scons_p p stm0 var_tm) (subst_tm (scons_p p ((funcomp) var_tm (zero_p p)) ((funcomp) (ren_tm (shift_p p)) sigmatm)) stm)) (hexp)
  end
  |  ?s  =>  match   hexp  with
  |  subst_tm ?sigma0 ?t  =>  unify   (subst_tm var_tm s) (hexp)
  |  ren_tm ?sigma0 ?t  =>  unify   (ren_tm (id) s) (hexp)
  end
  |  app ?p ?s0 ?s1  =>  match   hexp  with
  |  app ?p_ ?t0 ?t1  =>  heuristics   (p) (p_); heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  lam ?p ?s0  =>  match   hexp  with
  |  lam ?p_ ?t0  =>  heuristics   (p) (p_); heuristics   (s0) (t0)
  end
  |  subst_tm ?sigma0 ?s  =>  match   hexp  with
  |  subst_tm ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  ren_tm ?sigma0 ?s  =>  match   hexp  with
  |  ren_tm ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (subst_tm ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_tm ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (ren_tm ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_tm ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  end.

Ltac  match_concl_goal H :=
  let ty_hyp := type of H in
  match   goal  with
  |  [   |-  ?Pr ?garg0 ?garg1 ?garg2 ?garg3 ?garg4 ?garg5 ?garg6 ?garg7 ?garg8 ]  =>  match   ty_hyp  with
  |  Pr ?harg0 ?harg1 ?harg2 ?harg3 ?harg4 ?harg5 ?harg6 ?harg7 ?harg8  =>  heuristics   (garg0) (harg0); heuristics   (garg1) (harg1); heuristics   (garg2) (harg2); heuristics   (garg3) (harg3); heuristics   (garg4) (harg4); heuristics   (garg5) (harg5); heuristics   (garg6) (harg6); heuristics   (garg7) (harg7); heuristics   (garg8) (harg8)
  end
  |  [   |-  ?Pr ?garg0 ?garg1 ?garg2 ?garg3 ?garg4 ?garg5 ?garg6 ?garg7 ]  =>  match   ty_hyp  with
  |  Pr ?harg0 ?harg1 ?harg2 ?harg3 ?harg4 ?harg5 ?harg6 ?harg7  =>  heuristics   (garg0) (harg0); heuristics   (garg1) (harg1); heuristics   (garg2) (harg2); heuristics   (garg3) (harg3); heuristics   (garg4) (harg4); heuristics   (garg5) (harg5); heuristics   (garg6) (harg6); heuristics   (garg7) (harg7)
  end
  |  [   |-  ?Pr ?garg0 ?garg1 ?garg2 ?garg3 ?garg4 ?garg5 ?garg6 ]  =>  match   ty_hyp  with
  |  Pr ?harg0 ?harg1 ?harg2 ?harg3 ?harg4 ?harg5 ?harg6  =>  heuristics   (garg0) (harg0); heuristics   (garg1) (harg1); heuristics   (garg2) (harg2); heuristics   (garg3) (harg3); heuristics   (garg4) (harg4); heuristics   (garg5) (harg5); heuristics   (garg6) (harg6)
  end
  |  [   |-  ?Pr ?garg0 ?garg1 ?garg2 ?garg3 ?garg4 ?garg5 ]  =>  match   ty_hyp  with
  |  Pr ?harg0 ?harg1 ?harg2 ?harg3 ?harg4 ?harg5  =>  heuristics   (garg0) (harg0); heuristics   (garg1) (harg1); heuristics   (garg2) (harg2); heuristics   (garg3) (harg3); heuristics   (garg4) (harg4); heuristics   (garg5) (harg5)
  end
  |  [   |-  ?Pr ?garg0 ?garg1 ?garg2 ?garg3 ?garg4 ]  =>  match   ty_hyp  with
  |  Pr ?harg0 ?harg1 ?harg2 ?harg3 ?harg4  =>  heuristics   (garg0) (harg0); heuristics   (garg1) (harg1); heuristics   (garg2) (harg2); heuristics   (garg3) (harg3); heuristics   (garg4) (harg4)
  end
  |  [   |-  ?Pr ?garg0 ?garg1 ?garg2 ?garg3 ]  =>  match   ty_hyp  with
  |  Pr ?harg0 ?harg1 ?harg2 ?harg3  =>  heuristics   (garg0) (harg0); heuristics   (garg1) (harg1); heuristics   (garg2) (harg2); heuristics   (garg3) (harg3)
  end
  |  [   |-  ?Pr ?garg0 ?garg1 ?garg2 ]  =>  match   ty_hyp  with
  |  Pr ?harg0 ?harg1 ?harg2  =>  heuristics   (garg0) (harg0); heuristics   (garg1) (harg1); heuristics   (garg2) (harg2)
  end
  |  [   |-  ?Pr ?garg0 ?garg1 ]  =>  match   ty_hyp  with
  |  Pr ?harg0 ?harg1  =>  heuristics   (garg0) (harg0); heuristics   (garg1) (harg1)
  end
  |  [   |-  ?Pr ?garg0 ]  =>  match   ty_hyp  with
  |  Pr ?harg0  =>  heuristics   (garg0) (harg0)
  end
  end.

Ltac premises_to_subgoals H n := 
   match (eval compute in n) with 
   | 0 => match_concl_goal H; asimpl in H; exact H 
   | _ => let ty_hyp := type of H in 
        match ty_hyp with 
        | ?ant -> ?concl => let z := fresh "z" in 
                           evar (z: ant); specialize (H ?z); premises_to_subgoals H (n-1); clear z 
       end 
   end.

Ltac qvar_to_evar H n := 
  match (eval compute in n) with 
  | 0 => let H' := fresh "H" in 
       pose proof H as H'; 
       first [ premises_to_subgoals H' 0| premises_to_subgoals H' 1| premises_to_subgoals H' 2| premises_to_subgoals H' 3| premises_to_subgoals H' 4| premises_to_subgoals H' 5| premises_to_subgoals H' 6| premises_to_subgoals H' 7| premises_to_subgoals H' 8| premises_to_subgoals H' 9]; 
        clear H' 
  | _ => let ty_hyp := type of H in 
       match ty_hyp with 
       | forall (x: ?T), ?rest => let y := fresh "y" in 
                           evar (y: T); specialize (H ?y); qvar_to_evar H (n-1); clear y 
       end 
  end.

Ltac as_apply H' := unshelve( 
  intros; asimpl; 
  let H := fresh "H" in 
  pose proof H' as H; 
  asimpl in H; 
  first [ qvar_to_evar H 0| qvar_to_evar H 1| qvar_to_evar H 2| qvar_to_evar H 3| qvar_to_evar H 4| qvar_to_evar H 5| qvar_to_evar H 6| qvar_to_evar H 7| qvar_to_evar H 8| qvar_to_evar H 9| qvar_to_evar H 10| qvar_to_evar H 11| qvar_to_evar H 12| qvar_to_evar H 13| qvar_to_evar H 14| qvar_to_evar H 15]).
