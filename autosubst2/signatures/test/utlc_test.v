Require Export fintype.



Section tm.
Inductive tm (ntm : nat) : Type :=
  | var_tm : (fin) (ntm) -> tm (ntm)
  | app : tm  (ntm) -> tm  (ntm) -> tm (ntm)
  | lam1 : tm  ((S) ntm) -> tm (ntm)
  | lam2 : forall (p : nat), tm  (p + ((S) ((S) ntm))) -> tm (ntm)
  | lam3 : forall (p : nat), tm  ((S) ((S) (p + ntm))) -> tm (ntm)
  | lam4 : forall (p : nat) (q : nat), tm  (p + ((S) (q + ntm))) -> tm (ntm).

Lemma congr_app { mtm : nat } { s0 : tm  (mtm) } { s1 : tm  (mtm) } { t0 : tm  (mtm) } { t1 : tm  (mtm) } (H1 : s0 = t0) (H2 : s1 = t1) : app (mtm) s0 s1 = app (mtm) t0 t1 .
Proof. congruence. Qed.

Lemma congr_lam1 { mtm : nat } { s0 : tm  ((S) mtm) } { t0 : tm  ((S) mtm) } (H1 : s0 = t0) : lam1 (mtm) s0 = lam1 (mtm) t0 .
Proof. congruence. Qed.

Lemma congr_lam2 { p : nat } { mtm : nat } { s0 : tm  (p + ((S) ((S) mtm))) } { t0 : tm  (p + ((S) ((S) mtm))) } (H1 : s0 = t0) : lam2 (mtm) p s0 = lam2 (mtm) p t0 .
Proof. congruence. Qed.

Lemma congr_lam3 { p : nat } { mtm : nat } { s0 : tm  ((S) ((S) (p + mtm))) } { t0 : tm  ((S) ((S) (p + mtm))) } (H1 : s0 = t0) : lam3 (mtm) p s0 = lam3 (mtm) p t0 .
Proof. congruence. Qed.

Lemma congr_lam4 { p : nat } { q : nat } { mtm : nat } { s0 : tm  (p + ((S) (q + mtm))) } { t0 : tm  (p + ((S) (q + mtm))) } (H1 : s0 = t0) : lam4 (mtm) p q s0 = lam4 (mtm) p q t0 .
Proof. congruence. Qed.

Definition upRen_tm_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Definition upRenList_tm_tm (p : nat) { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (p + (m)) -> (fin) (p + (n)) :=
  upRen_p p xi.

Fixpoint ren_tm { mtm : nat } { ntm : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (s : tm (mtm)) : tm (ntm) :=
    match s return tm (ntm) with
    | var_tm (_) s => (var_tm (ntm)) (xitm s)
    | app (_) s0 s1 => app (ntm) ((ren_tm xitm) s0) ((ren_tm xitm) s1)
    | lam1 (_) s0 => lam1 (ntm) ((ren_tm (upRen_tm_tm xitm)) s0)
    | lam2 (_) p s0 => lam2 (ntm) p ((ren_tm (upRenList_tm_tm p (upRen_tm_tm (upRen_tm_tm xitm)))) s0)
    | lam3 (_) p s0 => lam3 (ntm) p ((ren_tm (upRen_tm_tm (upRen_tm_tm (upRenList_tm_tm p xitm)))) s0)
    | lam4 (_) p q s0 => lam4 (ntm) p q ((ren_tm (upRenList_tm_tm p (upRen_tm_tm (upRenList_tm_tm q xitm)))) s0)
    end.

Definition up_tm_tm { m : nat } { ntm : nat } (sigma : (fin) (m) -> tm (ntm)) : (fin) ((S) (m)) -> tm ((S) ntm) :=
  (scons) ((var_tm ((S) ntm)) (var_zero)) ((funcomp) (ren_tm (shift)) sigma).

Definition upList_tm_tm (p : nat) { m : nat } { ntm : nat } (sigma : (fin) (m) -> tm (ntm)) : (fin) (p + (m)) -> tm (p + ntm) :=
  scons_p  p ((funcomp) (var_tm (p + ntm)) (zero_p p)) ((funcomp) (ren_tm (shift_p p)) sigma).

Fixpoint subst_tm { mtm : nat } { ntm : nat } (sigmatm : (fin) (mtm) -> tm (ntm)) (s : tm (mtm)) : tm (ntm) :=
    match s return tm (ntm) with
    | var_tm (_) s => sigmatm s
    | app (_) s0 s1 => app (ntm) ((subst_tm sigmatm) s0) ((subst_tm sigmatm) s1)
    | lam1 (_) s0 => lam1 (ntm) ((subst_tm (up_tm_tm sigmatm)) s0)
    | lam2 (_) p s0 => lam2 (ntm) p ((subst_tm (upList_tm_tm p (up_tm_tm (up_tm_tm sigmatm)))) s0)
    | lam3 (_) p s0 => lam3 (ntm) p ((subst_tm (up_tm_tm (up_tm_tm (upList_tm_tm p sigmatm)))) s0)
    | lam4 (_) p q s0 => lam4 (ntm) p q ((subst_tm (upList_tm_tm p (up_tm_tm (upList_tm_tm q sigmatm)))) s0)
    end.

Definition upId_tm_tm { mtm : nat } (sigma : (fin) (mtm) -> tm (mtm)) (Eq : forall x, sigma x = (var_tm (mtm)) x) : forall x, (up_tm_tm sigma) x = (var_tm ((S) mtm)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Definition upIdList_tm_tm { p : nat } { mtm : nat } (sigma : (fin) (mtm) -> tm (mtm)) (Eq : forall x, sigma x = (var_tm (mtm)) x) : forall x, (upList_tm_tm p sigma) x = (var_tm (p + mtm)) x :=
  fun n => scons_p_eta (var_tm (p + mtm)) (fun n => (ap) (ren_tm (shift_p p)) (Eq n)) (fun n => eq_refl).

Fixpoint idSubst_tm { mtm : nat } (sigmatm : (fin) (mtm) -> tm (mtm)) (Eqtm : forall x, sigmatm x = (var_tm (mtm)) x) (s : tm (mtm)) : subst_tm sigmatm s = s :=
    match s return subst_tm sigmatm s = s with
    | var_tm (_) s => Eqtm s
    | app (_) s0 s1 => congr_app ((idSubst_tm sigmatm Eqtm) s0) ((idSubst_tm sigmatm Eqtm) s1)
    | lam1 (_) s0 => congr_lam1 ((idSubst_tm (up_tm_tm sigmatm) (upId_tm_tm (_) Eqtm)) s0)
    | lam2 (_) p s0 => congr_lam2 ((idSubst_tm (upList_tm_tm p (up_tm_tm (up_tm_tm sigmatm))) (upIdList_tm_tm (_) (upId_tm_tm (_) (upId_tm_tm (_) Eqtm)))) s0)
    | lam3 (_) p s0 => congr_lam3 ((idSubst_tm (up_tm_tm (up_tm_tm (upList_tm_tm p sigmatm))) (upId_tm_tm (_) (upId_tm_tm (_) (upIdList_tm_tm (_) Eqtm)))) s0)
    | lam4 (_) p q s0 => congr_lam4 ((idSubst_tm (upList_tm_tm p (up_tm_tm (upList_tm_tm q sigmatm))) (upIdList_tm_tm (_) (upId_tm_tm (_) (upIdList_tm_tm (_) Eqtm)))) s0)
    end.

Definition upExtRen_tm_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_tm_tm xi) x = (upRen_tm_tm zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Definition upExtRen_list_tm_tm { p : nat } { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRenList_tm_tm p xi) x = (upRenList_tm_tm p zeta) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (shift_p p) (Eq n)).

Fixpoint extRen_tm { mtm : nat } { ntm : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (zetatm : (fin) (mtm) -> (fin) (ntm)) (Eqtm : forall x, xitm x = zetatm x) (s : tm (mtm)) : ren_tm xitm s = ren_tm zetatm s :=
    match s return ren_tm xitm s = ren_tm zetatm s with
    | var_tm (_) s => (ap) (var_tm (ntm)) (Eqtm s)
    | app (_) s0 s1 => congr_app ((extRen_tm xitm zetatm Eqtm) s0) ((extRen_tm xitm zetatm Eqtm) s1)
    | lam1 (_) s0 => congr_lam1 ((extRen_tm (upRen_tm_tm xitm) (upRen_tm_tm zetatm) (upExtRen_tm_tm (_) (_) Eqtm)) s0)
    | lam2 (_) p s0 => congr_lam2 ((extRen_tm (upRenList_tm_tm p (upRen_tm_tm (upRen_tm_tm xitm))) (upRenList_tm_tm p (upRen_tm_tm (upRen_tm_tm zetatm))) (upExtRen_list_tm_tm (_) (_) (upExtRen_tm_tm (_) (_) (upExtRen_tm_tm (_) (_) Eqtm)))) s0)
    | lam3 (_) p s0 => congr_lam3 ((extRen_tm (upRen_tm_tm (upRen_tm_tm (upRenList_tm_tm p xitm))) (upRen_tm_tm (upRen_tm_tm (upRenList_tm_tm p zetatm))) (upExtRen_tm_tm (_) (_) (upExtRen_tm_tm (_) (_) (upExtRen_list_tm_tm (_) (_) Eqtm)))) s0)
    | lam4 (_) p q s0 => congr_lam4 ((extRen_tm (upRenList_tm_tm p (upRen_tm_tm (upRenList_tm_tm q xitm))) (upRenList_tm_tm p (upRen_tm_tm (upRenList_tm_tm q zetatm))) (upExtRen_list_tm_tm (_) (_) (upExtRen_tm_tm (_) (_) (upExtRen_list_tm_tm (_) (_) Eqtm)))) s0)
    end.

Definition upExt_tm_tm { m : nat } { ntm : nat } (sigma : (fin) (m) -> tm (ntm)) (tau : (fin) (m) -> tm (ntm)) (Eq : forall x, sigma x = tau x) : forall x, (up_tm_tm sigma) x = (up_tm_tm tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Definition upExt_list_tm_tm { p : nat } { m : nat } { ntm : nat } (sigma : (fin) (m) -> tm (ntm)) (tau : (fin) (m) -> tm (ntm)) (Eq : forall x, sigma x = tau x) : forall x, (upList_tm_tm p sigma) x = (upList_tm_tm p tau) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (ren_tm (shift_p p)) (Eq n)).

Fixpoint ext_tm { mtm : nat } { ntm : nat } (sigmatm : (fin) (mtm) -> tm (ntm)) (tautm : (fin) (mtm) -> tm (ntm)) (Eqtm : forall x, sigmatm x = tautm x) (s : tm (mtm)) : subst_tm sigmatm s = subst_tm tautm s :=
    match s return subst_tm sigmatm s = subst_tm tautm s with
    | var_tm (_) s => Eqtm s
    | app (_) s0 s1 => congr_app ((ext_tm sigmatm tautm Eqtm) s0) ((ext_tm sigmatm tautm Eqtm) s1)
    | lam1 (_) s0 => congr_lam1 ((ext_tm (up_tm_tm sigmatm) (up_tm_tm tautm) (upExt_tm_tm (_) (_) Eqtm)) s0)
    | lam2 (_) p s0 => congr_lam2 ((ext_tm (upList_tm_tm p (up_tm_tm (up_tm_tm sigmatm))) (upList_tm_tm p (up_tm_tm (up_tm_tm tautm))) (upExt_list_tm_tm (_) (_) (upExt_tm_tm (_) (_) (upExt_tm_tm (_) (_) Eqtm)))) s0)
    | lam3 (_) p s0 => congr_lam3 ((ext_tm (up_tm_tm (up_tm_tm (upList_tm_tm p sigmatm))) (up_tm_tm (up_tm_tm (upList_tm_tm p tautm))) (upExt_tm_tm (_) (_) (upExt_tm_tm (_) (_) (upExt_list_tm_tm (_) (_) Eqtm)))) s0)
    | lam4 (_) p q s0 => congr_lam4 ((ext_tm (upList_tm_tm p (up_tm_tm (upList_tm_tm q sigmatm))) (upList_tm_tm p (up_tm_tm (upList_tm_tm q tautm))) (upExt_list_tm_tm (_) (_) (upExt_tm_tm (_) (_) (upExt_list_tm_tm (_) (_) Eqtm)))) s0)
    end.

Definition up_ren_ren_tm_tm { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_tm_tm tau) (upRen_tm_tm xi)) x = (upRen_tm_tm theta) x :=
  up_ren_ren xi tau theta Eq.

Definition up_ren_ren_list_tm_tm { p : nat } { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRenList_tm_tm p tau) (upRenList_tm_tm p xi)) x = (upRenList_tm_tm p theta) x :=
  up_ren_ren_p Eq.

Fixpoint compRenRen_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (rhotm : (fin) (mtm) -> (fin) (ltm)) (Eqtm : forall x, ((funcomp) zetatm xitm) x = rhotm x) (s : tm (mtm)) : ren_tm zetatm (ren_tm xitm s) = ren_tm rhotm s :=
    match s return ren_tm zetatm (ren_tm xitm s) = ren_tm rhotm s with
    | var_tm (_) s => (ap) (var_tm (ltm)) (Eqtm s)
    | app (_) s0 s1 => congr_app ((compRenRen_tm xitm zetatm rhotm Eqtm) s0) ((compRenRen_tm xitm zetatm rhotm Eqtm) s1)
    | lam1 (_) s0 => congr_lam1 ((compRenRen_tm (upRen_tm_tm xitm) (upRen_tm_tm zetatm) (upRen_tm_tm rhotm) (up_ren_ren (_) (_) (_) Eqtm)) s0)
    | lam2 (_) p s0 => congr_lam2 ((compRenRen_tm (upRenList_tm_tm p (upRen_tm_tm (upRen_tm_tm xitm))) (upRenList_tm_tm p (upRen_tm_tm (upRen_tm_tm zetatm))) (upRenList_tm_tm p (upRen_tm_tm (upRen_tm_tm rhotm))) (up_ren_ren_p (up_ren_ren (_) (_) (_) (up_ren_ren (_) (_) (_) Eqtm)))) s0)
    | lam3 (_) p s0 => congr_lam3 ((compRenRen_tm (upRen_tm_tm (upRen_tm_tm (upRenList_tm_tm p xitm))) (upRen_tm_tm (upRen_tm_tm (upRenList_tm_tm p zetatm))) (upRen_tm_tm (upRen_tm_tm (upRenList_tm_tm p rhotm))) (up_ren_ren (_) (_) (_) (up_ren_ren (_) (_) (_) (up_ren_ren_p Eqtm)))) s0)
    | lam4 (_) p q s0 => congr_lam4 ((compRenRen_tm (upRenList_tm_tm p (upRen_tm_tm (upRenList_tm_tm q xitm))) (upRenList_tm_tm p (upRen_tm_tm (upRenList_tm_tm q zetatm))) (upRenList_tm_tm p (upRen_tm_tm (upRenList_tm_tm q rhotm))) (up_ren_ren_p (up_ren_ren (_) (_) (_) (up_ren_ren_p Eqtm)))) s0)
    end.

Definition up_ren_subst_tm_tm { k : nat } { l : nat } { mtm : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> tm (mtm)) (theta : (fin) (k) -> tm (mtm)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_tm_tm tau) (upRen_tm_tm xi)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Definition up_ren_subst_list_tm_tm { p : nat } { k : nat } { l : nat } { mtm : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> tm (mtm)) (theta : (fin) (k) -> tm (mtm)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upList_tm_tm p tau) (upRenList_tm_tm p xi)) x = (upList_tm_tm p theta) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (_) n) (scons_p_congr (fun z => scons_p_head' (_) (_) z) (fun z => (eq_trans) (scons_p_tail' (_) (_) (xi z)) ((ap) (ren_tm (shift_p p)) (Eq z)))).

Fixpoint compRenSubst_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (tautm : (fin) (ktm) -> tm (ltm)) (thetatm : (fin) (mtm) -> tm (ltm)) (Eqtm : forall x, ((funcomp) tautm xitm) x = thetatm x) (s : tm (mtm)) : subst_tm tautm (ren_tm xitm s) = subst_tm thetatm s :=
    match s return subst_tm tautm (ren_tm xitm s) = subst_tm thetatm s with
    | var_tm (_) s => Eqtm s
    | app (_) s0 s1 => congr_app ((compRenSubst_tm xitm tautm thetatm Eqtm) s0) ((compRenSubst_tm xitm tautm thetatm Eqtm) s1)
    | lam1 (_) s0 => congr_lam1 ((compRenSubst_tm (upRen_tm_tm xitm) (up_tm_tm tautm) (up_tm_tm thetatm) (up_ren_subst_tm_tm (_) (_) (_) Eqtm)) s0)
    | lam2 (_) p s0 => congr_lam2 ((compRenSubst_tm (upRenList_tm_tm p (upRen_tm_tm (upRen_tm_tm xitm))) (upList_tm_tm p (up_tm_tm (up_tm_tm tautm))) (upList_tm_tm p (up_tm_tm (up_tm_tm thetatm))) (up_ren_subst_list_tm_tm (_) (_) (_) (up_ren_subst_tm_tm (_) (_) (_) (up_ren_subst_tm_tm (_) (_) (_) Eqtm)))) s0)
    | lam3 (_) p s0 => congr_lam3 ((compRenSubst_tm (upRen_tm_tm (upRen_tm_tm (upRenList_tm_tm p xitm))) (up_tm_tm (up_tm_tm (upList_tm_tm p tautm))) (up_tm_tm (up_tm_tm (upList_tm_tm p thetatm))) (up_ren_subst_tm_tm (_) (_) (_) (up_ren_subst_tm_tm (_) (_) (_) (up_ren_subst_list_tm_tm (_) (_) (_) Eqtm)))) s0)
    | lam4 (_) p q s0 => congr_lam4 ((compRenSubst_tm (upRenList_tm_tm p (upRen_tm_tm (upRenList_tm_tm q xitm))) (upList_tm_tm p (up_tm_tm (upList_tm_tm q tautm))) (upList_tm_tm p (up_tm_tm (upList_tm_tm q thetatm))) (up_ren_subst_list_tm_tm (_) (_) (_) (up_ren_subst_tm_tm (_) (_) (_) (up_ren_subst_list_tm_tm (_) (_) (_) Eqtm)))) s0)
    end.

Definition up_subst_ren_tm_tm { k : nat } { ltm : nat } { mtm : nat } (sigma : (fin) (k) -> tm (ltm)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (theta : (fin) (k) -> tm (mtm)) (Eq : forall x, ((funcomp) (ren_tm zetatm) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRen_tm_tm zetatm)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_tm (shift) (upRen_tm_tm zetatm) ((funcomp) (shift) zetatm) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetatm (shift) ((funcomp) (shift) zetatm) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_tm (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Definition up_subst_ren_list_tm_tm { p : nat } { k : nat } { ltm : nat } { mtm : nat } (sigma : (fin) (k) -> tm (ltm)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (theta : (fin) (k) -> tm (mtm)) (Eq : forall x, ((funcomp) (ren_tm zetatm) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRenList_tm_tm p zetatm)) (upList_tm_tm p sigma)) x = (upList_tm_tm p theta) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (_) n) (scons_p_congr (fun x => (ap) (var_tm (p + mtm)) (scons_p_head' (_) (_) x)) (fun n => (eq_trans) (compRenRen_tm (shift_p p) (upRenList_tm_tm p zetatm) ((funcomp) (shift_p p) zetatm) (fun x => scons_p_tail' (_) (_) x) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetatm (shift_p p) ((funcomp) (shift_p p) zetatm) (fun x => eq_refl) (sigma n))) ((ap) (ren_tm (shift_p p)) (Eq n))))).

Fixpoint compSubstRen_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : (fin) (mtm) -> tm (ktm)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (thetatm : (fin) (mtm) -> tm (ltm)) (Eqtm : forall x, ((funcomp) (ren_tm zetatm) sigmatm) x = thetatm x) (s : tm (mtm)) : ren_tm zetatm (subst_tm sigmatm s) = subst_tm thetatm s :=
    match s return ren_tm zetatm (subst_tm sigmatm s) = subst_tm thetatm s with
    | var_tm (_) s => Eqtm s
    | app (_) s0 s1 => congr_app ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s0) ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s1)
    | lam1 (_) s0 => congr_lam1 ((compSubstRen_tm (up_tm_tm sigmatm) (upRen_tm_tm zetatm) (up_tm_tm thetatm) (up_subst_ren_tm_tm (_) (_) (_) Eqtm)) s0)
    | lam2 (_) p s0 => congr_lam2 ((compSubstRen_tm (upList_tm_tm p (up_tm_tm (up_tm_tm sigmatm))) (upRenList_tm_tm p (upRen_tm_tm (upRen_tm_tm zetatm))) (upList_tm_tm p (up_tm_tm (up_tm_tm thetatm))) (up_subst_ren_list_tm_tm (_) (_) (_) (up_subst_ren_tm_tm (_) (_) (_) (up_subst_ren_tm_tm (_) (_) (_) Eqtm)))) s0)
    | lam3 (_) p s0 => congr_lam3 ((compSubstRen_tm (up_tm_tm (up_tm_tm (upList_tm_tm p sigmatm))) (upRen_tm_tm (upRen_tm_tm (upRenList_tm_tm p zetatm))) (up_tm_tm (up_tm_tm (upList_tm_tm p thetatm))) (up_subst_ren_tm_tm (_) (_) (_) (up_subst_ren_tm_tm (_) (_) (_) (up_subst_ren_list_tm_tm (_) (_) (_) Eqtm)))) s0)
    | lam4 (_) p q s0 => congr_lam4 ((compSubstRen_tm (upList_tm_tm p (up_tm_tm (upList_tm_tm q sigmatm))) (upRenList_tm_tm p (upRen_tm_tm (upRenList_tm_tm q zetatm))) (upList_tm_tm p (up_tm_tm (upList_tm_tm q thetatm))) (up_subst_ren_list_tm_tm (_) (_) (_) (up_subst_ren_tm_tm (_) (_) (_) (up_subst_ren_list_tm_tm (_) (_) (_) Eqtm)))) s0)
    end.

Definition up_subst_subst_tm_tm { k : nat } { ltm : nat } { mtm : nat } (sigma : (fin) (k) -> tm (ltm)) (tautm : (fin) (ltm) -> tm (mtm)) (theta : (fin) (k) -> tm (mtm)) (Eq : forall x, ((funcomp) (subst_tm tautm) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (up_tm_tm tautm)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_tm (shift) (up_tm_tm tautm) ((funcomp) (up_tm_tm tautm) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tautm (shift) ((funcomp) (ren_tm (shift)) tautm) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_tm (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Definition up_subst_subst_list_tm_tm { p : nat } { k : nat } { ltm : nat } { mtm : nat } (sigma : (fin) (k) -> tm (ltm)) (tautm : (fin) (ltm) -> tm (mtm)) (theta : (fin) (k) -> tm (mtm)) (Eq : forall x, ((funcomp) (subst_tm tautm) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (upList_tm_tm p tautm)) (upList_tm_tm p sigma)) x = (upList_tm_tm p theta) x :=
  fun n => (eq_trans) (scons_p_comp' ((funcomp) (var_tm (p + ltm)) (zero_p p)) (_) (_) n) (scons_p_congr (fun x => scons_p_head' (_) (fun z => ren_tm (shift_p p) (_)) x) (fun n => (eq_trans) (compRenSubst_tm (shift_p p) (upList_tm_tm p tautm) ((funcomp) (upList_tm_tm p tautm) (shift_p p)) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tautm (shift_p p) (_) (fun x => (eq_sym) (scons_p_tail' (_) (_) x)) (sigma n))) ((ap) (ren_tm (shift_p p)) (Eq n))))).

Fixpoint compSubstSubst_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : (fin) (mtm) -> tm (ktm)) (tautm : (fin) (ktm) -> tm (ltm)) (thetatm : (fin) (mtm) -> tm (ltm)) (Eqtm : forall x, ((funcomp) (subst_tm tautm) sigmatm) x = thetatm x) (s : tm (mtm)) : subst_tm tautm (subst_tm sigmatm s) = subst_tm thetatm s :=
    match s return subst_tm tautm (subst_tm sigmatm s) = subst_tm thetatm s with
    | var_tm (_) s => Eqtm s
    | app (_) s0 s1 => congr_app ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s0) ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s1)
    | lam1 (_) s0 => congr_lam1 ((compSubstSubst_tm (up_tm_tm sigmatm) (up_tm_tm tautm) (up_tm_tm thetatm) (up_subst_subst_tm_tm (_) (_) (_) Eqtm)) s0)
    | lam2 (_) p s0 => congr_lam2 ((compSubstSubst_tm (upList_tm_tm p (up_tm_tm (up_tm_tm sigmatm))) (upList_tm_tm p (up_tm_tm (up_tm_tm tautm))) (upList_tm_tm p (up_tm_tm (up_tm_tm thetatm))) (up_subst_subst_list_tm_tm (_) (_) (_) (up_subst_subst_tm_tm (_) (_) (_) (up_subst_subst_tm_tm (_) (_) (_) Eqtm)))) s0)
    | lam3 (_) p s0 => congr_lam3 ((compSubstSubst_tm (up_tm_tm (up_tm_tm (upList_tm_tm p sigmatm))) (up_tm_tm (up_tm_tm (upList_tm_tm p tautm))) (up_tm_tm (up_tm_tm (upList_tm_tm p thetatm))) (up_subst_subst_tm_tm (_) (_) (_) (up_subst_subst_tm_tm (_) (_) (_) (up_subst_subst_list_tm_tm (_) (_) (_) Eqtm)))) s0)
    | lam4 (_) p q s0 => congr_lam4 ((compSubstSubst_tm (upList_tm_tm p (up_tm_tm (upList_tm_tm q sigmatm))) (upList_tm_tm p (up_tm_tm (upList_tm_tm q tautm))) (upList_tm_tm p (up_tm_tm (upList_tm_tm q thetatm))) (up_subst_subst_list_tm_tm (_) (_) (_) (up_subst_subst_tm_tm (_) (_) (_) (up_subst_subst_list_tm_tm (_) (_) (_) Eqtm)))) s0)
    end.

Definition rinstInst_up_tm_tm { m : nat } { ntm : nat } (xi : (fin) (m) -> (fin) (ntm)) (sigma : (fin) (m) -> tm (ntm)) (Eq : forall x, ((funcomp) (var_tm (ntm)) xi) x = sigma x) : forall x, ((funcomp) (var_tm ((S) ntm)) (upRen_tm_tm xi)) x = (up_tm_tm sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Definition rinstInst_up_list_tm_tm { p : nat } { m : nat } { ntm : nat } (xi : (fin) (m) -> (fin) (ntm)) (sigma : (fin) (m) -> tm (ntm)) (Eq : forall x, ((funcomp) (var_tm (ntm)) xi) x = sigma x) : forall x, ((funcomp) (var_tm (p + ntm)) (upRenList_tm_tm p xi)) x = (upList_tm_tm p sigma) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (var_tm (p + ntm)) n) (scons_p_congr (fun z => eq_refl) (fun n => (ap) (ren_tm (shift_p p)) (Eq n))).

Fixpoint rinst_inst_tm { mtm : nat } { ntm : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (sigmatm : (fin) (mtm) -> tm (ntm)) (Eqtm : forall x, ((funcomp) (var_tm (ntm)) xitm) x = sigmatm x) (s : tm (mtm)) : ren_tm xitm s = subst_tm sigmatm s :=
    match s return ren_tm xitm s = subst_tm sigmatm s with
    | var_tm (_) s => Eqtm s
    | app (_) s0 s1 => congr_app ((rinst_inst_tm xitm sigmatm Eqtm) s0) ((rinst_inst_tm xitm sigmatm Eqtm) s1)
    | lam1 (_) s0 => congr_lam1 ((rinst_inst_tm (upRen_tm_tm xitm) (up_tm_tm sigmatm) (rinstInst_up_tm_tm (_) (_) Eqtm)) s0)
    | lam2 (_) p s0 => congr_lam2 ((rinst_inst_tm (upRenList_tm_tm p (upRen_tm_tm (upRen_tm_tm xitm))) (upList_tm_tm p (up_tm_tm (up_tm_tm sigmatm))) (rinstInst_up_list_tm_tm (_) (_) (rinstInst_up_tm_tm (_) (_) (rinstInst_up_tm_tm (_) (_) Eqtm)))) s0)
    | lam3 (_) p s0 => congr_lam3 ((rinst_inst_tm (upRen_tm_tm (upRen_tm_tm (upRenList_tm_tm p xitm))) (up_tm_tm (up_tm_tm (upList_tm_tm p sigmatm))) (rinstInst_up_tm_tm (_) (_) (rinstInst_up_tm_tm (_) (_) (rinstInst_up_list_tm_tm (_) (_) Eqtm)))) s0)
    | lam4 (_) p q s0 => congr_lam4 ((rinst_inst_tm (upRenList_tm_tm p (upRen_tm_tm (upRenList_tm_tm q xitm))) (upList_tm_tm p (up_tm_tm (upList_tm_tm q sigmatm))) (rinstInst_up_list_tm_tm (_) (_) (rinstInst_up_tm_tm (_) (_) (rinstInst_up_list_tm_tm (_) (_) Eqtm)))) s0)
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

Arguments lam1 {ntm}.

Arguments lam2 {ntm}.

Arguments lam3 {ntm}.

Arguments lam4 {ntm}.

Global Instance Subst_tm { mtm : nat } { ntm : nat } : Subst1 ((fin) (mtm) -> tm (ntm)) (tm (mtm)) (tm (ntm)) := @subst_tm (mtm) (ntm) .

Global Instance Ren_tm { mtm : nat } { ntm : nat } : Ren1 ((fin) (mtm) -> (fin) (ntm)) (tm (mtm)) (tm (ntm)) := @ren_tm (mtm) (ntm) .

Global Instance VarInstance_tm { mtm : nat } : Var ((fin) (mtm)) (tm (mtm)) := @var_tm (mtm) .

Notation "x '__tm'" := (var_tm x) (at level 5, format "x __tm") : subst_scope.

Notation "x '__tm'" := (@ids (_) (_) VarInstance_tm x) (at level 5, only printing, format "x __tm") : subst_scope.

Notation "'var'" := (var_tm) (only printing, at level 1) : subst_scope.

Class Up_tm X Y := up_tm : X -> Y.

Notation "↑__tm" := (up_tm) (only printing) : subst_scope.

Notation "↑__tm" := (up_tm_tm) (only printing) : subst_scope.

Global Instance Up_tm_tm { m : nat } { ntm : nat } : Up_tm (_) (_) := @up_tm_tm (m) (ntm) .

Notation "s [ sigmatm ]" := (subst_tm sigmatm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmatm ]" := (subst_tm sigmatm) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xitm ⟩" := (ren_tm xitm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xitm ⟩" := (ren_tm xitm) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_tm,  Ren_tm,  VarInstance_tm.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_tm,  Ren_tm,  VarInstance_tm in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_tm| progress rewrite ?compComp_tm| progress rewrite ?compComp'_tm| progress rewrite ?rinstId_tm| progress rewrite ?compRen_tm| progress rewrite ?compRen'_tm| progress rewrite ?renComp_tm| progress rewrite ?renComp'_tm| progress rewrite ?renRen_tm| progress rewrite ?renRen'_tm| progress rewrite ?varL_tm| progress rewrite ?varLRen_tm| progress (unfold up_ren, upRen_tm_tm, upRenList_tm_tm, upRenList_tm_tm, up_tm_tm, upList_tm_tm, upList_tm_tm)| progress (cbn [subst_tm ren_tm])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_tm in *| progress rewrite ?compComp_tm in *| progress rewrite ?compComp'_tm in *| progress rewrite ?rinstId_tm in *| progress rewrite ?compRen_tm in *| progress rewrite ?compRen'_tm in *| progress rewrite ?renComp_tm in *| progress rewrite ?renComp'_tm in *| progress rewrite ?renRen_tm in *| progress rewrite ?renRen'_tm in *| progress rewrite ?varL_tm in *| progress rewrite ?varLRen_tm in *| progress (unfold up_ren, upRen_tm_tm, upRenList_tm_tm, upRenList_tm_tm, up_tm_tm, upList_tm_tm, upList_tm_tm in *)| progress (cbn [subst_tm ren_tm] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_tm).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_tm).

(** as_apply follows **)

Ltac  musigma gexp hexp :=
  match   gexp  with
  |  ?s  =>  unify   (gexp) (hexp)
  |  app (subst_tm ?sigma0 ?s0) (subst_tm ?sigma0 ?s1)  =>  first [ unify   (subst_tm sigma0 (app s0 s1)) (hexp)|  musigma   (subst_tm sigma0 (app s0 s1)) (hexp) ]
  |  lam1 (subst_tm ((scons) (var_tm (var_zero)) ((funcomp) (ren_tm (shift)) ?sigma0)) ?s0)  =>  first [ unify   (subst_tm sigma0 (lam1 s0)) (hexp)|  musigma   (subst_tm sigma0 (lam1 s0)) (hexp) ]
  |  lam2 ?p (subst_tm (scons_p ?p ((funcomp) var_tm (zero_p ?p)) ((scons) (var_tm (shift_p ?p (var_zero))) ((scons) (var_tm (shift_p ?p ((shift) (var_zero)))) ((funcomp) (ren_tm ((funcomp) ((funcomp) (shift_p ?p) (shift)) (shift))) ?sigma0)))) ?s0)  =>  first [ unify   (subst_tm sigma0 (lam2 p s0)) (hexp)|  musigma   (subst_tm sigma0 (lam2 p s0)) (hexp) ]
  |  lam3 ?p (subst_tm ((scons) (var_tm (var_zero)) ((scons) (var_tm ((shift) (var_zero))) (scons_p ?p ((funcomp) ((funcomp) ((funcomp) var_tm (shift)) (shift)) (zero_p ?p)) ((funcomp) (ren_tm ((funcomp) ((funcomp) (shift) (shift)) (shift_p ?p))) ?sigma0)))) ?s0)  =>  first [ unify   (subst_tm sigma0 (lam3 p s0)) (hexp)|  musigma   (subst_tm sigma0 (lam3 p s0)) (hexp) ]
  |  lam4 ?p ?q (subst_tm (scons_p ?p ((funcomp) var_tm (zero_p ?p)) ((scons) (var_tm (shift_p ?p (var_zero))) (scons_p ?q ((funcomp) ((funcomp) ((funcomp) var_tm (shift_p ?p)) (shift)) (zero_p ?q)) ((funcomp) (ren_tm ((funcomp) ((funcomp) (shift_p ?p) (shift)) (shift_p ?q))) ?sigma0)))) ?s0)  =>  first [ unify   (subst_tm sigma0 (lam4 p q s0)) (hexp)|  musigma   (subst_tm sigma0 (lam4 p q s0)) (hexp) ]
  |  app (ren_tm ?sigma0 ?s0) (ren_tm ?sigma0 ?s1)  =>  first [ unify   (ren_tm sigma0 (app s0 s1)) (hexp)|  musigma   (ren_tm sigma0 (app s0 s1)) (hexp) ]
  |  lam1 (ren_tm ((scons) (var_zero) ((funcomp) (shift) ?sigma0)) ?s0)  =>  first [ unify   (ren_tm sigma0 (lam1 s0)) (hexp)|  musigma   (ren_tm sigma0 (lam1 s0)) (hexp) ]
  |  lam2 ?p (ren_tm (scons_p ?p (zero_p ?p) ((scons) (shift_p ?p (var_zero)) ((scons) (shift_p ?p ((shift) (var_zero))) ((funcomp) ((funcomp) ((funcomp) (shift) (shift)) (shift_p ?p)) ?sigma0)))) ?s0)  =>  first [ unify   (ren_tm sigma0 (lam2 p s0)) (hexp)|  musigma   (ren_tm sigma0 (lam2 p s0)) (hexp) ]
  |  lam3 ?p (ren_tm ((scons) (var_zero) ((scons) ((shift) (var_zero)) (scons_p ?p ((funcomp) ((funcomp) (shift) (shift)) (zero_p ?p)) ((funcomp) ((shift) ((shift) (shift_p ?p) (shift)) (shift)) ?sigma0)))) ?s0)  =>  first [ unify   (ren_tm sigma0 (lam3 p s0)) (hexp)|  musigma   (ren_tm sigma0 (lam3 p s0)) (hexp) ]
  |  lam4 ?p ?q (ren_tm (scons_p ?p (zero_p ?p) ((scons) (shift_p ?p (var_zero)) (scons_p ?q ((funcomp) ((funcomp) (shift_p ?p) (shift)) (zero_p ?q)) ((funcomp) ((funcomp) ((shift) (shift_p ?q) (shift)) (shift_p ?p)) ?sigma0)))) ?s0)  =>  first [ unify   (ren_tm sigma0 (lam4 p q s0)) (hexp)|  musigma   (ren_tm sigma0 (lam4 p q s0)) (hexp) ]
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
  |  app ?s0 ?s1  =>  match   hexp  with
  |  app ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  lam1 ?s0  =>  match   hexp  with
  |  lam1 ?t0  =>  musigma   (s0) (t0)
  end
  |  lam2 ?p ?s0  =>  match   hexp  with
  |  lam2 ?p_ ?t0  =>  musigma   (p) (p_); musigma   (s0) (t0)
  end
  |  lam3 ?p ?s0  =>  match   hexp  with
  |  lam3 ?p_ ?t0  =>  musigma   (p) (p_); musigma   (s0) (t0)
  end
  |  lam4 ?p ?q ?s0  =>  match   hexp  with
  |  lam4 ?p_ ?q_ ?t0  =>  musigma   (p) (p_); musigma   (q) (q_); musigma   (s0) (t0)
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
  |  subst_tm ((scons) ?stm0 ((funcomp) var_tm ?sigmatm)) ?stm  =>  match   hexp  with
  |  subst_tm ((scons) ?ttm0 var_tm) ?ttm  =>  unify   (subst_tm ((scons) stm0 var_tm) (ren_tm ((scons) (var_zero) ((funcomp) (shift) sigmatm)) stm)) (hexp)
  end
  |  subst_tm (scons_p ?p ?stm2 ((scons) ?stm1 ((scons) ?stm0 ((funcomp) var_tm ?sigmatm)))) ?stm  =>  match   hexp  with
  |  subst_tm (scons_p ?p_ ?ttm2 ((scons) ?ttm1 ((scons) ?ttm0 var_tm))) ?ttm  =>  unify   (subst_tm (scons_p p stm2 ((scons) stm1 ((scons) stm0 var_tm))) (ren_tm (scons_p p (zero_p p) ((scons) (shift_p p (var_zero)) ((scons) (shift_p p ((shift) (var_zero))) ((funcomp) ((funcomp) ((funcomp) (shift) (shift)) (shift_p p)) sigmatm)))) stm)) (hexp)
  end
  |  subst_tm ((scons) ?stm2 ((scons) ?stm1 (scons_p ?p ?stm0 ((funcomp) var_tm ?sigmatm)))) ?stm  =>  match   hexp  with
  |  subst_tm ((scons) ?ttm2 ((scons) ?ttm1 (scons_p ?p_ ?ttm0 var_tm))) ?ttm  =>  unify   (subst_tm ((scons) stm2 ((scons) stm1 (scons_p p stm0 var_tm))) (ren_tm ((scons) (var_zero) ((scons) ((shift) (var_zero)) (scons_p p ((funcomp) ((funcomp) (shift) (shift)) (zero_p p)) ((funcomp) ((shift) ((shift) (shift_p p) (shift)) (shift)) sigmatm)))) stm)) (hexp)
  end
  |  subst_tm (scons_p ?p ?stm2 ((scons) ?stm1 (scons_p ?q ?stm0 ((funcomp) var_tm ?sigmatm)))) ?stm  =>  match   hexp  with
  |  subst_tm (scons_p ?p_ ?ttm2 ((scons) ?ttm1 (scons_p ?q_ ?ttm0 var_tm))) ?ttm  =>  unify   (subst_tm (scons_p p stm2 ((scons) stm1 (scons_p q stm0 var_tm))) (ren_tm (scons_p p (zero_p p) ((scons) (shift_p p (var_zero)) (scons_p q ((funcomp) ((funcomp) (shift_p p) (shift)) (zero_p q)) ((funcomp) ((funcomp) ((shift) (shift_p q) (shift)) (shift_p p)) sigmatm)))) stm)) (hexp)
  end
  |  subst_tm ((scons) ?stm0 ?sigmatm) ?stm  =>  match   hexp  with
  |  subst_tm ((scons) ?ttm0 var_tm) ?ttm  =>  unify   (subst_tm ((scons) stm0 var_tm) (subst_tm ((scons) (var_tm (var_zero)) ((funcomp) (ren_tm (shift)) sigmatm)) stm)) (hexp)
  end
  |  subst_tm (scons_p ?p ?stm2 ((scons) ?stm1 ((scons) ?stm0 ?sigmatm))) ?stm  =>  match   hexp  with
  |  subst_tm (scons_p ?p_ ?ttm2 ((scons) ?ttm1 ((scons) ?ttm0 var_tm))) ?ttm  =>  unify   (subst_tm (scons_p p stm2 ((scons) stm1 ((scons) stm0 var_tm))) (subst_tm (scons_p p ((funcomp) var_tm (zero_p p)) ((scons) (var_tm (shift_p p (var_zero))) ((scons) (var_tm (shift_p p ((shift) (var_zero)))) ((funcomp) (ren_tm ((funcomp) ((funcomp) (shift_p p) (shift)) (shift))) sigmatm)))) stm)) (hexp)
  end
  |  subst_tm ((scons) ?stm2 ((scons) ?stm1 (scons_p ?p ?stm0 ?sigmatm))) ?stm  =>  match   hexp  with
  |  subst_tm ((scons) ?ttm2 ((scons) ?ttm1 (scons_p ?p_ ?ttm0 var_tm))) ?ttm  =>  unify   (subst_tm ((scons) stm2 ((scons) stm1 (scons_p p stm0 var_tm))) (subst_tm ((scons) (var_tm (var_zero)) ((scons) (var_tm ((shift) (var_zero))) (scons_p p ((funcomp) ((funcomp) ((funcomp) var_tm (shift)) (shift)) (zero_p p)) ((funcomp) (ren_tm ((funcomp) ((funcomp) (shift) (shift)) (shift_p p))) sigmatm)))) stm)) (hexp)
  end
  |  subst_tm (scons_p ?p ?stm2 ((scons) ?stm1 (scons_p ?q ?stm0 ?sigmatm))) ?stm  =>  match   hexp  with
  |  subst_tm (scons_p ?p_ ?ttm2 ((scons) ?ttm1 (scons_p ?q_ ?ttm0 var_tm))) ?ttm  =>  unify   (subst_tm (scons_p p stm2 ((scons) stm1 (scons_p q stm0 var_tm))) (subst_tm (scons_p p ((funcomp) var_tm (zero_p p)) ((scons) (var_tm (shift_p p (var_zero))) (scons_p q ((funcomp) ((funcomp) ((funcomp) var_tm (shift_p p)) (shift)) (zero_p q)) ((funcomp) (ren_tm ((funcomp) ((funcomp) (shift_p p) (shift)) (shift_p q))) sigmatm)))) stm)) (hexp)
  end
  |  ?s  =>  match   hexp  with
  |  subst_tm ?sigma0 ?t  =>  unify   (subst_tm var_tm s) (hexp)
  |  ren_tm ?sigma0 ?t  =>  unify   (ren_tm (id) s) (hexp)
  end
  |  app ?s0 ?s1  =>  match   hexp  with
  |  app ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  lam1 ?s0  =>  match   hexp  with
  |  lam1 ?t0  =>  heuristics   (s0) (t0)
  end
  |  lam2 ?p ?s0  =>  match   hexp  with
  |  lam2 ?p_ ?t0  =>  heuristics   (p) (p_); heuristics   (s0) (t0)
  end
  |  lam3 ?p ?s0  =>  match   hexp  with
  |  lam3 ?p_ ?t0  =>  heuristics   (p) (p_); heuristics   (s0) (t0)
  end
  |  lam4 ?p ?q ?s0  =>  match   hexp  with
  |  lam4 ?p_ ?q_ ?t0  =>  heuristics   (p) (p_); heuristics   (q) (q_); heuristics   (s0) (t0)
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
