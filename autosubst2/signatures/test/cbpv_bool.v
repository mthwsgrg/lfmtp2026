Require Export fintype.



Section tmvl.
Inductive tm (nvl : nat) : Type :=
  | lam : tm  ((S) nvl) -> tm (nvl)
  | app : tm  (nvl) -> vl  (nvl) -> tm (nvl)
  | creturn : vl  (nvl) -> tm (nvl)
  | clet : tm  (nvl) -> tm  ((S) nvl) -> tm (nvl)
  | force : vl  (nvl) -> tm (nvl)
  | cif : vl  (nvl) -> tm  (nvl) -> tm  (nvl) -> tm (nvl)
 with vl (nvl : nat) : Type :=
  | var_vl : (fin) (nvl) -> vl (nvl)
  | true : vl (nvl)
  | false : vl (nvl)
  | thunk : tm  (nvl) -> vl (nvl).

Lemma congr_lam { mvl : nat } { s0 : tm  ((S) mvl) } { t0 : tm  ((S) mvl) } (H1 : s0 = t0) : lam (mvl) s0 = lam (mvl) t0 .
Proof. congruence. Qed.

Lemma congr_app { mvl : nat } { s0 : tm  (mvl) } { s1 : vl  (mvl) } { t0 : tm  (mvl) } { t1 : vl  (mvl) } (H1 : s0 = t0) (H2 : s1 = t1) : app (mvl) s0 s1 = app (mvl) t0 t1 .
Proof. congruence. Qed.

Lemma congr_creturn { mvl : nat } { s0 : vl  (mvl) } { t0 : vl  (mvl) } (H1 : s0 = t0) : creturn (mvl) s0 = creturn (mvl) t0 .
Proof. congruence. Qed.

Lemma congr_clet { mvl : nat } { s0 : tm  (mvl) } { s1 : tm  ((S) mvl) } { t0 : tm  (mvl) } { t1 : tm  ((S) mvl) } (H1 : s0 = t0) (H2 : s1 = t1) : clet (mvl) s0 s1 = clet (mvl) t0 t1 .
Proof. congruence. Qed.

Lemma congr_force { mvl : nat } { s0 : vl  (mvl) } { t0 : vl  (mvl) } (H1 : s0 = t0) : force (mvl) s0 = force (mvl) t0 .
Proof. congruence. Qed.

Lemma congr_cif { mvl : nat } { s0 : vl  (mvl) } { s1 : tm  (mvl) } { s2 : tm  (mvl) } { t0 : vl  (mvl) } { t1 : tm  (mvl) } { t2 : tm  (mvl) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : cif (mvl) s0 s1 s2 = cif (mvl) t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_true { mvl : nat } : true (mvl) = true (mvl) .
Proof. congruence. Qed.

Lemma congr_false { mvl : nat } : false (mvl) = false (mvl) .
Proof. congruence. Qed.

Lemma congr_thunk { mvl : nat } { s0 : tm  (mvl) } { t0 : tm  (mvl) } (H1 : s0 = t0) : thunk (mvl) s0 = thunk (mvl) t0 .
Proof. congruence. Qed.

Definition upRen_vl_vl { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Fixpoint ren_tm { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (s : tm (mvl)) : tm (nvl) :=
    match s return tm (nvl) with
    | lam (_) s0 => lam (nvl) ((ren_tm (upRen_vl_vl xivl)) s0)
    | app (_) s0 s1 => app (nvl) ((ren_tm xivl) s0) ((ren_vl xivl) s1)
    | creturn (_) s0 => creturn (nvl) ((ren_vl xivl) s0)
    | clet (_) s0 s1 => clet (nvl) ((ren_tm xivl) s0) ((ren_tm (upRen_vl_vl xivl)) s1)
    | force (_) s0 => force (nvl) ((ren_vl xivl) s0)
    | cif (_) s0 s1 s2 => cif (nvl) ((ren_vl xivl) s0) ((ren_tm xivl) s1) ((ren_tm xivl) s2)
    end
 with ren_vl { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (s : vl (mvl)) : vl (nvl) :=
    match s return vl (nvl) with
    | var_vl (_) s => (var_vl (nvl)) (xivl s)
    | true (_)  => true (nvl)
    | false (_)  => false (nvl)
    | thunk (_) s0 => thunk (nvl) ((ren_tm xivl) s0)
    end.

Definition up_vl_vl { m : nat } { nvl : nat } (sigma : (fin) (m) -> vl (nvl)) : (fin) ((S) (m)) -> vl ((S) nvl) :=
  (scons) ((var_vl ((S) nvl)) (var_zero)) ((funcomp) (ren_vl (shift)) sigma).

Fixpoint subst_tm { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) (s : tm (mvl)) : tm (nvl) :=
    match s return tm (nvl) with
    | lam (_) s0 => lam (nvl) ((subst_tm (up_vl_vl sigmavl)) s0)
    | app (_) s0 s1 => app (nvl) ((subst_tm sigmavl) s0) ((subst_vl sigmavl) s1)
    | creturn (_) s0 => creturn (nvl) ((subst_vl sigmavl) s0)
    | clet (_) s0 s1 => clet (nvl) ((subst_tm sigmavl) s0) ((subst_tm (up_vl_vl sigmavl)) s1)
    | force (_) s0 => force (nvl) ((subst_vl sigmavl) s0)
    | cif (_) s0 s1 s2 => cif (nvl) ((subst_vl sigmavl) s0) ((subst_tm sigmavl) s1) ((subst_tm sigmavl) s2)
    end
 with subst_vl { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) (s : vl (mvl)) : vl (nvl) :=
    match s return vl (nvl) with
    | var_vl (_) s => sigmavl s
    | true (_)  => true (nvl)
    | false (_)  => false (nvl)
    | thunk (_) s0 => thunk (nvl) ((subst_tm sigmavl) s0)
    end.

Definition upId_vl_vl { mvl : nat } (sigma : (fin) (mvl) -> vl (mvl)) (Eq : forall x, sigma x = (var_vl (mvl)) x) : forall x, (up_vl_vl sigma) x = (var_vl ((S) mvl)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_vl (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint idSubst_tm { mvl : nat } (sigmavl : (fin) (mvl) -> vl (mvl)) (Eqvl : forall x, sigmavl x = (var_vl (mvl)) x) (s : tm (mvl)) : subst_tm sigmavl s = s :=
    match s return subst_tm sigmavl s = s with
    | lam (_) s0 => congr_lam ((idSubst_tm (up_vl_vl sigmavl) (upId_vl_vl (_) Eqvl)) s0)
    | app (_) s0 s1 => congr_app ((idSubst_tm sigmavl Eqvl) s0) ((idSubst_vl sigmavl Eqvl) s1)
    | creturn (_) s0 => congr_creturn ((idSubst_vl sigmavl Eqvl) s0)
    | clet (_) s0 s1 => congr_clet ((idSubst_tm sigmavl Eqvl) s0) ((idSubst_tm (up_vl_vl sigmavl) (upId_vl_vl (_) Eqvl)) s1)
    | force (_) s0 => congr_force ((idSubst_vl sigmavl Eqvl) s0)
    | cif (_) s0 s1 s2 => congr_cif ((idSubst_vl sigmavl Eqvl) s0) ((idSubst_tm sigmavl Eqvl) s1) ((idSubst_tm sigmavl Eqvl) s2)
    end
 with idSubst_vl { mvl : nat } (sigmavl : (fin) (mvl) -> vl (mvl)) (Eqvl : forall x, sigmavl x = (var_vl (mvl)) x) (s : vl (mvl)) : subst_vl sigmavl s = s :=
    match s return subst_vl sigmavl s = s with
    | var_vl (_) s => Eqvl s
    | true (_)  => congr_true 
    | false (_)  => congr_false 
    | thunk (_) s0 => congr_thunk ((idSubst_tm sigmavl Eqvl) s0)
    end.

Definition upExtRen_vl_vl { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_vl_vl xi) x = (upRen_vl_vl zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint extRen_tm { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (zetavl : (fin) (mvl) -> (fin) (nvl)) (Eqvl : forall x, xivl x = zetavl x) (s : tm (mvl)) : ren_tm xivl s = ren_tm zetavl s :=
    match s return ren_tm xivl s = ren_tm zetavl s with
    | lam (_) s0 => congr_lam ((extRen_tm (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upExtRen_vl_vl (_) (_) Eqvl)) s0)
    | app (_) s0 s1 => congr_app ((extRen_tm xivl zetavl Eqvl) s0) ((extRen_vl xivl zetavl Eqvl) s1)
    | creturn (_) s0 => congr_creturn ((extRen_vl xivl zetavl Eqvl) s0)
    | clet (_) s0 s1 => congr_clet ((extRen_tm xivl zetavl Eqvl) s0) ((extRen_tm (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upExtRen_vl_vl (_) (_) Eqvl)) s1)
    | force (_) s0 => congr_force ((extRen_vl xivl zetavl Eqvl) s0)
    | cif (_) s0 s1 s2 => congr_cif ((extRen_vl xivl zetavl Eqvl) s0) ((extRen_tm xivl zetavl Eqvl) s1) ((extRen_tm xivl zetavl Eqvl) s2)
    end
 with extRen_vl { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (zetavl : (fin) (mvl) -> (fin) (nvl)) (Eqvl : forall x, xivl x = zetavl x) (s : vl (mvl)) : ren_vl xivl s = ren_vl zetavl s :=
    match s return ren_vl xivl s = ren_vl zetavl s with
    | var_vl (_) s => (ap) (var_vl (nvl)) (Eqvl s)
    | true (_)  => congr_true 
    | false (_)  => congr_false 
    | thunk (_) s0 => congr_thunk ((extRen_tm xivl zetavl Eqvl) s0)
    end.

Definition upExt_vl_vl { m : nat } { nvl : nat } (sigma : (fin) (m) -> vl (nvl)) (tau : (fin) (m) -> vl (nvl)) (Eq : forall x, sigma x = tau x) : forall x, (up_vl_vl sigma) x = (up_vl_vl tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_vl (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint ext_tm { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) (tauvl : (fin) (mvl) -> vl (nvl)) (Eqvl : forall x, sigmavl x = tauvl x) (s : tm (mvl)) : subst_tm sigmavl s = subst_tm tauvl s :=
    match s return subst_tm sigmavl s = subst_tm tauvl s with
    | lam (_) s0 => congr_lam ((ext_tm (up_vl_vl sigmavl) (up_vl_vl tauvl) (upExt_vl_vl (_) (_) Eqvl)) s0)
    | app (_) s0 s1 => congr_app ((ext_tm sigmavl tauvl Eqvl) s0) ((ext_vl sigmavl tauvl Eqvl) s1)
    | creturn (_) s0 => congr_creturn ((ext_vl sigmavl tauvl Eqvl) s0)
    | clet (_) s0 s1 => congr_clet ((ext_tm sigmavl tauvl Eqvl) s0) ((ext_tm (up_vl_vl sigmavl) (up_vl_vl tauvl) (upExt_vl_vl (_) (_) Eqvl)) s1)
    | force (_) s0 => congr_force ((ext_vl sigmavl tauvl Eqvl) s0)
    | cif (_) s0 s1 s2 => congr_cif ((ext_vl sigmavl tauvl Eqvl) s0) ((ext_tm sigmavl tauvl Eqvl) s1) ((ext_tm sigmavl tauvl Eqvl) s2)
    end
 with ext_vl { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) (tauvl : (fin) (mvl) -> vl (nvl)) (Eqvl : forall x, sigmavl x = tauvl x) (s : vl (mvl)) : subst_vl sigmavl s = subst_vl tauvl s :=
    match s return subst_vl sigmavl s = subst_vl tauvl s with
    | var_vl (_) s => Eqvl s
    | true (_)  => congr_true 
    | false (_)  => congr_false 
    | thunk (_) s0 => congr_thunk ((ext_tm sigmavl tauvl Eqvl) s0)
    end.

Definition up_ren_ren_vl_vl { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_vl_vl tau) (upRen_vl_vl xi)) x = (upRen_vl_vl theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_tm { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (rhovl : (fin) (mvl) -> (fin) (lvl)) (Eqvl : forall x, ((funcomp) zetavl xivl) x = rhovl x) (s : tm (mvl)) : ren_tm zetavl (ren_tm xivl s) = ren_tm rhovl s :=
    match s return ren_tm zetavl (ren_tm xivl s) = ren_tm rhovl s with
    | lam (_) s0 => congr_lam ((compRenRen_tm (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upRen_vl_vl rhovl) (up_ren_ren (_) (_) (_) Eqvl)) s0)
    | app (_) s0 s1 => congr_app ((compRenRen_tm xivl zetavl rhovl Eqvl) s0) ((compRenRen_vl xivl zetavl rhovl Eqvl) s1)
    | creturn (_) s0 => congr_creturn ((compRenRen_vl xivl zetavl rhovl Eqvl) s0)
    | clet (_) s0 s1 => congr_clet ((compRenRen_tm xivl zetavl rhovl Eqvl) s0) ((compRenRen_tm (upRen_vl_vl xivl) (upRen_vl_vl zetavl) (upRen_vl_vl rhovl) (up_ren_ren (_) (_) (_) Eqvl)) s1)
    | force (_) s0 => congr_force ((compRenRen_vl xivl zetavl rhovl Eqvl) s0)
    | cif (_) s0 s1 s2 => congr_cif ((compRenRen_vl xivl zetavl rhovl Eqvl) s0) ((compRenRen_tm xivl zetavl rhovl Eqvl) s1) ((compRenRen_tm xivl zetavl rhovl Eqvl) s2)
    end
 with compRenRen_vl { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (rhovl : (fin) (mvl) -> (fin) (lvl)) (Eqvl : forall x, ((funcomp) zetavl xivl) x = rhovl x) (s : vl (mvl)) : ren_vl zetavl (ren_vl xivl s) = ren_vl rhovl s :=
    match s return ren_vl zetavl (ren_vl xivl s) = ren_vl rhovl s with
    | var_vl (_) s => (ap) (var_vl (lvl)) (Eqvl s)
    | true (_)  => congr_true 
    | false (_)  => congr_false 
    | thunk (_) s0 => congr_thunk ((compRenRen_tm xivl zetavl rhovl Eqvl) s0)
    end.

Definition up_ren_subst_vl_vl { k : nat } { l : nat } { mvl : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> vl (mvl)) (theta : (fin) (k) -> vl (mvl)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_vl_vl tau) (upRen_vl_vl xi)) x = (up_vl_vl theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_vl (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint compRenSubst_tm { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) tauvl xivl) x = thetavl x) (s : tm (mvl)) : subst_tm tauvl (ren_tm xivl s) = subst_tm thetavl s :=
    match s return subst_tm tauvl (ren_tm xivl s) = subst_tm thetavl s with
    | lam (_) s0 => congr_lam ((compRenSubst_tm (upRen_vl_vl xivl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_ren_subst_vl_vl (_) (_) (_) Eqvl)) s0)
    | app (_) s0 s1 => congr_app ((compRenSubst_tm xivl tauvl thetavl Eqvl) s0) ((compRenSubst_vl xivl tauvl thetavl Eqvl) s1)
    | creturn (_) s0 => congr_creturn ((compRenSubst_vl xivl tauvl thetavl Eqvl) s0)
    | clet (_) s0 s1 => congr_clet ((compRenSubst_tm xivl tauvl thetavl Eqvl) s0) ((compRenSubst_tm (upRen_vl_vl xivl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_ren_subst_vl_vl (_) (_) (_) Eqvl)) s1)
    | force (_) s0 => congr_force ((compRenSubst_vl xivl tauvl thetavl Eqvl) s0)
    | cif (_) s0 s1 s2 => congr_cif ((compRenSubst_vl xivl tauvl thetavl Eqvl) s0) ((compRenSubst_tm xivl tauvl thetavl Eqvl) s1) ((compRenSubst_tm xivl tauvl thetavl Eqvl) s2)
    end
 with compRenSubst_vl { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) tauvl xivl) x = thetavl x) (s : vl (mvl)) : subst_vl tauvl (ren_vl xivl s) = subst_vl thetavl s :=
    match s return subst_vl tauvl (ren_vl xivl s) = subst_vl thetavl s with
    | var_vl (_) s => Eqvl s
    | true (_)  => congr_true 
    | false (_)  => congr_false 
    | thunk (_) s0 => congr_thunk ((compRenSubst_tm xivl tauvl thetavl Eqvl) s0)
    end.

Definition up_subst_ren_vl_vl { k : nat } { lvl : nat } { mvl : nat } (sigma : (fin) (k) -> vl (lvl)) (zetavl : (fin) (lvl) -> (fin) (mvl)) (theta : (fin) (k) -> vl (mvl)) (Eq : forall x, ((funcomp) (ren_vl zetavl) sigma) x = theta x) : forall x, ((funcomp) (ren_vl (upRen_vl_vl zetavl)) (up_vl_vl sigma)) x = (up_vl_vl theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_vl (shift) (upRen_vl_vl zetavl) ((funcomp) (shift) zetavl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_vl zetavl (shift) ((funcomp) (shift) zetavl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_vl (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstRen_tm { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) (ren_vl zetavl) sigmavl) x = thetavl x) (s : tm (mvl)) : ren_tm zetavl (subst_tm sigmavl s) = subst_tm thetavl s :=
    match s return ren_tm zetavl (subst_tm sigmavl s) = subst_tm thetavl s with
    | lam (_) s0 => congr_lam ((compSubstRen_tm (up_vl_vl sigmavl) (upRen_vl_vl zetavl) (up_vl_vl thetavl) (up_subst_ren_vl_vl (_) (_) (_) Eqvl)) s0)
    | app (_) s0 s1 => congr_app ((compSubstRen_tm sigmavl zetavl thetavl Eqvl) s0) ((compSubstRen_vl sigmavl zetavl thetavl Eqvl) s1)
    | creturn (_) s0 => congr_creturn ((compSubstRen_vl sigmavl zetavl thetavl Eqvl) s0)
    | clet (_) s0 s1 => congr_clet ((compSubstRen_tm sigmavl zetavl thetavl Eqvl) s0) ((compSubstRen_tm (up_vl_vl sigmavl) (upRen_vl_vl zetavl) (up_vl_vl thetavl) (up_subst_ren_vl_vl (_) (_) (_) Eqvl)) s1)
    | force (_) s0 => congr_force ((compSubstRen_vl sigmavl zetavl thetavl Eqvl) s0)
    | cif (_) s0 s1 s2 => congr_cif ((compSubstRen_vl sigmavl zetavl thetavl Eqvl) s0) ((compSubstRen_tm sigmavl zetavl thetavl Eqvl) s1) ((compSubstRen_tm sigmavl zetavl thetavl Eqvl) s2)
    end
 with compSubstRen_vl { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) (ren_vl zetavl) sigmavl) x = thetavl x) (s : vl (mvl)) : ren_vl zetavl (subst_vl sigmavl s) = subst_vl thetavl s :=
    match s return ren_vl zetavl (subst_vl sigmavl s) = subst_vl thetavl s with
    | var_vl (_) s => Eqvl s
    | true (_)  => congr_true 
    | false (_)  => congr_false 
    | thunk (_) s0 => congr_thunk ((compSubstRen_tm sigmavl zetavl thetavl Eqvl) s0)
    end.

Definition up_subst_subst_vl_vl { k : nat } { lvl : nat } { mvl : nat } (sigma : (fin) (k) -> vl (lvl)) (tauvl : (fin) (lvl) -> vl (mvl)) (theta : (fin) (k) -> vl (mvl)) (Eq : forall x, ((funcomp) (subst_vl tauvl) sigma) x = theta x) : forall x, ((funcomp) (subst_vl (up_vl_vl tauvl)) (up_vl_vl sigma)) x = (up_vl_vl theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_vl (shift) (up_vl_vl tauvl) ((funcomp) (up_vl_vl tauvl) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_vl tauvl (shift) ((funcomp) (ren_vl (shift)) tauvl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_vl (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstSubst_tm { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) (subst_vl tauvl) sigmavl) x = thetavl x) (s : tm (mvl)) : subst_tm tauvl (subst_tm sigmavl s) = subst_tm thetavl s :=
    match s return subst_tm tauvl (subst_tm sigmavl s) = subst_tm thetavl s with
    | lam (_) s0 => congr_lam ((compSubstSubst_tm (up_vl_vl sigmavl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_subst_subst_vl_vl (_) (_) (_) Eqvl)) s0)
    | app (_) s0 s1 => congr_app ((compSubstSubst_tm sigmavl tauvl thetavl Eqvl) s0) ((compSubstSubst_vl sigmavl tauvl thetavl Eqvl) s1)
    | creturn (_) s0 => congr_creturn ((compSubstSubst_vl sigmavl tauvl thetavl Eqvl) s0)
    | clet (_) s0 s1 => congr_clet ((compSubstSubst_tm sigmavl tauvl thetavl Eqvl) s0) ((compSubstSubst_tm (up_vl_vl sigmavl) (up_vl_vl tauvl) (up_vl_vl thetavl) (up_subst_subst_vl_vl (_) (_) (_) Eqvl)) s1)
    | force (_) s0 => congr_force ((compSubstSubst_vl sigmavl tauvl thetavl Eqvl) s0)
    | cif (_) s0 s1 s2 => congr_cif ((compSubstSubst_vl sigmavl tauvl thetavl Eqvl) s0) ((compSubstSubst_tm sigmavl tauvl thetavl Eqvl) s1) ((compSubstSubst_tm sigmavl tauvl thetavl Eqvl) s2)
    end
 with compSubstSubst_vl { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (thetavl : (fin) (mvl) -> vl (lvl)) (Eqvl : forall x, ((funcomp) (subst_vl tauvl) sigmavl) x = thetavl x) (s : vl (mvl)) : subst_vl tauvl (subst_vl sigmavl s) = subst_vl thetavl s :=
    match s return subst_vl tauvl (subst_vl sigmavl s) = subst_vl thetavl s with
    | var_vl (_) s => Eqvl s
    | true (_)  => congr_true 
    | false (_)  => congr_false 
    | thunk (_) s0 => congr_thunk ((compSubstSubst_tm sigmavl tauvl thetavl Eqvl) s0)
    end.

Definition rinstInst_up_vl_vl { m : nat } { nvl : nat } (xi : (fin) (m) -> (fin) (nvl)) (sigma : (fin) (m) -> vl (nvl)) (Eq : forall x, ((funcomp) (var_vl (nvl)) xi) x = sigma x) : forall x, ((funcomp) (var_vl ((S) nvl)) (upRen_vl_vl xi)) x = (up_vl_vl sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_vl (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint rinst_inst_tm { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (sigmavl : (fin) (mvl) -> vl (nvl)) (Eqvl : forall x, ((funcomp) (var_vl (nvl)) xivl) x = sigmavl x) (s : tm (mvl)) : ren_tm xivl s = subst_tm sigmavl s :=
    match s return ren_tm xivl s = subst_tm sigmavl s with
    | lam (_) s0 => congr_lam ((rinst_inst_tm (upRen_vl_vl xivl) (up_vl_vl sigmavl) (rinstInst_up_vl_vl (_) (_) Eqvl)) s0)
    | app (_) s0 s1 => congr_app ((rinst_inst_tm xivl sigmavl Eqvl) s0) ((rinst_inst_vl xivl sigmavl Eqvl) s1)
    | creturn (_) s0 => congr_creturn ((rinst_inst_vl xivl sigmavl Eqvl) s0)
    | clet (_) s0 s1 => congr_clet ((rinst_inst_tm xivl sigmavl Eqvl) s0) ((rinst_inst_tm (upRen_vl_vl xivl) (up_vl_vl sigmavl) (rinstInst_up_vl_vl (_) (_) Eqvl)) s1)
    | force (_) s0 => congr_force ((rinst_inst_vl xivl sigmavl Eqvl) s0)
    | cif (_) s0 s1 s2 => congr_cif ((rinst_inst_vl xivl sigmavl Eqvl) s0) ((rinst_inst_tm xivl sigmavl Eqvl) s1) ((rinst_inst_tm xivl sigmavl Eqvl) s2)
    end
 with rinst_inst_vl { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) (sigmavl : (fin) (mvl) -> vl (nvl)) (Eqvl : forall x, ((funcomp) (var_vl (nvl)) xivl) x = sigmavl x) (s : vl (mvl)) : ren_vl xivl s = subst_vl sigmavl s :=
    match s return ren_vl xivl s = subst_vl sigmavl s with
    | var_vl (_) s => Eqvl s
    | true (_)  => congr_true 
    | false (_)  => congr_false 
    | thunk (_) s0 => congr_thunk ((rinst_inst_tm xivl sigmavl Eqvl) s0)
    end.

Lemma rinstInst_tm { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) : ren_tm xivl = subst_tm ((funcomp) (var_vl (nvl)) xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_tm xivl (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_vl { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) : ren_vl xivl = subst_vl ((funcomp) (var_vl (nvl)) xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_vl xivl (_) (fun n => eq_refl) x)). Qed.

Lemma instId_tm { mvl : nat } : subst_tm (var_vl (mvl)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_tm (var_vl (mvl)) (fun n => eq_refl) ((id) x))). Qed.

Lemma instId_vl { mvl : nat } : subst_vl (var_vl (mvl)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_vl (var_vl (mvl)) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_tm { mvl : nat } : @ren_tm (mvl) (mvl) (id) = id .
Proof. exact ((eq_trans) (rinstInst_tm ((id) (_))) instId_tm). Qed.

Lemma rinstId_vl { mvl : nat } : @ren_vl (mvl) (mvl) (id) = id .
Proof. exact ((eq_trans) (rinstInst_vl ((id) (_))) instId_vl). Qed.

Lemma varL_vl { mvl : nat } { nvl : nat } (sigmavl : (fin) (mvl) -> vl (nvl)) : (funcomp) (subst_vl sigmavl) (var_vl (mvl)) = sigmavl .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_vl { mvl : nat } { nvl : nat } (xivl : (fin) (mvl) -> (fin) (nvl)) : (funcomp) (ren_vl xivl) (var_vl (mvl)) = (funcomp) (var_vl (nvl)) xivl .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_tm { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (s : tm (mvl)) : subst_tm tauvl (subst_tm sigmavl s) = subst_tm ((funcomp) (subst_vl tauvl) sigmavl) s .
Proof. exact (compSubstSubst_tm sigmavl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma compComp_vl { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (s : vl (mvl)) : subst_vl tauvl (subst_vl sigmavl s) = subst_vl ((funcomp) (subst_vl tauvl) sigmavl) s .
Proof. exact (compSubstSubst_vl sigmavl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_tm { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) : (funcomp) (subst_tm tauvl) (subst_tm sigmavl) = subst_tm ((funcomp) (subst_vl tauvl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_tm sigmavl tauvl n)). Qed.

Lemma compComp'_vl { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) : (funcomp) (subst_vl tauvl) (subst_vl sigmavl) = subst_vl ((funcomp) (subst_vl tauvl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_vl sigmavl tauvl n)). Qed.

Lemma compRen_tm { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : tm (mvl)) : ren_tm zetavl (subst_tm sigmavl s) = subst_tm ((funcomp) (ren_vl zetavl) sigmavl) s .
Proof. exact (compSubstRen_tm sigmavl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma compRen_vl { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : vl (mvl)) : ren_vl zetavl (subst_vl sigmavl s) = subst_vl ((funcomp) (ren_vl zetavl) sigmavl) s .
Proof. exact (compSubstRen_vl sigmavl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_tm { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_tm zetavl) (subst_tm sigmavl) = subst_tm ((funcomp) (ren_vl zetavl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_tm sigmavl zetavl n)). Qed.

Lemma compRen'_vl { kvl : nat } { lvl : nat } { mvl : nat } (sigmavl : (fin) (mvl) -> vl (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_vl zetavl) (subst_vl sigmavl) = subst_vl ((funcomp) (ren_vl zetavl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_vl sigmavl zetavl n)). Qed.

Lemma renComp_tm { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (s : tm (mvl)) : subst_tm tauvl (ren_tm xivl s) = subst_tm ((funcomp) tauvl xivl) s .
Proof. exact (compRenSubst_tm xivl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma renComp_vl { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) (s : vl (mvl)) : subst_vl tauvl (ren_vl xivl s) = subst_vl ((funcomp) tauvl xivl) s .
Proof. exact (compRenSubst_vl xivl tauvl (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_tm { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) : (funcomp) (subst_tm tauvl) (ren_tm xivl) = subst_tm ((funcomp) tauvl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_tm xivl tauvl n)). Qed.

Lemma renComp'_vl { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (tauvl : (fin) (kvl) -> vl (lvl)) : (funcomp) (subst_vl tauvl) (ren_vl xivl) = subst_vl ((funcomp) tauvl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_vl xivl tauvl n)). Qed.

Lemma renRen_tm { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : tm (mvl)) : ren_tm zetavl (ren_tm xivl s) = ren_tm ((funcomp) zetavl xivl) s .
Proof. exact (compRenRen_tm xivl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma renRen_vl { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : vl (mvl)) : ren_vl zetavl (ren_vl xivl s) = ren_vl ((funcomp) zetavl xivl) s .
Proof. exact (compRenRen_vl xivl zetavl (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_tm { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_tm zetavl) (ren_tm xivl) = ren_tm ((funcomp) zetavl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_tm xivl zetavl n)). Qed.

Lemma renRen'_vl { kvl : nat } { lvl : nat } { mvl : nat } (xivl : (fin) (mvl) -> (fin) (kvl)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_vl zetavl) (ren_vl xivl) = ren_vl ((funcomp) zetavl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_vl xivl zetavl n)). Qed.

End tmvl.

Section Tm.
Inductive Tm (nTm : nat) : Type :=
  | var_Tm : (fin) (nTm) -> Tm (nTm)
  | Lam : Tm  ((S) nTm) -> Tm (nTm)
  | App : Tm  (nTm) -> Tm  (nTm) -> Tm (nTm)
  | If : Tm  (nTm) -> Tm  (nTm) -> Tm  (nTm) -> Tm (nTm)
  | True : Tm (nTm)
  | False : Tm (nTm).

Lemma congr_Lam { mTm : nat } { s0 : Tm  ((S) mTm) } { t0 : Tm  ((S) mTm) } (H1 : s0 = t0) : Lam (mTm) s0 = Lam (mTm) t0 .
Proof. congruence. Qed.

Lemma congr_App { mTm : nat } { s0 : Tm  (mTm) } { s1 : Tm  (mTm) } { t0 : Tm  (mTm) } { t1 : Tm  (mTm) } (H1 : s0 = t0) (H2 : s1 = t1) : App (mTm) s0 s1 = App (mTm) t0 t1 .
Proof. congruence. Qed.

Lemma congr_If { mTm : nat } { s0 : Tm  (mTm) } { s1 : Tm  (mTm) } { s2 : Tm  (mTm) } { t0 : Tm  (mTm) } { t1 : Tm  (mTm) } { t2 : Tm  (mTm) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : If (mTm) s0 s1 s2 = If (mTm) t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_True { mTm : nat } : True (mTm) = True (mTm) .
Proof. congruence. Qed.

Lemma congr_False { mTm : nat } : False (mTm) = False (mTm) .
Proof. congruence. Qed.

Definition upRen_Tm_Tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Fixpoint ren_Tm { mTm : nat } { nTm : nat } (xiTm : (fin) (mTm) -> (fin) (nTm)) (s : Tm (mTm)) : Tm (nTm) :=
    match s return Tm (nTm) with
    | var_Tm (_) s => (var_Tm (nTm)) (xiTm s)
    | Lam (_) s0 => Lam (nTm) ((ren_Tm (upRen_Tm_Tm xiTm)) s0)
    | App (_) s0 s1 => App (nTm) ((ren_Tm xiTm) s0) ((ren_Tm xiTm) s1)
    | If (_) s0 s1 s2 => If (nTm) ((ren_Tm xiTm) s0) ((ren_Tm xiTm) s1) ((ren_Tm xiTm) s2)
    | True (_)  => True (nTm)
    | False (_)  => False (nTm)
    end.

Definition up_Tm_Tm { m : nat } { nTm : nat } (sigma : (fin) (m) -> Tm (nTm)) : (fin) ((S) (m)) -> Tm ((S) nTm) :=
  (scons) ((var_Tm ((S) nTm)) (var_zero)) ((funcomp) (ren_Tm (shift)) sigma).

Fixpoint subst_Tm { mTm : nat } { nTm : nat } (sigmaTm : (fin) (mTm) -> Tm (nTm)) (s : Tm (mTm)) : Tm (nTm) :=
    match s return Tm (nTm) with
    | var_Tm (_) s => sigmaTm s
    | Lam (_) s0 => Lam (nTm) ((subst_Tm (up_Tm_Tm sigmaTm)) s0)
    | App (_) s0 s1 => App (nTm) ((subst_Tm sigmaTm) s0) ((subst_Tm sigmaTm) s1)
    | If (_) s0 s1 s2 => If (nTm) ((subst_Tm sigmaTm) s0) ((subst_Tm sigmaTm) s1) ((subst_Tm sigmaTm) s2)
    | True (_)  => True (nTm)
    | False (_)  => False (nTm)
    end.

Definition upId_Tm_Tm { mTm : nat } (sigma : (fin) (mTm) -> Tm (mTm)) (Eq : forall x, sigma x = (var_Tm (mTm)) x) : forall x, (up_Tm_Tm sigma) x = (var_Tm ((S) mTm)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Tm (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint idSubst_Tm { mTm : nat } (sigmaTm : (fin) (mTm) -> Tm (mTm)) (EqTm : forall x, sigmaTm x = (var_Tm (mTm)) x) (s : Tm (mTm)) : subst_Tm sigmaTm s = s :=
    match s return subst_Tm sigmaTm s = s with
    | var_Tm (_) s => EqTm s
    | Lam (_) s0 => congr_Lam ((idSubst_Tm (up_Tm_Tm sigmaTm) (upId_Tm_Tm (_) EqTm)) s0)
    | App (_) s0 s1 => congr_App ((idSubst_Tm sigmaTm EqTm) s0) ((idSubst_Tm sigmaTm EqTm) s1)
    | If (_) s0 s1 s2 => congr_If ((idSubst_Tm sigmaTm EqTm) s0) ((idSubst_Tm sigmaTm EqTm) s1) ((idSubst_Tm sigmaTm EqTm) s2)
    | True (_)  => congr_True 
    | False (_)  => congr_False 
    end.

Definition upExtRen_Tm_Tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_Tm_Tm xi) x = (upRen_Tm_Tm zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint extRen_Tm { mTm : nat } { nTm : nat } (xiTm : (fin) (mTm) -> (fin) (nTm)) (zetaTm : (fin) (mTm) -> (fin) (nTm)) (EqTm : forall x, xiTm x = zetaTm x) (s : Tm (mTm)) : ren_Tm xiTm s = ren_Tm zetaTm s :=
    match s return ren_Tm xiTm s = ren_Tm zetaTm s with
    | var_Tm (_) s => (ap) (var_Tm (nTm)) (EqTm s)
    | Lam (_) s0 => congr_Lam ((extRen_Tm (upRen_Tm_Tm xiTm) (upRen_Tm_Tm zetaTm) (upExtRen_Tm_Tm (_) (_) EqTm)) s0)
    | App (_) s0 s1 => congr_App ((extRen_Tm xiTm zetaTm EqTm) s0) ((extRen_Tm xiTm zetaTm EqTm) s1)
    | If (_) s0 s1 s2 => congr_If ((extRen_Tm xiTm zetaTm EqTm) s0) ((extRen_Tm xiTm zetaTm EqTm) s1) ((extRen_Tm xiTm zetaTm EqTm) s2)
    | True (_)  => congr_True 
    | False (_)  => congr_False 
    end.

Definition upExt_Tm_Tm { m : nat } { nTm : nat } (sigma : (fin) (m) -> Tm (nTm)) (tau : (fin) (m) -> Tm (nTm)) (Eq : forall x, sigma x = tau x) : forall x, (up_Tm_Tm sigma) x = (up_Tm_Tm tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Tm (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint ext_Tm { mTm : nat } { nTm : nat } (sigmaTm : (fin) (mTm) -> Tm (nTm)) (tauTm : (fin) (mTm) -> Tm (nTm)) (EqTm : forall x, sigmaTm x = tauTm x) (s : Tm (mTm)) : subst_Tm sigmaTm s = subst_Tm tauTm s :=
    match s return subst_Tm sigmaTm s = subst_Tm tauTm s with
    | var_Tm (_) s => EqTm s
    | Lam (_) s0 => congr_Lam ((ext_Tm (up_Tm_Tm sigmaTm) (up_Tm_Tm tauTm) (upExt_Tm_Tm (_) (_) EqTm)) s0)
    | App (_) s0 s1 => congr_App ((ext_Tm sigmaTm tauTm EqTm) s0) ((ext_Tm sigmaTm tauTm EqTm) s1)
    | If (_) s0 s1 s2 => congr_If ((ext_Tm sigmaTm tauTm EqTm) s0) ((ext_Tm sigmaTm tauTm EqTm) s1) ((ext_Tm sigmaTm tauTm EqTm) s2)
    | True (_)  => congr_True 
    | False (_)  => congr_False 
    end.

Definition up_ren_ren_Tm_Tm { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_Tm_Tm tau) (upRen_Tm_Tm xi)) x = (upRen_Tm_Tm theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_Tm { kTm : nat } { lTm : nat } { mTm : nat } (xiTm : (fin) (mTm) -> (fin) (kTm)) (zetaTm : (fin) (kTm) -> (fin) (lTm)) (rhoTm : (fin) (mTm) -> (fin) (lTm)) (EqTm : forall x, ((funcomp) zetaTm xiTm) x = rhoTm x) (s : Tm (mTm)) : ren_Tm zetaTm (ren_Tm xiTm s) = ren_Tm rhoTm s :=
    match s return ren_Tm zetaTm (ren_Tm xiTm s) = ren_Tm rhoTm s with
    | var_Tm (_) s => (ap) (var_Tm (lTm)) (EqTm s)
    | Lam (_) s0 => congr_Lam ((compRenRen_Tm (upRen_Tm_Tm xiTm) (upRen_Tm_Tm zetaTm) (upRen_Tm_Tm rhoTm) (up_ren_ren (_) (_) (_) EqTm)) s0)
    | App (_) s0 s1 => congr_App ((compRenRen_Tm xiTm zetaTm rhoTm EqTm) s0) ((compRenRen_Tm xiTm zetaTm rhoTm EqTm) s1)
    | If (_) s0 s1 s2 => congr_If ((compRenRen_Tm xiTm zetaTm rhoTm EqTm) s0) ((compRenRen_Tm xiTm zetaTm rhoTm EqTm) s1) ((compRenRen_Tm xiTm zetaTm rhoTm EqTm) s2)
    | True (_)  => congr_True 
    | False (_)  => congr_False 
    end.

Definition up_ren_subst_Tm_Tm { k : nat } { l : nat } { mTm : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> Tm (mTm)) (theta : (fin) (k) -> Tm (mTm)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_Tm_Tm tau) (upRen_Tm_Tm xi)) x = (up_Tm_Tm theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Tm (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint compRenSubst_Tm { kTm : nat } { lTm : nat } { mTm : nat } (xiTm : (fin) (mTm) -> (fin) (kTm)) (tauTm : (fin) (kTm) -> Tm (lTm)) (thetaTm : (fin) (mTm) -> Tm (lTm)) (EqTm : forall x, ((funcomp) tauTm xiTm) x = thetaTm x) (s : Tm (mTm)) : subst_Tm tauTm (ren_Tm xiTm s) = subst_Tm thetaTm s :=
    match s return subst_Tm tauTm (ren_Tm xiTm s) = subst_Tm thetaTm s with
    | var_Tm (_) s => EqTm s
    | Lam (_) s0 => congr_Lam ((compRenSubst_Tm (upRen_Tm_Tm xiTm) (up_Tm_Tm tauTm) (up_Tm_Tm thetaTm) (up_ren_subst_Tm_Tm (_) (_) (_) EqTm)) s0)
    | App (_) s0 s1 => congr_App ((compRenSubst_Tm xiTm tauTm thetaTm EqTm) s0) ((compRenSubst_Tm xiTm tauTm thetaTm EqTm) s1)
    | If (_) s0 s1 s2 => congr_If ((compRenSubst_Tm xiTm tauTm thetaTm EqTm) s0) ((compRenSubst_Tm xiTm tauTm thetaTm EqTm) s1) ((compRenSubst_Tm xiTm tauTm thetaTm EqTm) s2)
    | True (_)  => congr_True 
    | False (_)  => congr_False 
    end.

Definition up_subst_ren_Tm_Tm { k : nat } { lTm : nat } { mTm : nat } (sigma : (fin) (k) -> Tm (lTm)) (zetaTm : (fin) (lTm) -> (fin) (mTm)) (theta : (fin) (k) -> Tm (mTm)) (Eq : forall x, ((funcomp) (ren_Tm zetaTm) sigma) x = theta x) : forall x, ((funcomp) (ren_Tm (upRen_Tm_Tm zetaTm)) (up_Tm_Tm sigma)) x = (up_Tm_Tm theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_Tm (shift) (upRen_Tm_Tm zetaTm) ((funcomp) (shift) zetaTm) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_Tm zetaTm (shift) ((funcomp) (shift) zetaTm) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_Tm (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstRen_Tm { kTm : nat } { lTm : nat } { mTm : nat } (sigmaTm : (fin) (mTm) -> Tm (kTm)) (zetaTm : (fin) (kTm) -> (fin) (lTm)) (thetaTm : (fin) (mTm) -> Tm (lTm)) (EqTm : forall x, ((funcomp) (ren_Tm zetaTm) sigmaTm) x = thetaTm x) (s : Tm (mTm)) : ren_Tm zetaTm (subst_Tm sigmaTm s) = subst_Tm thetaTm s :=
    match s return ren_Tm zetaTm (subst_Tm sigmaTm s) = subst_Tm thetaTm s with
    | var_Tm (_) s => EqTm s
    | Lam (_) s0 => congr_Lam ((compSubstRen_Tm (up_Tm_Tm sigmaTm) (upRen_Tm_Tm zetaTm) (up_Tm_Tm thetaTm) (up_subst_ren_Tm_Tm (_) (_) (_) EqTm)) s0)
    | App (_) s0 s1 => congr_App ((compSubstRen_Tm sigmaTm zetaTm thetaTm EqTm) s0) ((compSubstRen_Tm sigmaTm zetaTm thetaTm EqTm) s1)
    | If (_) s0 s1 s2 => congr_If ((compSubstRen_Tm sigmaTm zetaTm thetaTm EqTm) s0) ((compSubstRen_Tm sigmaTm zetaTm thetaTm EqTm) s1) ((compSubstRen_Tm sigmaTm zetaTm thetaTm EqTm) s2)
    | True (_)  => congr_True 
    | False (_)  => congr_False 
    end.

Definition up_subst_subst_Tm_Tm { k : nat } { lTm : nat } { mTm : nat } (sigma : (fin) (k) -> Tm (lTm)) (tauTm : (fin) (lTm) -> Tm (mTm)) (theta : (fin) (k) -> Tm (mTm)) (Eq : forall x, ((funcomp) (subst_Tm tauTm) sigma) x = theta x) : forall x, ((funcomp) (subst_Tm (up_Tm_Tm tauTm)) (up_Tm_Tm sigma)) x = (up_Tm_Tm theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_Tm (shift) (up_Tm_Tm tauTm) ((funcomp) (up_Tm_Tm tauTm) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_Tm tauTm (shift) ((funcomp) (ren_Tm (shift)) tauTm) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_Tm (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstSubst_Tm { kTm : nat } { lTm : nat } { mTm : nat } (sigmaTm : (fin) (mTm) -> Tm (kTm)) (tauTm : (fin) (kTm) -> Tm (lTm)) (thetaTm : (fin) (mTm) -> Tm (lTm)) (EqTm : forall x, ((funcomp) (subst_Tm tauTm) sigmaTm) x = thetaTm x) (s : Tm (mTm)) : subst_Tm tauTm (subst_Tm sigmaTm s) = subst_Tm thetaTm s :=
    match s return subst_Tm tauTm (subst_Tm sigmaTm s) = subst_Tm thetaTm s with
    | var_Tm (_) s => EqTm s
    | Lam (_) s0 => congr_Lam ((compSubstSubst_Tm (up_Tm_Tm sigmaTm) (up_Tm_Tm tauTm) (up_Tm_Tm thetaTm) (up_subst_subst_Tm_Tm (_) (_) (_) EqTm)) s0)
    | App (_) s0 s1 => congr_App ((compSubstSubst_Tm sigmaTm tauTm thetaTm EqTm) s0) ((compSubstSubst_Tm sigmaTm tauTm thetaTm EqTm) s1)
    | If (_) s0 s1 s2 => congr_If ((compSubstSubst_Tm sigmaTm tauTm thetaTm EqTm) s0) ((compSubstSubst_Tm sigmaTm tauTm thetaTm EqTm) s1) ((compSubstSubst_Tm sigmaTm tauTm thetaTm EqTm) s2)
    | True (_)  => congr_True 
    | False (_)  => congr_False 
    end.

Definition rinstInst_up_Tm_Tm { m : nat } { nTm : nat } (xi : (fin) (m) -> (fin) (nTm)) (sigma : (fin) (m) -> Tm (nTm)) (Eq : forall x, ((funcomp) (var_Tm (nTm)) xi) x = sigma x) : forall x, ((funcomp) (var_Tm ((S) nTm)) (upRen_Tm_Tm xi)) x = (up_Tm_Tm sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Tm (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint rinst_inst_Tm { mTm : nat } { nTm : nat } (xiTm : (fin) (mTm) -> (fin) (nTm)) (sigmaTm : (fin) (mTm) -> Tm (nTm)) (EqTm : forall x, ((funcomp) (var_Tm (nTm)) xiTm) x = sigmaTm x) (s : Tm (mTm)) : ren_Tm xiTm s = subst_Tm sigmaTm s :=
    match s return ren_Tm xiTm s = subst_Tm sigmaTm s with
    | var_Tm (_) s => EqTm s
    | Lam (_) s0 => congr_Lam ((rinst_inst_Tm (upRen_Tm_Tm xiTm) (up_Tm_Tm sigmaTm) (rinstInst_up_Tm_Tm (_) (_) EqTm)) s0)
    | App (_) s0 s1 => congr_App ((rinst_inst_Tm xiTm sigmaTm EqTm) s0) ((rinst_inst_Tm xiTm sigmaTm EqTm) s1)
    | If (_) s0 s1 s2 => congr_If ((rinst_inst_Tm xiTm sigmaTm EqTm) s0) ((rinst_inst_Tm xiTm sigmaTm EqTm) s1) ((rinst_inst_Tm xiTm sigmaTm EqTm) s2)
    | True (_)  => congr_True 
    | False (_)  => congr_False 
    end.

Lemma rinstInst_Tm { mTm : nat } { nTm : nat } (xiTm : (fin) (mTm) -> (fin) (nTm)) : ren_Tm xiTm = subst_Tm ((funcomp) (var_Tm (nTm)) xiTm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_Tm xiTm (_) (fun n => eq_refl) x)). Qed.

Lemma instId_Tm { mTm : nat } : subst_Tm (var_Tm (mTm)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_Tm (var_Tm (mTm)) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_Tm { mTm : nat } : @ren_Tm (mTm) (mTm) (id) = id .
Proof. exact ((eq_trans) (rinstInst_Tm ((id) (_))) instId_Tm). Qed.

Lemma varL_Tm { mTm : nat } { nTm : nat } (sigmaTm : (fin) (mTm) -> Tm (nTm)) : (funcomp) (subst_Tm sigmaTm) (var_Tm (mTm)) = sigmaTm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_Tm { mTm : nat } { nTm : nat } (xiTm : (fin) (mTm) -> (fin) (nTm)) : (funcomp) (ren_Tm xiTm) (var_Tm (mTm)) = (funcomp) (var_Tm (nTm)) xiTm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_Tm { kTm : nat } { lTm : nat } { mTm : nat } (sigmaTm : (fin) (mTm) -> Tm (kTm)) (tauTm : (fin) (kTm) -> Tm (lTm)) (s : Tm (mTm)) : subst_Tm tauTm (subst_Tm sigmaTm s) = subst_Tm ((funcomp) (subst_Tm tauTm) sigmaTm) s .
Proof. exact (compSubstSubst_Tm sigmaTm tauTm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_Tm { kTm : nat } { lTm : nat } { mTm : nat } (sigmaTm : (fin) (mTm) -> Tm (kTm)) (tauTm : (fin) (kTm) -> Tm (lTm)) : (funcomp) (subst_Tm tauTm) (subst_Tm sigmaTm) = subst_Tm ((funcomp) (subst_Tm tauTm) sigmaTm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_Tm sigmaTm tauTm n)). Qed.

Lemma compRen_Tm { kTm : nat } { lTm : nat } { mTm : nat } (sigmaTm : (fin) (mTm) -> Tm (kTm)) (zetaTm : (fin) (kTm) -> (fin) (lTm)) (s : Tm (mTm)) : ren_Tm zetaTm (subst_Tm sigmaTm s) = subst_Tm ((funcomp) (ren_Tm zetaTm) sigmaTm) s .
Proof. exact (compSubstRen_Tm sigmaTm zetaTm (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_Tm { kTm : nat } { lTm : nat } { mTm : nat } (sigmaTm : (fin) (mTm) -> Tm (kTm)) (zetaTm : (fin) (kTm) -> (fin) (lTm)) : (funcomp) (ren_Tm zetaTm) (subst_Tm sigmaTm) = subst_Tm ((funcomp) (ren_Tm zetaTm) sigmaTm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_Tm sigmaTm zetaTm n)). Qed.

Lemma renComp_Tm { kTm : nat } { lTm : nat } { mTm : nat } (xiTm : (fin) (mTm) -> (fin) (kTm)) (tauTm : (fin) (kTm) -> Tm (lTm)) (s : Tm (mTm)) : subst_Tm tauTm (ren_Tm xiTm s) = subst_Tm ((funcomp) tauTm xiTm) s .
Proof. exact (compRenSubst_Tm xiTm tauTm (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_Tm { kTm : nat } { lTm : nat } { mTm : nat } (xiTm : (fin) (mTm) -> (fin) (kTm)) (tauTm : (fin) (kTm) -> Tm (lTm)) : (funcomp) (subst_Tm tauTm) (ren_Tm xiTm) = subst_Tm ((funcomp) tauTm xiTm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_Tm xiTm tauTm n)). Qed.

Lemma renRen_Tm { kTm : nat } { lTm : nat } { mTm : nat } (xiTm : (fin) (mTm) -> (fin) (kTm)) (zetaTm : (fin) (kTm) -> (fin) (lTm)) (s : Tm (mTm)) : ren_Tm zetaTm (ren_Tm xiTm s) = ren_Tm ((funcomp) zetaTm xiTm) s .
Proof. exact (compRenRen_Tm xiTm zetaTm (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_Tm { kTm : nat } { lTm : nat } { mTm : nat } (xiTm : (fin) (mTm) -> (fin) (kTm)) (zetaTm : (fin) (kTm) -> (fin) (lTm)) : (funcomp) (ren_Tm zetaTm) (ren_Tm xiTm) = ren_Tm ((funcomp) zetaTm xiTm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_Tm xiTm zetaTm n)). Qed.

End Tm.

Arguments lam {nvl}.

Arguments app {nvl}.

Arguments creturn {nvl}.

Arguments clet {nvl}.

Arguments force {nvl}.

Arguments cif {nvl}.

Arguments var_vl {nvl}.

Arguments true {nvl}.

Arguments false {nvl}.

Arguments thunk {nvl}.

Arguments var_Tm {nTm}.

Arguments Lam {nTm}.

Arguments App {nTm}.

Arguments If {nTm}.

Arguments True {nTm}.

Arguments False {nTm}.

Global Instance Subst_tm { mvl : nat } { nvl : nat } : Subst1 ((fin) (mvl) -> vl (nvl)) (tm (mvl)) (tm (nvl)) := @subst_tm (mvl) (nvl) .

Global Instance Subst_vl { mvl : nat } { nvl : nat } : Subst1 ((fin) (mvl) -> vl (nvl)) (vl (mvl)) (vl (nvl)) := @subst_vl (mvl) (nvl) .

Global Instance Subst_Tm { mTm : nat } { nTm : nat } : Subst1 ((fin) (mTm) -> Tm (nTm)) (Tm (mTm)) (Tm (nTm)) := @subst_Tm (mTm) (nTm) .

Global Instance Ren_tm { mvl : nat } { nvl : nat } : Ren1 ((fin) (mvl) -> (fin) (nvl)) (tm (mvl)) (tm (nvl)) := @ren_tm (mvl) (nvl) .

Global Instance Ren_vl { mvl : nat } { nvl : nat } : Ren1 ((fin) (mvl) -> (fin) (nvl)) (vl (mvl)) (vl (nvl)) := @ren_vl (mvl) (nvl) .

Global Instance Ren_Tm { mTm : nat } { nTm : nat } : Ren1 ((fin) (mTm) -> (fin) (nTm)) (Tm (mTm)) (Tm (nTm)) := @ren_Tm (mTm) (nTm) .

Global Instance VarInstance_vl { mvl : nat } : Var ((fin) (mvl)) (vl (mvl)) := @var_vl (mvl) .

Notation "x '__vl'" := (var_vl x) (at level 5, format "x __vl") : subst_scope.

Notation "x '__vl'" := (@ids (_) (_) VarInstance_vl x) (at level 5, only printing, format "x __vl") : subst_scope.

Notation "'var'" := (var_vl) (only printing, at level 1) : subst_scope.

Global Instance VarInstance_Tm { mTm : nat } : Var ((fin) (mTm)) (Tm (mTm)) := @var_Tm (mTm) .

Notation "x '__Tm'" := (var_Tm x) (at level 5, format "x __Tm") : subst_scope.

Notation "x '__Tm'" := (@ids (_) (_) VarInstance_Tm x) (at level 5, only printing, format "x __Tm") : subst_scope.

Notation "'var'" := (var_Tm) (only printing, at level 1) : subst_scope.

Class Up_vl X Y := up_vl : X -> Y.

Notation "↑__vl" := (up_vl) (only printing) : subst_scope.

Class Up_Tm X Y := up_Tm : X -> Y.

Notation "↑__Tm" := (up_Tm) (only printing) : subst_scope.

Notation "↑__vl" := (up_vl_vl) (only printing) : subst_scope.

Global Instance Up_vl_vl { m : nat } { nvl : nat } : Up_vl (_) (_) := @up_vl_vl (m) (nvl) .

Notation "↑__Tm" := (up_Tm_Tm) (only printing) : subst_scope.

Global Instance Up_Tm_Tm { m : nat } { nTm : nat } : Up_Tm (_) (_) := @up_Tm_Tm (m) (nTm) .

Notation "s [ sigmavl ]" := (subst_tm sigmavl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmavl ]" := (subst_tm sigmavl) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xivl ⟩" := (ren_tm xivl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xivl ⟩" := (ren_tm xivl) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmavl ]" := (subst_vl sigmavl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmavl ]" := (subst_vl sigmavl) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xivl ⟩" := (ren_vl xivl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xivl ⟩" := (ren_vl xivl) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaTm ]" := (subst_Tm sigmaTm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaTm ]" := (subst_Tm sigmaTm) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiTm ⟩" := (ren_Tm xiTm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiTm ⟩" := (ren_Tm xiTm) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_tm,  Subst_vl,  Subst_Tm,  Ren_tm,  Ren_vl,  Ren_Tm,  VarInstance_vl,  VarInstance_Tm.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_tm,  Subst_vl,  Subst_Tm,  Ren_tm,  Ren_vl,  Ren_Tm,  VarInstance_vl,  VarInstance_Tm in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_tm| progress rewrite ?compComp_tm| progress rewrite ?compComp'_tm| progress rewrite ?instId_vl| progress rewrite ?compComp_vl| progress rewrite ?compComp'_vl| progress rewrite ?instId_Tm| progress rewrite ?compComp_Tm| progress rewrite ?compComp'_Tm| progress rewrite ?rinstId_tm| progress rewrite ?compRen_tm| progress rewrite ?compRen'_tm| progress rewrite ?renComp_tm| progress rewrite ?renComp'_tm| progress rewrite ?renRen_tm| progress rewrite ?renRen'_tm| progress rewrite ?rinstId_vl| progress rewrite ?compRen_vl| progress rewrite ?compRen'_vl| progress rewrite ?renComp_vl| progress rewrite ?renComp'_vl| progress rewrite ?renRen_vl| progress rewrite ?renRen'_vl| progress rewrite ?rinstId_Tm| progress rewrite ?compRen_Tm| progress rewrite ?compRen'_Tm| progress rewrite ?renComp_Tm| progress rewrite ?renComp'_Tm| progress rewrite ?renRen_Tm| progress rewrite ?renRen'_Tm| progress rewrite ?varL_vl| progress rewrite ?varL_Tm| progress rewrite ?varLRen_vl| progress rewrite ?varLRen_Tm| progress (unfold up_ren, upRen_vl_vl, upRen_Tm_Tm, up_vl_vl, up_Tm_Tm)| progress (cbn [subst_tm subst_vl subst_Tm ren_tm ren_vl ren_Tm])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_tm in *| progress rewrite ?compComp_tm in *| progress rewrite ?compComp'_tm in *| progress rewrite ?instId_vl in *| progress rewrite ?compComp_vl in *| progress rewrite ?compComp'_vl in *| progress rewrite ?instId_Tm in *| progress rewrite ?compComp_Tm in *| progress rewrite ?compComp'_Tm in *| progress rewrite ?rinstId_tm in *| progress rewrite ?compRen_tm in *| progress rewrite ?compRen'_tm in *| progress rewrite ?renComp_tm in *| progress rewrite ?renComp'_tm in *| progress rewrite ?renRen_tm in *| progress rewrite ?renRen'_tm in *| progress rewrite ?rinstId_vl in *| progress rewrite ?compRen_vl in *| progress rewrite ?compRen'_vl in *| progress rewrite ?renComp_vl in *| progress rewrite ?renComp'_vl in *| progress rewrite ?renRen_vl in *| progress rewrite ?renRen'_vl in *| progress rewrite ?rinstId_Tm in *| progress rewrite ?compRen_Tm in *| progress rewrite ?compRen'_Tm in *| progress rewrite ?renComp_Tm in *| progress rewrite ?renComp'_Tm in *| progress rewrite ?renRen_Tm in *| progress rewrite ?renRen'_Tm in *| progress rewrite ?varL_vl in *| progress rewrite ?varL_Tm in *| progress rewrite ?varLRen_vl in *| progress rewrite ?varLRen_Tm in *| progress (unfold up_ren, upRen_vl_vl, upRen_Tm_Tm, up_vl_vl, up_Tm_Tm in *)| progress (cbn [subst_tm subst_vl subst_Tm ren_tm ren_vl ren_Tm] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_tm); try repeat (erewrite rinstInst_vl); try repeat (erewrite rinstInst_Tm).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_tm); try repeat (erewrite <- rinstInst_vl); try repeat (erewrite <- rinstInst_Tm).

(** as_apply follows **)

Ltac  musigma gexp hexp :=
  match   gexp  with
  |  ?s  =>  unify   (gexp) (hexp)
  |  lam (subst_tm ((scons) (var_vl (var_zero)) ((funcomp) (ren_vl (shift)) ?sigma0)) ?s0)  =>  first [ unify   (subst_tm sigma0 (lam s0)) (hexp)|  musigma   (subst_tm sigma0 (lam s0)) (hexp) ]
  |  app (subst_tm ?sigma0 ?s0) (subst_vl ?sigma0 ?s1)  =>  first [ unify   (subst_tm sigma0 (app s0 s1)) (hexp)|  musigma   (subst_tm sigma0 (app s0 s1)) (hexp) ]
  |  creturn (subst_vl ?sigma0 ?s0)  =>  first [ unify   (subst_tm sigma0 (creturn s0)) (hexp)|  musigma   (subst_tm sigma0 (creturn s0)) (hexp) ]
  |  clet (subst_tm ?sigma0 ?s0) (subst_tm ((scons) (var_vl (var_zero)) ((funcomp) (ren_vl (shift)) ?sigma0)) ?s1)  =>  first [ unify   (subst_tm sigma0 (clet s0 s1)) (hexp)|  musigma   (subst_tm sigma0 (clet s0 s1)) (hexp) ]
  |  force (subst_vl ?sigma0 ?s0)  =>  first [ unify   (subst_tm sigma0 (force s0)) (hexp)|  musigma   (subst_tm sigma0 (force s0)) (hexp) ]
  |  cif (subst_vl ?sigma0 ?s0) (subst_tm ?sigma0 ?s1) (subst_tm ?sigma0 ?s2)  =>  first [ unify   (subst_tm sigma0 (cif s0 s1 s2)) (hexp)|  musigma   (subst_tm sigma0 (cif s0 s1 s2)) (hexp) ]
  |  lam (ren_tm ((scons) (var_zero) ((funcomp) (shift) ?sigma0)) ?s0)  =>  first [ unify   (ren_tm sigma0 (lam s0)) (hexp)|  musigma   (ren_tm sigma0 (lam s0)) (hexp) ]
  |  app (ren_tm ?sigma0 ?s0) (ren_vl ?sigma0 ?s1)  =>  first [ unify   (ren_tm sigma0 (app s0 s1)) (hexp)|  musigma   (ren_tm sigma0 (app s0 s1)) (hexp) ]
  |  creturn (ren_vl ?sigma0 ?s0)  =>  first [ unify   (ren_tm sigma0 (creturn s0)) (hexp)|  musigma   (ren_tm sigma0 (creturn s0)) (hexp) ]
  |  clet (ren_tm ?sigma0 ?s0) (ren_tm ((scons) (var_zero) ((funcomp) (shift) ?sigma0)) ?s1)  =>  first [ unify   (ren_tm sigma0 (clet s0 s1)) (hexp)|  musigma   (ren_tm sigma0 (clet s0 s1)) (hexp) ]
  |  force (ren_vl ?sigma0 ?s0)  =>  first [ unify   (ren_tm sigma0 (force s0)) (hexp)|  musigma   (ren_tm sigma0 (force s0)) (hexp) ]
  |  cif (ren_vl ?sigma0 ?s0) (ren_tm ?sigma0 ?s1) (ren_tm ?sigma0 ?s2)  =>  first [ unify   (ren_tm sigma0 (cif s0 s1 s2)) (hexp)|  musigma   (ren_tm sigma0 (cif s0 s1 s2)) (hexp) ]
  |  thunk (subst_tm ?sigma0 ?s0)  =>  first [ unify   (subst_vl sigma0 (thunk s0)) (hexp)|  musigma   (subst_vl sigma0 (thunk s0)) (hexp) ]
  |  thunk (ren_tm ?sigma0 ?s0)  =>  first [ unify   (ren_vl sigma0 (thunk s0)) (hexp)|  musigma   (ren_vl sigma0 (thunk s0)) (hexp) ]
  |  Lam (subst_Tm ((scons) (var_Tm (var_zero)) ((funcomp) (ren_Tm (shift)) ?sigma0)) ?s0)  =>  first [ unify   (subst_Tm sigma0 (Lam s0)) (hexp)|  musigma   (subst_Tm sigma0 (Lam s0)) (hexp) ]
  |  App (subst_Tm ?sigma0 ?s0) (subst_Tm ?sigma0 ?s1)  =>  first [ unify   (subst_Tm sigma0 (App s0 s1)) (hexp)|  musigma   (subst_Tm sigma0 (App s0 s1)) (hexp) ]
  |  If (subst_Tm ?sigma0 ?s0) (subst_Tm ?sigma0 ?s1) (subst_Tm ?sigma0 ?s2)  =>  first [ unify   (subst_Tm sigma0 (If s0 s1 s2)) (hexp)|  musigma   (subst_Tm sigma0 (If s0 s1 s2)) (hexp) ]
  |  Lam (ren_Tm ((scons) (var_zero) ((funcomp) (shift) ?sigma0)) ?s0)  =>  first [ unify   (ren_Tm sigma0 (Lam s0)) (hexp)|  musigma   (ren_Tm sigma0 (Lam s0)) (hexp) ]
  |  App (ren_Tm ?sigma0 ?s0) (ren_Tm ?sigma0 ?s1)  =>  first [ unify   (ren_Tm sigma0 (App s0 s1)) (hexp)|  musigma   (ren_Tm sigma0 (App s0 s1)) (hexp) ]
  |  If (ren_Tm ?sigma0 ?s0) (ren_Tm ?sigma0 ?s1) (ren_Tm ?sigma0 ?s2)  =>  first [ unify   (ren_Tm sigma0 (If s0 s1 s2)) (hexp)|  musigma   (ren_Tm sigma0 (If s0 s1 s2)) (hexp) ]
  |  ren_tm ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  ren_tm ?theta0 ?t  =>  first [ unify   (ren_tm tau0 (ren_tm sigma0 s)) (hexp)|  musigma   (ren_tm tau0 (ren_tm sigma0 s)) (hexp) ]
  end
  |  subst_tm ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  subst_tm ?theta0 ?t  =>  first [ unify   (subst_tm tau0 (ren_tm sigma0 s)) (hexp)|  musigma   (subst_tm tau0 (ren_tm sigma0 s)) (hexp) ]
  end
  |  subst_tm ((funcomp) (ren_vl ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  ren_tm ?theta0 ?t  =>  first [ unify   (ren_tm tau0 (subst_tm sigma0 s)) (hexp)|  musigma   (ren_tm tau0 (subst_tm sigma0 s)) (hexp) ]
  end
  |  subst_tm ((funcomp) (subst_vl ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  subst_tm ?theta0 ?t  =>  first [ unify   (subst_tm tau0 (subst_tm sigma0 s)) (hexp)|  musigma   (subst_tm tau0 (subst_tm sigma0 s)) (hexp) ]
  end
  |  ren_vl ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  ren_vl ?theta0 ?t  =>  first [ unify   (ren_vl tau0 (ren_vl sigma0 s)) (hexp)|  musigma   (ren_vl tau0 (ren_vl sigma0 s)) (hexp) ]
  end
  |  subst_vl ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  subst_vl ?theta0 ?t  =>  first [ unify   (subst_vl tau0 (ren_vl sigma0 s)) (hexp)|  musigma   (subst_vl tau0 (ren_vl sigma0 s)) (hexp) ]
  end
  |  subst_vl ((funcomp) (ren_vl ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  ren_vl ?theta0 ?t  =>  first [ unify   (ren_vl tau0 (subst_vl sigma0 s)) (hexp)|  musigma   (ren_vl tau0 (subst_vl sigma0 s)) (hexp) ]
  end
  |  subst_vl ((funcomp) (subst_vl ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  subst_vl ?theta0 ?t  =>  first [ unify   (subst_vl tau0 (subst_vl sigma0 s)) (hexp)|  musigma   (subst_vl tau0 (subst_vl sigma0 s)) (hexp) ]
  end
  |  ren_Tm ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  ren_Tm ?theta0 ?t  =>  first [ unify   (ren_Tm tau0 (ren_Tm sigma0 s)) (hexp)|  musigma   (ren_Tm tau0 (ren_Tm sigma0 s)) (hexp) ]
  end
  |  subst_Tm ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  subst_Tm ?theta0 ?t  =>  first [ unify   (subst_Tm tau0 (ren_Tm sigma0 s)) (hexp)|  musigma   (subst_Tm tau0 (ren_Tm sigma0 s)) (hexp) ]
  end
  |  subst_Tm ((funcomp) (ren_Tm ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  ren_Tm ?theta0 ?t  =>  first [ unify   (ren_Tm tau0 (subst_Tm sigma0 s)) (hexp)|  musigma   (ren_Tm tau0 (subst_Tm sigma0 s)) (hexp) ]
  end
  |  subst_Tm ((funcomp) (subst_Tm ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  subst_Tm ?theta0 ?t  =>  first [ unify   (subst_Tm tau0 (subst_Tm sigma0 s)) (hexp)|  musigma   (subst_Tm tau0 (subst_Tm sigma0 s)) (hexp) ]
  end
  |  (funcomp) (ren_tm ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_tm ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_tm tau0) ((funcomp) (ren_tm sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (ren_tm tau0) ((funcomp) (ren_tm sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_tm ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_tm ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_tm tau0) ((funcomp) (ren_tm sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (subst_tm tau0) ((funcomp) (ren_tm sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_tm ((funcomp) (ren_vl ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_tm ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_tm tau0) ((funcomp) (subst_tm sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (ren_tm tau0) ((funcomp) (subst_tm sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_tm ((funcomp) (subst_vl ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_tm ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_tm tau0) ((funcomp) (subst_tm sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (subst_tm tau0) ((funcomp) (subst_tm sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (ren_vl ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_vl ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_vl tau0) ((funcomp) (ren_vl sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (ren_vl tau0) ((funcomp) (ren_vl sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_vl ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_vl ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_vl tau0) ((funcomp) (ren_vl sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (subst_vl tau0) ((funcomp) (ren_vl sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_vl ((funcomp) (ren_vl ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_vl ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_vl tau0) ((funcomp) (subst_vl sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (ren_vl tau0) ((funcomp) (subst_vl sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_vl ((funcomp) (subst_vl ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_vl ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_vl tau0) ((funcomp) (subst_vl sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (subst_vl tau0) ((funcomp) (subst_vl sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (ren_Tm ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_Tm ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_Tm tau0) ((funcomp) (ren_Tm sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (ren_Tm tau0) ((funcomp) (ren_Tm sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_Tm ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_Tm ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_Tm tau0) ((funcomp) (ren_Tm sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (subst_Tm tau0) ((funcomp) (ren_Tm sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_Tm ((funcomp) (ren_Tm ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_Tm ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_Tm tau0) ((funcomp) (subst_Tm sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (ren_Tm tau0) ((funcomp) (subst_Tm sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_Tm ((funcomp) (subst_Tm ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_Tm ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_Tm tau0) ((funcomp) (subst_Tm sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (subst_Tm tau0) ((funcomp) (subst_Tm sigma0) sigmas)) (hexp) ]
  end
  |  (scons) (ren_tm ?sigma0 ?s) ((funcomp) (ren_tm ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (ren_tm ?tau0) ?thetah  =>  first [ unify   ((funcomp) (ren_tm sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (ren_tm sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (subst_tm ?sigma0 ?s) ((funcomp) (subst_tm ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (subst_tm ?tau0) ?thetah  =>  first [ unify   ((funcomp) (subst_tm sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (subst_tm sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (ren_vl ?sigma0 ?s) ((funcomp) (ren_vl ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (ren_vl ?tau0) ?thetah  =>  first [ unify   ((funcomp) (ren_vl sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (ren_vl sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (subst_vl ?sigma0 ?s) ((funcomp) (subst_vl ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (subst_vl ?tau0) ?thetah  =>  first [ unify   ((funcomp) (subst_vl sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (subst_vl sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (ren_Tm ?sigma0 ?s) ((funcomp) (ren_Tm ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (ren_Tm ?tau0) ?thetah  =>  first [ unify   ((funcomp) (ren_Tm sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (ren_Tm sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (subst_Tm ?sigma0 ?s) ((funcomp) (subst_Tm ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (subst_Tm ?tau0) ?thetah  =>  first [ unify   ((funcomp) (subst_Tm sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (subst_Tm sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  lam ?s0  =>  match   hexp  with
  |  lam ?t0  =>  musigma   (s0) (t0)
  end
  |  app ?s0 ?s1  =>  match   hexp  with
  |  app ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  creturn ?s0  =>  match   hexp  with
  |  creturn ?t0  =>  musigma   (s0) (t0)
  end
  |  clet ?s0 ?s1  =>  match   hexp  with
  |  clet ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  force ?s0  =>  match   hexp  with
  |  force ?t0  =>  musigma   (s0) (t0)
  end
  |  cif ?s0 ?s1 ?s2  =>  match   hexp  with
  |  cif ?t0 ?t1 ?t2  =>  musigma   (s0) (t0); musigma   (s1) (t1); musigma   (s2) (t2)
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
  |  thunk ?s0  =>  match   hexp  with
  |  thunk ?t0  =>  musigma   (s0) (t0)
  end
  |  subst_vl ?sigma0 ?s  =>  match   hexp  with
  |  subst_vl ?tau0 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0)
  end
  |  ren_vl ?sigma0 ?s  =>  match   hexp  with
  |  ren_vl ?tau0 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0)
  end
  |  (funcomp) (subst_vl ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_vl ?tau0) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0)
  end
  |  (funcomp) (ren_vl ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_vl ?tau0) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0)
  end
  |  Lam ?s0  =>  match   hexp  with
  |  Lam ?t0  =>  musigma   (s0) (t0)
  end
  |  App ?s0 ?s1  =>  match   hexp  with
  |  App ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  If ?s0 ?s1 ?s2  =>  match   hexp  with
  |  If ?t0 ?t1 ?t2  =>  musigma   (s0) (t0); musigma   (s1) (t1); musigma   (s2) (t2)
  end
  |  subst_Tm ?sigma0 ?s  =>  match   hexp  with
  |  subst_Tm ?tau0 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0)
  end
  |  ren_Tm ?sigma0 ?s  =>  match   hexp  with
  |  ren_Tm ?tau0 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0)
  end
  |  (funcomp) (subst_Tm ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_Tm ?tau0) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0)
  end
  |  (funcomp) (ren_Tm ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_Tm ?tau0) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0)
  end
  end.

Ltac  heuristics gexp hexp :=
  match   gexp  with
  |  ?s  =>  unify   (gexp) (hexp)
  |  (funcomp) (subst_tm ((funcomp) var_vl ?sigma0)) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_tm ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (subst_tm ((funcomp) var_vl sigma0)) sigma = (funcomp) (ren_tm sigma0) sigma) as eq by (renamify; reflexivity); rewrite   (eq); unify   ((funcomp) (ren_tm sigma0) sigma) (hexp); clear eq
  end
  |  subst_tm ((funcomp) var_vl ?sigma0) ?s  =>  match   hexp  with
  |  ren_tm ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (subst_tm ((funcomp) var_vl sigma0) s = ren_tm sigma0 s) as eq by (renamify; reflexivity); rewrite   (eq); unify   (ren_tm sigma0 s) (hexp); clear eq
  end
  |  (funcomp) (subst_vl ((funcomp) var_vl ?sigma0)) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_vl ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (subst_vl ((funcomp) var_vl sigma0)) sigma = (funcomp) (ren_vl sigma0) sigma) as eq by (renamify; reflexivity); rewrite   (eq); unify   ((funcomp) (ren_vl sigma0) sigma) (hexp); clear eq
  end
  |  subst_vl ((funcomp) var_vl ?sigma0) ?s  =>  match   hexp  with
  |  ren_vl ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (subst_vl ((funcomp) var_vl sigma0) s = ren_vl sigma0 s) as eq by (renamify; reflexivity); rewrite   (eq); unify   (ren_vl sigma0 s) (hexp); clear eq
  end
  |  (funcomp) (subst_Tm ((funcomp) var_Tm ?sigma0)) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_Tm ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (subst_Tm ((funcomp) var_Tm sigma0)) sigma = (funcomp) (ren_Tm sigma0) sigma) as eq by (renamify; reflexivity); rewrite   (eq); unify   ((funcomp) (ren_Tm sigma0) sigma) (hexp); clear eq
  end
  |  subst_Tm ((funcomp) var_Tm ?sigma0) ?s  =>  match   hexp  with
  |  ren_Tm ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (subst_Tm ((funcomp) var_Tm sigma0) s = ren_Tm sigma0 s) as eq by (renamify; reflexivity); rewrite   (eq); unify   (ren_Tm sigma0 s) (hexp); clear eq
  end
  |  (funcomp) (ren_tm ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_tm ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_tm sigma0) sigma = (funcomp) (subst_tm ((funcomp) var_vl sigma0)) sigma) as eq by (substify; reflexivity); rewrite   (eq); unify   ((funcomp) (subst_tm ((funcomp) var_vl sigma0)) sigma) (hexp); clear eq
  end
  |  ren_tm ?sigma0 ?s  =>  match   hexp  with
  |  subst_tm ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (ren_tm sigma0 s = subst_tm ((funcomp) var_vl sigma0) s) as eq by (substify; reflexivity); rewrite   (eq); unify   (subst_tm ((funcomp) var_vl sigma0) s) (hexp); clear eq
  end
  |  (funcomp) (ren_vl ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_vl ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_vl sigma0) sigma = (funcomp) (subst_vl ((funcomp) var_vl sigma0)) sigma) as eq by (substify; reflexivity); rewrite   (eq); unify   ((funcomp) (subst_vl ((funcomp) var_vl sigma0)) sigma) (hexp); clear eq
  end
  |  ren_vl ?sigma0 ?s  =>  match   hexp  with
  |  subst_vl ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (ren_vl sigma0 s = subst_vl ((funcomp) var_vl sigma0) s) as eq by (substify; reflexivity); rewrite   (eq); unify   (subst_vl ((funcomp) var_vl sigma0) s) (hexp); clear eq
  end
  |  (funcomp) (ren_Tm ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_Tm ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_Tm sigma0) sigma = (funcomp) (subst_Tm ((funcomp) var_Tm sigma0)) sigma) as eq by (substify; reflexivity); rewrite   (eq); unify   ((funcomp) (subst_Tm ((funcomp) var_Tm sigma0)) sigma) (hexp); clear eq
  end
  |  ren_Tm ?sigma0 ?s  =>  match   hexp  with
  |  subst_Tm ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (ren_Tm sigma0 s = subst_Tm ((funcomp) var_Tm sigma0) s) as eq by (substify; reflexivity); rewrite   (eq); unify   (subst_Tm ((funcomp) var_Tm sigma0) s) (hexp); clear eq
  end
  |  ?s  =>  musigma   (gexp) (hexp)
  |  subst_tm ((scons) ?svl0 ((funcomp) var_vl ?sigmavl)) ?stm  =>  match   hexp  with
  |  subst_tm ((scons) ?tvl0 var_vl) ?ttm  =>  unify   (subst_tm ((scons) svl0 var_vl) (ren_tm ((scons) (var_zero) ((funcomp) (shift) sigmavl)) stm)) (hexp)
  end
  |  subst_tm ((scons) ?svl0 ((funcomp) var_vl ?sigmavl)) ?stm  =>  match   hexp  with
  |  subst_tm ((scons) ?tvl0 var_vl) ?ttm  =>  unify   (subst_tm ((scons) svl0 var_vl) (ren_tm ((scons) (var_zero) ((funcomp) (shift) sigmavl)) stm)) (hexp)
  end
  |  subst_tm ((scons) ?svl0 ?sigmavl) ?stm  =>  match   hexp  with
  |  subst_tm ((scons) ?tvl0 var_vl) ?ttm  =>  unify   (subst_tm ((scons) svl0 var_vl) (subst_tm ((scons) (var_vl (var_zero)) ((funcomp) (ren_vl (shift)) sigmavl)) stm)) (hexp)
  end
  |  subst_tm ((scons) ?svl0 ?sigmavl) ?stm  =>  match   hexp  with
  |  subst_tm ((scons) ?tvl0 var_vl) ?ttm  =>  unify   (subst_tm ((scons) svl0 var_vl) (subst_tm ((scons) (var_vl (var_zero)) ((funcomp) (ren_vl (shift)) sigmavl)) stm)) (hexp)
  end
  |  subst_Tm ((scons) ?sTm0 ((funcomp) var_Tm ?sigmaTm)) ?sTm  =>  match   hexp  with
  |  subst_Tm ((scons) ?tTm0 var_Tm) ?tTm  =>  unify   (subst_Tm ((scons) sTm0 var_Tm) (ren_Tm ((scons) (var_zero) ((funcomp) (shift) sigmaTm)) sTm)) (hexp)
  end
  |  subst_Tm ((scons) ?sTm0 ?sigmaTm) ?sTm  =>  match   hexp  with
  |  subst_Tm ((scons) ?tTm0 var_Tm) ?tTm  =>  unify   (subst_Tm ((scons) sTm0 var_Tm) (subst_Tm ((scons) (var_Tm (var_zero)) ((funcomp) (ren_Tm (shift)) sigmaTm)) sTm)) (hexp)
  end
  |  ?s  =>  match   hexp  with
  |  subst_tm ?sigma0 ?t  =>  unify   (subst_tm var_vl s) (hexp)
  |  ren_tm ?sigma0 ?t  =>  unify   (ren_tm (id) s) (hexp)
  |  subst_vl ?sigma0 ?t  =>  unify   (subst_vl var_vl s) (hexp)
  |  ren_vl ?sigma0 ?t  =>  unify   (ren_vl (id) s) (hexp)
  |  subst_Tm ?sigma0 ?t  =>  unify   (subst_Tm var_Tm s) (hexp)
  |  ren_Tm ?sigma0 ?t  =>  unify   (ren_Tm (id) s) (hexp)
  end
  |  lam ?s0  =>  match   hexp  with
  |  lam ?t0  =>  heuristics   (s0) (t0)
  end
  |  app ?s0 ?s1  =>  match   hexp  with
  |  app ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  creturn ?s0  =>  match   hexp  with
  |  creturn ?t0  =>  heuristics   (s0) (t0)
  end
  |  clet ?s0 ?s1  =>  match   hexp  with
  |  clet ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  force ?s0  =>  match   hexp  with
  |  force ?t0  =>  heuristics   (s0) (t0)
  end
  |  cif ?s0 ?s1 ?s2  =>  match   hexp  with
  |  cif ?t0 ?t1 ?t2  =>  heuristics   (s0) (t0); heuristics   (s1) (t1); heuristics   (s2) (t2)
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
  |  thunk ?s0  =>  match   hexp  with
  |  thunk ?t0  =>  heuristics   (s0) (t0)
  end
  |  subst_vl ?sigma0 ?s  =>  match   hexp  with
  |  subst_vl ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  ren_vl ?sigma0 ?s  =>  match   hexp  with
  |  ren_vl ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (subst_vl ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_vl ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (ren_vl ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_vl ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  |  Lam ?s0  =>  match   hexp  with
  |  Lam ?t0  =>  heuristics   (s0) (t0)
  end
  |  App ?s0 ?s1  =>  match   hexp  with
  |  App ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  If ?s0 ?s1 ?s2  =>  match   hexp  with
  |  If ?t0 ?t1 ?t2  =>  heuristics   (s0) (t0); heuristics   (s1) (t1); heuristics   (s2) (t2)
  end
  |  subst_Tm ?sigma0 ?s  =>  match   hexp  with
  |  subst_Tm ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  ren_Tm ?sigma0 ?s  =>  match   hexp  with
  |  ren_Tm ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (subst_Tm ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_Tm ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (ren_Tm ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_Tm ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
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
