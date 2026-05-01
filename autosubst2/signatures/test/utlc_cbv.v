Require Export fintype.



Section nfne.
Inductive nf (nne : nat) : Type :=
  | val : ne  (nne) -> nf (nne)
  | lam : nf  ((S) nne) -> nf (nne)
 with ne (nne : nat) : Type :=
  | var_ne : (fin) (nne) -> ne (nne)
  | app : ne  (nne) -> nf  (nne) -> ne (nne).

Lemma congr_val { mne : nat } { s0 : ne  (mne) } { t0 : ne  (mne) } (H1 : s0 = t0) : val (mne) s0 = val (mne) t0 .
Proof. congruence. Qed.

Lemma congr_lam { mne : nat } { s0 : nf  ((S) mne) } { t0 : nf  ((S) mne) } (H1 : s0 = t0) : lam (mne) s0 = lam (mne) t0 .
Proof. congruence. Qed.

Lemma congr_app { mne : nat } { s0 : ne  (mne) } { s1 : nf  (mne) } { t0 : ne  (mne) } { t1 : nf  (mne) } (H1 : s0 = t0) (H2 : s1 = t1) : app (mne) s0 s1 = app (mne) t0 t1 .
Proof. congruence. Qed.

Definition upRen_ne_ne { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Fixpoint ren_nf { mne : nat } { nne : nat } (xine : (fin) (mne) -> (fin) (nne)) (s : nf (mne)) : nf (nne) :=
    match s return nf (nne) with
    | val (_) s0 => val (nne) ((ren_ne xine) s0)
    | lam (_) s0 => lam (nne) ((ren_nf (upRen_ne_ne xine)) s0)
    end
 with ren_ne { mne : nat } { nne : nat } (xine : (fin) (mne) -> (fin) (nne)) (s : ne (mne)) : ne (nne) :=
    match s return ne (nne) with
    | var_ne (_) s => (var_ne (nne)) (xine s)
    | app (_) s0 s1 => app (nne) ((ren_ne xine) s0) ((ren_nf xine) s1)
    end.

Definition up_ne_ne { m : nat } { nne : nat } (sigma : (fin) (m) -> ne (nne)) : (fin) ((S) (m)) -> ne ((S) nne) :=
  (scons) ((var_ne ((S) nne)) (var_zero)) ((funcomp) (ren_ne (shift)) sigma).

Fixpoint subst_nf { mne : nat } { nne : nat } (sigmane : (fin) (mne) -> ne (nne)) (s : nf (mne)) : nf (nne) :=
    match s return nf (nne) with
    | val (_) s0 => val (nne) ((subst_ne sigmane) s0)
    | lam (_) s0 => lam (nne) ((subst_nf (up_ne_ne sigmane)) s0)
    end
 with subst_ne { mne : nat } { nne : nat } (sigmane : (fin) (mne) -> ne (nne)) (s : ne (mne)) : ne (nne) :=
    match s return ne (nne) with
    | var_ne (_) s => sigmane s
    | app (_) s0 s1 => app (nne) ((subst_ne sigmane) s0) ((subst_nf sigmane) s1)
    end.

Definition upId_ne_ne { mne : nat } (sigma : (fin) (mne) -> ne (mne)) (Eq : forall x, sigma x = (var_ne (mne)) x) : forall x, (up_ne_ne sigma) x = (var_ne ((S) mne)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_ne (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint idSubst_nf { mne : nat } (sigmane : (fin) (mne) -> ne (mne)) (Eqne : forall x, sigmane x = (var_ne (mne)) x) (s : nf (mne)) : subst_nf sigmane s = s :=
    match s return subst_nf sigmane s = s with
    | val (_) s0 => congr_val ((idSubst_ne sigmane Eqne) s0)
    | lam (_) s0 => congr_lam ((idSubst_nf (up_ne_ne sigmane) (upId_ne_ne (_) Eqne)) s0)
    end
 with idSubst_ne { mne : nat } (sigmane : (fin) (mne) -> ne (mne)) (Eqne : forall x, sigmane x = (var_ne (mne)) x) (s : ne (mne)) : subst_ne sigmane s = s :=
    match s return subst_ne sigmane s = s with
    | var_ne (_) s => Eqne s
    | app (_) s0 s1 => congr_app ((idSubst_ne sigmane Eqne) s0) ((idSubst_nf sigmane Eqne) s1)
    end.

Definition upExtRen_ne_ne { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_ne_ne xi) x = (upRen_ne_ne zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint extRen_nf { mne : nat } { nne : nat } (xine : (fin) (mne) -> (fin) (nne)) (zetane : (fin) (mne) -> (fin) (nne)) (Eqne : forall x, xine x = zetane x) (s : nf (mne)) : ren_nf xine s = ren_nf zetane s :=
    match s return ren_nf xine s = ren_nf zetane s with
    | val (_) s0 => congr_val ((extRen_ne xine zetane Eqne) s0)
    | lam (_) s0 => congr_lam ((extRen_nf (upRen_ne_ne xine) (upRen_ne_ne zetane) (upExtRen_ne_ne (_) (_) Eqne)) s0)
    end
 with extRen_ne { mne : nat } { nne : nat } (xine : (fin) (mne) -> (fin) (nne)) (zetane : (fin) (mne) -> (fin) (nne)) (Eqne : forall x, xine x = zetane x) (s : ne (mne)) : ren_ne xine s = ren_ne zetane s :=
    match s return ren_ne xine s = ren_ne zetane s with
    | var_ne (_) s => (ap) (var_ne (nne)) (Eqne s)
    | app (_) s0 s1 => congr_app ((extRen_ne xine zetane Eqne) s0) ((extRen_nf xine zetane Eqne) s1)
    end.

Definition upExt_ne_ne { m : nat } { nne : nat } (sigma : (fin) (m) -> ne (nne)) (tau : (fin) (m) -> ne (nne)) (Eq : forall x, sigma x = tau x) : forall x, (up_ne_ne sigma) x = (up_ne_ne tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_ne (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint ext_nf { mne : nat } { nne : nat } (sigmane : (fin) (mne) -> ne (nne)) (taune : (fin) (mne) -> ne (nne)) (Eqne : forall x, sigmane x = taune x) (s : nf (mne)) : subst_nf sigmane s = subst_nf taune s :=
    match s return subst_nf sigmane s = subst_nf taune s with
    | val (_) s0 => congr_val ((ext_ne sigmane taune Eqne) s0)
    | lam (_) s0 => congr_lam ((ext_nf (up_ne_ne sigmane) (up_ne_ne taune) (upExt_ne_ne (_) (_) Eqne)) s0)
    end
 with ext_ne { mne : nat } { nne : nat } (sigmane : (fin) (mne) -> ne (nne)) (taune : (fin) (mne) -> ne (nne)) (Eqne : forall x, sigmane x = taune x) (s : ne (mne)) : subst_ne sigmane s = subst_ne taune s :=
    match s return subst_ne sigmane s = subst_ne taune s with
    | var_ne (_) s => Eqne s
    | app (_) s0 s1 => congr_app ((ext_ne sigmane taune Eqne) s0) ((ext_nf sigmane taune Eqne) s1)
    end.

Definition up_ren_ren_ne_ne { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_ne_ne tau) (upRen_ne_ne xi)) x = (upRen_ne_ne theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_nf { kne : nat } { lne : nat } { mne : nat } (xine : (fin) (mne) -> (fin) (kne)) (zetane : (fin) (kne) -> (fin) (lne)) (rhone : (fin) (mne) -> (fin) (lne)) (Eqne : forall x, ((funcomp) zetane xine) x = rhone x) (s : nf (mne)) : ren_nf zetane (ren_nf xine s) = ren_nf rhone s :=
    match s return ren_nf zetane (ren_nf xine s) = ren_nf rhone s with
    | val (_) s0 => congr_val ((compRenRen_ne xine zetane rhone Eqne) s0)
    | lam (_) s0 => congr_lam ((compRenRen_nf (upRen_ne_ne xine) (upRen_ne_ne zetane) (upRen_ne_ne rhone) (up_ren_ren (_) (_) (_) Eqne)) s0)
    end
 with compRenRen_ne { kne : nat } { lne : nat } { mne : nat } (xine : (fin) (mne) -> (fin) (kne)) (zetane : (fin) (kne) -> (fin) (lne)) (rhone : (fin) (mne) -> (fin) (lne)) (Eqne : forall x, ((funcomp) zetane xine) x = rhone x) (s : ne (mne)) : ren_ne zetane (ren_ne xine s) = ren_ne rhone s :=
    match s return ren_ne zetane (ren_ne xine s) = ren_ne rhone s with
    | var_ne (_) s => (ap) (var_ne (lne)) (Eqne s)
    | app (_) s0 s1 => congr_app ((compRenRen_ne xine zetane rhone Eqne) s0) ((compRenRen_nf xine zetane rhone Eqne) s1)
    end.

Definition up_ren_subst_ne_ne { k : nat } { l : nat } { mne : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> ne (mne)) (theta : (fin) (k) -> ne (mne)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_ne_ne tau) (upRen_ne_ne xi)) x = (up_ne_ne theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_ne (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint compRenSubst_nf { kne : nat } { lne : nat } { mne : nat } (xine : (fin) (mne) -> (fin) (kne)) (taune : (fin) (kne) -> ne (lne)) (thetane : (fin) (mne) -> ne (lne)) (Eqne : forall x, ((funcomp) taune xine) x = thetane x) (s : nf (mne)) : subst_nf taune (ren_nf xine s) = subst_nf thetane s :=
    match s return subst_nf taune (ren_nf xine s) = subst_nf thetane s with
    | val (_) s0 => congr_val ((compRenSubst_ne xine taune thetane Eqne) s0)
    | lam (_) s0 => congr_lam ((compRenSubst_nf (upRen_ne_ne xine) (up_ne_ne taune) (up_ne_ne thetane) (up_ren_subst_ne_ne (_) (_) (_) Eqne)) s0)
    end
 with compRenSubst_ne { kne : nat } { lne : nat } { mne : nat } (xine : (fin) (mne) -> (fin) (kne)) (taune : (fin) (kne) -> ne (lne)) (thetane : (fin) (mne) -> ne (lne)) (Eqne : forall x, ((funcomp) taune xine) x = thetane x) (s : ne (mne)) : subst_ne taune (ren_ne xine s) = subst_ne thetane s :=
    match s return subst_ne taune (ren_ne xine s) = subst_ne thetane s with
    | var_ne (_) s => Eqne s
    | app (_) s0 s1 => congr_app ((compRenSubst_ne xine taune thetane Eqne) s0) ((compRenSubst_nf xine taune thetane Eqne) s1)
    end.

Definition up_subst_ren_ne_ne { k : nat } { lne : nat } { mne : nat } (sigma : (fin) (k) -> ne (lne)) (zetane : (fin) (lne) -> (fin) (mne)) (theta : (fin) (k) -> ne (mne)) (Eq : forall x, ((funcomp) (ren_ne zetane) sigma) x = theta x) : forall x, ((funcomp) (ren_ne (upRen_ne_ne zetane)) (up_ne_ne sigma)) x = (up_ne_ne theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_ne (shift) (upRen_ne_ne zetane) ((funcomp) (shift) zetane) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_ne zetane (shift) ((funcomp) (shift) zetane) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_ne (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstRen_nf { kne : nat } { lne : nat } { mne : nat } (sigmane : (fin) (mne) -> ne (kne)) (zetane : (fin) (kne) -> (fin) (lne)) (thetane : (fin) (mne) -> ne (lne)) (Eqne : forall x, ((funcomp) (ren_ne zetane) sigmane) x = thetane x) (s : nf (mne)) : ren_nf zetane (subst_nf sigmane s) = subst_nf thetane s :=
    match s return ren_nf zetane (subst_nf sigmane s) = subst_nf thetane s with
    | val (_) s0 => congr_val ((compSubstRen_ne sigmane zetane thetane Eqne) s0)
    | lam (_) s0 => congr_lam ((compSubstRen_nf (up_ne_ne sigmane) (upRen_ne_ne zetane) (up_ne_ne thetane) (up_subst_ren_ne_ne (_) (_) (_) Eqne)) s0)
    end
 with compSubstRen_ne { kne : nat } { lne : nat } { mne : nat } (sigmane : (fin) (mne) -> ne (kne)) (zetane : (fin) (kne) -> (fin) (lne)) (thetane : (fin) (mne) -> ne (lne)) (Eqne : forall x, ((funcomp) (ren_ne zetane) sigmane) x = thetane x) (s : ne (mne)) : ren_ne zetane (subst_ne sigmane s) = subst_ne thetane s :=
    match s return ren_ne zetane (subst_ne sigmane s) = subst_ne thetane s with
    | var_ne (_) s => Eqne s
    | app (_) s0 s1 => congr_app ((compSubstRen_ne sigmane zetane thetane Eqne) s0) ((compSubstRen_nf sigmane zetane thetane Eqne) s1)
    end.

Definition up_subst_subst_ne_ne { k : nat } { lne : nat } { mne : nat } (sigma : (fin) (k) -> ne (lne)) (taune : (fin) (lne) -> ne (mne)) (theta : (fin) (k) -> ne (mne)) (Eq : forall x, ((funcomp) (subst_ne taune) sigma) x = theta x) : forall x, ((funcomp) (subst_ne (up_ne_ne taune)) (up_ne_ne sigma)) x = (up_ne_ne theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_ne (shift) (up_ne_ne taune) ((funcomp) (up_ne_ne taune) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_ne taune (shift) ((funcomp) (ren_ne (shift)) taune) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_ne (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstSubst_nf { kne : nat } { lne : nat } { mne : nat } (sigmane : (fin) (mne) -> ne (kne)) (taune : (fin) (kne) -> ne (lne)) (thetane : (fin) (mne) -> ne (lne)) (Eqne : forall x, ((funcomp) (subst_ne taune) sigmane) x = thetane x) (s : nf (mne)) : subst_nf taune (subst_nf sigmane s) = subst_nf thetane s :=
    match s return subst_nf taune (subst_nf sigmane s) = subst_nf thetane s with
    | val (_) s0 => congr_val ((compSubstSubst_ne sigmane taune thetane Eqne) s0)
    | lam (_) s0 => congr_lam ((compSubstSubst_nf (up_ne_ne sigmane) (up_ne_ne taune) (up_ne_ne thetane) (up_subst_subst_ne_ne (_) (_) (_) Eqne)) s0)
    end
 with compSubstSubst_ne { kne : nat } { lne : nat } { mne : nat } (sigmane : (fin) (mne) -> ne (kne)) (taune : (fin) (kne) -> ne (lne)) (thetane : (fin) (mne) -> ne (lne)) (Eqne : forall x, ((funcomp) (subst_ne taune) sigmane) x = thetane x) (s : ne (mne)) : subst_ne taune (subst_ne sigmane s) = subst_ne thetane s :=
    match s return subst_ne taune (subst_ne sigmane s) = subst_ne thetane s with
    | var_ne (_) s => Eqne s
    | app (_) s0 s1 => congr_app ((compSubstSubst_ne sigmane taune thetane Eqne) s0) ((compSubstSubst_nf sigmane taune thetane Eqne) s1)
    end.

Definition rinstInst_up_ne_ne { m : nat } { nne : nat } (xi : (fin) (m) -> (fin) (nne)) (sigma : (fin) (m) -> ne (nne)) (Eq : forall x, ((funcomp) (var_ne (nne)) xi) x = sigma x) : forall x, ((funcomp) (var_ne ((S) nne)) (upRen_ne_ne xi)) x = (up_ne_ne sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_ne (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint rinst_inst_nf { mne : nat } { nne : nat } (xine : (fin) (mne) -> (fin) (nne)) (sigmane : (fin) (mne) -> ne (nne)) (Eqne : forall x, ((funcomp) (var_ne (nne)) xine) x = sigmane x) (s : nf (mne)) : ren_nf xine s = subst_nf sigmane s :=
    match s return ren_nf xine s = subst_nf sigmane s with
    | val (_) s0 => congr_val ((rinst_inst_ne xine sigmane Eqne) s0)
    | lam (_) s0 => congr_lam ((rinst_inst_nf (upRen_ne_ne xine) (up_ne_ne sigmane) (rinstInst_up_ne_ne (_) (_) Eqne)) s0)
    end
 with rinst_inst_ne { mne : nat } { nne : nat } (xine : (fin) (mne) -> (fin) (nne)) (sigmane : (fin) (mne) -> ne (nne)) (Eqne : forall x, ((funcomp) (var_ne (nne)) xine) x = sigmane x) (s : ne (mne)) : ren_ne xine s = subst_ne sigmane s :=
    match s return ren_ne xine s = subst_ne sigmane s with
    | var_ne (_) s => Eqne s
    | app (_) s0 s1 => congr_app ((rinst_inst_ne xine sigmane Eqne) s0) ((rinst_inst_nf xine sigmane Eqne) s1)
    end.

Lemma rinstInst_nf { mne : nat } { nne : nat } (xine : (fin) (mne) -> (fin) (nne)) : ren_nf xine = subst_nf ((funcomp) (var_ne (nne)) xine) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_nf xine (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_ne { mne : nat } { nne : nat } (xine : (fin) (mne) -> (fin) (nne)) : ren_ne xine = subst_ne ((funcomp) (var_ne (nne)) xine) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_ne xine (_) (fun n => eq_refl) x)). Qed.

Lemma instId_nf { mne : nat } : subst_nf (var_ne (mne)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_nf (var_ne (mne)) (fun n => eq_refl) ((id) x))). Qed.

Lemma instId_ne { mne : nat } : subst_ne (var_ne (mne)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_ne (var_ne (mne)) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_nf { mne : nat } : @ren_nf (mne) (mne) (id) = id .
Proof. exact ((eq_trans) (rinstInst_nf ((id) (_))) instId_nf). Qed.

Lemma rinstId_ne { mne : nat } : @ren_ne (mne) (mne) (id) = id .
Proof. exact ((eq_trans) (rinstInst_ne ((id) (_))) instId_ne). Qed.

Lemma varL_ne { mne : nat } { nne : nat } (sigmane : (fin) (mne) -> ne (nne)) : (funcomp) (subst_ne sigmane) (var_ne (mne)) = sigmane .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_ne { mne : nat } { nne : nat } (xine : (fin) (mne) -> (fin) (nne)) : (funcomp) (ren_ne xine) (var_ne (mne)) = (funcomp) (var_ne (nne)) xine .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_nf { kne : nat } { lne : nat } { mne : nat } (sigmane : (fin) (mne) -> ne (kne)) (taune : (fin) (kne) -> ne (lne)) (s : nf (mne)) : subst_nf taune (subst_nf sigmane s) = subst_nf ((funcomp) (subst_ne taune) sigmane) s .
Proof. exact (compSubstSubst_nf sigmane taune (_) (fun n => eq_refl) s). Qed.

Lemma compComp_ne { kne : nat } { lne : nat } { mne : nat } (sigmane : (fin) (mne) -> ne (kne)) (taune : (fin) (kne) -> ne (lne)) (s : ne (mne)) : subst_ne taune (subst_ne sigmane s) = subst_ne ((funcomp) (subst_ne taune) sigmane) s .
Proof. exact (compSubstSubst_ne sigmane taune (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_nf { kne : nat } { lne : nat } { mne : nat } (sigmane : (fin) (mne) -> ne (kne)) (taune : (fin) (kne) -> ne (lne)) : (funcomp) (subst_nf taune) (subst_nf sigmane) = subst_nf ((funcomp) (subst_ne taune) sigmane) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_nf sigmane taune n)). Qed.

Lemma compComp'_ne { kne : nat } { lne : nat } { mne : nat } (sigmane : (fin) (mne) -> ne (kne)) (taune : (fin) (kne) -> ne (lne)) : (funcomp) (subst_ne taune) (subst_ne sigmane) = subst_ne ((funcomp) (subst_ne taune) sigmane) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_ne sigmane taune n)). Qed.

Lemma compRen_nf { kne : nat } { lne : nat } { mne : nat } (sigmane : (fin) (mne) -> ne (kne)) (zetane : (fin) (kne) -> (fin) (lne)) (s : nf (mne)) : ren_nf zetane (subst_nf sigmane s) = subst_nf ((funcomp) (ren_ne zetane) sigmane) s .
Proof. exact (compSubstRen_nf sigmane zetane (_) (fun n => eq_refl) s). Qed.

Lemma compRen_ne { kne : nat } { lne : nat } { mne : nat } (sigmane : (fin) (mne) -> ne (kne)) (zetane : (fin) (kne) -> (fin) (lne)) (s : ne (mne)) : ren_ne zetane (subst_ne sigmane s) = subst_ne ((funcomp) (ren_ne zetane) sigmane) s .
Proof. exact (compSubstRen_ne sigmane zetane (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_nf { kne : nat } { lne : nat } { mne : nat } (sigmane : (fin) (mne) -> ne (kne)) (zetane : (fin) (kne) -> (fin) (lne)) : (funcomp) (ren_nf zetane) (subst_nf sigmane) = subst_nf ((funcomp) (ren_ne zetane) sigmane) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_nf sigmane zetane n)). Qed.

Lemma compRen'_ne { kne : nat } { lne : nat } { mne : nat } (sigmane : (fin) (mne) -> ne (kne)) (zetane : (fin) (kne) -> (fin) (lne)) : (funcomp) (ren_ne zetane) (subst_ne sigmane) = subst_ne ((funcomp) (ren_ne zetane) sigmane) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_ne sigmane zetane n)). Qed.

Lemma renComp_nf { kne : nat } { lne : nat } { mne : nat } (xine : (fin) (mne) -> (fin) (kne)) (taune : (fin) (kne) -> ne (lne)) (s : nf (mne)) : subst_nf taune (ren_nf xine s) = subst_nf ((funcomp) taune xine) s .
Proof. exact (compRenSubst_nf xine taune (_) (fun n => eq_refl) s). Qed.

Lemma renComp_ne { kne : nat } { lne : nat } { mne : nat } (xine : (fin) (mne) -> (fin) (kne)) (taune : (fin) (kne) -> ne (lne)) (s : ne (mne)) : subst_ne taune (ren_ne xine s) = subst_ne ((funcomp) taune xine) s .
Proof. exact (compRenSubst_ne xine taune (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_nf { kne : nat } { lne : nat } { mne : nat } (xine : (fin) (mne) -> (fin) (kne)) (taune : (fin) (kne) -> ne (lne)) : (funcomp) (subst_nf taune) (ren_nf xine) = subst_nf ((funcomp) taune xine) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_nf xine taune n)). Qed.

Lemma renComp'_ne { kne : nat } { lne : nat } { mne : nat } (xine : (fin) (mne) -> (fin) (kne)) (taune : (fin) (kne) -> ne (lne)) : (funcomp) (subst_ne taune) (ren_ne xine) = subst_ne ((funcomp) taune xine) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_ne xine taune n)). Qed.

Lemma renRen_nf { kne : nat } { lne : nat } { mne : nat } (xine : (fin) (mne) -> (fin) (kne)) (zetane : (fin) (kne) -> (fin) (lne)) (s : nf (mne)) : ren_nf zetane (ren_nf xine s) = ren_nf ((funcomp) zetane xine) s .
Proof. exact (compRenRen_nf xine zetane (_) (fun n => eq_refl) s). Qed.

Lemma renRen_ne { kne : nat } { lne : nat } { mne : nat } (xine : (fin) (mne) -> (fin) (kne)) (zetane : (fin) (kne) -> (fin) (lne)) (s : ne (mne)) : ren_ne zetane (ren_ne xine s) = ren_ne ((funcomp) zetane xine) s .
Proof. exact (compRenRen_ne xine zetane (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_nf { kne : nat } { lne : nat } { mne : nat } (xine : (fin) (mne) -> (fin) (kne)) (zetane : (fin) (kne) -> (fin) (lne)) : (funcomp) (ren_nf zetane) (ren_nf xine) = ren_nf ((funcomp) zetane xine) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_nf xine zetane n)). Qed.

Lemma renRen'_ne { kne : nat } { lne : nat } { mne : nat } (xine : (fin) (mne) -> (fin) (kne)) (zetane : (fin) (kne) -> (fin) (lne)) : (funcomp) (ren_ne zetane) (ren_ne xine) = ren_ne ((funcomp) zetane xine) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_ne xine zetane n)). Qed.

End nfne.

Arguments val {nne}.

Arguments lam {nne}.

Arguments var_ne {nne}.

Arguments app {nne}.

Global Instance Subst_nf { mne : nat } { nne : nat } : Subst1 ((fin) (mne) -> ne (nne)) (nf (mne)) (nf (nne)) := @subst_nf (mne) (nne) .

Global Instance Subst_ne { mne : nat } { nne : nat } : Subst1 ((fin) (mne) -> ne (nne)) (ne (mne)) (ne (nne)) := @subst_ne (mne) (nne) .

Global Instance Ren_nf { mne : nat } { nne : nat } : Ren1 ((fin) (mne) -> (fin) (nne)) (nf (mne)) (nf (nne)) := @ren_nf (mne) (nne) .

Global Instance Ren_ne { mne : nat } { nne : nat } : Ren1 ((fin) (mne) -> (fin) (nne)) (ne (mne)) (ne (nne)) := @ren_ne (mne) (nne) .

Global Instance VarInstance_ne { mne : nat } : Var ((fin) (mne)) (ne (mne)) := @var_ne (mne) .

Notation "x '__ne'" := (var_ne x) (at level 5, format "x __ne") : subst_scope.

Notation "x '__ne'" := (@ids (_) (_) VarInstance_ne x) (at level 5, only printing, format "x __ne") : subst_scope.

Notation "'var'" := (var_ne) (only printing, at level 1) : subst_scope.

Class Up_ne X Y := up_ne : X -> Y.

Notation "↑__ne" := (up_ne) (only printing) : subst_scope.

Notation "↑__ne" := (up_ne_ne) (only printing) : subst_scope.

Global Instance Up_ne_ne { m : nat } { nne : nat } : Up_ne (_) (_) := @up_ne_ne (m) (nne) .

Notation "s [ sigmane ]" := (subst_nf sigmane s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmane ]" := (subst_nf sigmane) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xine ⟩" := (ren_nf xine s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xine ⟩" := (ren_nf xine) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmane ]" := (subst_ne sigmane s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmane ]" := (subst_ne sigmane) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xine ⟩" := (ren_ne xine s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xine ⟩" := (ren_ne xine) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_nf,  Subst_ne,  Ren_nf,  Ren_ne,  VarInstance_ne.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_nf,  Subst_ne,  Ren_nf,  Ren_ne,  VarInstance_ne in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_nf| progress rewrite ?compComp_nf| progress rewrite ?compComp'_nf| progress rewrite ?instId_ne| progress rewrite ?compComp_ne| progress rewrite ?compComp'_ne| progress rewrite ?rinstId_nf| progress rewrite ?compRen_nf| progress rewrite ?compRen'_nf| progress rewrite ?renComp_nf| progress rewrite ?renComp'_nf| progress rewrite ?renRen_nf| progress rewrite ?renRen'_nf| progress rewrite ?rinstId_ne| progress rewrite ?compRen_ne| progress rewrite ?compRen'_ne| progress rewrite ?renComp_ne| progress rewrite ?renComp'_ne| progress rewrite ?renRen_ne| progress rewrite ?renRen'_ne| progress rewrite ?varL_ne| progress rewrite ?varLRen_ne| progress (unfold up_ren, upRen_ne_ne, up_ne_ne)| progress (cbn [subst_nf subst_ne ren_nf ren_ne])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_nf in *| progress rewrite ?compComp_nf in *| progress rewrite ?compComp'_nf in *| progress rewrite ?instId_ne in *| progress rewrite ?compComp_ne in *| progress rewrite ?compComp'_ne in *| progress rewrite ?rinstId_nf in *| progress rewrite ?compRen_nf in *| progress rewrite ?compRen'_nf in *| progress rewrite ?renComp_nf in *| progress rewrite ?renComp'_nf in *| progress rewrite ?renRen_nf in *| progress rewrite ?renRen'_nf in *| progress rewrite ?rinstId_ne in *| progress rewrite ?compRen_ne in *| progress rewrite ?compRen'_ne in *| progress rewrite ?renComp_ne in *| progress rewrite ?renComp'_ne in *| progress rewrite ?renRen_ne in *| progress rewrite ?renRen'_ne in *| progress rewrite ?varL_ne in *| progress rewrite ?varLRen_ne in *| progress (unfold up_ren, upRen_ne_ne, up_ne_ne in *)| progress (cbn [subst_nf subst_ne ren_nf ren_ne] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_nf); try repeat (erewrite rinstInst_ne).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_nf); try repeat (erewrite <- rinstInst_ne).

(** as_apply follows **)

Ltac  musigma gexp hexp :=
  match   gexp  with
  |  ?s  =>  unify   (gexp) (hexp)
  |  val (subst_ne ?sigma0 ?s0)  =>  first [ unify   (subst_nf sigma0 (val s0)) (hexp)|  musigma   (subst_nf sigma0 (val s0)) (hexp) ]
  |  lam (subst_nf ((scons) (var_ne (var_zero)) ((funcomp) (ren_ne (shift)) ?sigma0)) ?s0)  =>  first [ unify   (subst_nf sigma0 (lam s0)) (hexp)|  musigma   (subst_nf sigma0 (lam s0)) (hexp) ]
  |  val (ren_ne ?sigma0 ?s0)  =>  first [ unify   (ren_nf sigma0 (val s0)) (hexp)|  musigma   (ren_nf sigma0 (val s0)) (hexp) ]
  |  lam (ren_nf ((scons) (var_zero) ((funcomp) (shift) ?sigma0)) ?s0)  =>  first [ unify   (ren_nf sigma0 (lam s0)) (hexp)|  musigma   (ren_nf sigma0 (lam s0)) (hexp) ]
  |  app (subst_ne ?sigma0 ?s0) (subst_nf ?sigma0 ?s1)  =>  first [ unify   (subst_ne sigma0 (app s0 s1)) (hexp)|  musigma   (subst_ne sigma0 (app s0 s1)) (hexp) ]
  |  app (ren_ne ?sigma0 ?s0) (ren_nf ?sigma0 ?s1)  =>  first [ unify   (ren_ne sigma0 (app s0 s1)) (hexp)|  musigma   (ren_ne sigma0 (app s0 s1)) (hexp) ]
  |  ren_nf ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  ren_nf ?theta0 ?t  =>  first [ unify   (ren_nf tau0 (ren_nf sigma0 s)) (hexp)|  musigma   (ren_nf tau0 (ren_nf sigma0 s)) (hexp) ]
  end
  |  subst_nf ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  subst_nf ?theta0 ?t  =>  first [ unify   (subst_nf tau0 (ren_nf sigma0 s)) (hexp)|  musigma   (subst_nf tau0 (ren_nf sigma0 s)) (hexp) ]
  end
  |  subst_nf ((funcomp) (ren_ne ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  ren_nf ?theta0 ?t  =>  first [ unify   (ren_nf tau0 (subst_nf sigma0 s)) (hexp)|  musigma   (ren_nf tau0 (subst_nf sigma0 s)) (hexp) ]
  end
  |  subst_nf ((funcomp) (subst_ne ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  subst_nf ?theta0 ?t  =>  first [ unify   (subst_nf tau0 (subst_nf sigma0 s)) (hexp)|  musigma   (subst_nf tau0 (subst_nf sigma0 s)) (hexp) ]
  end
  |  ren_ne ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  ren_ne ?theta0 ?t  =>  first [ unify   (ren_ne tau0 (ren_ne sigma0 s)) (hexp)|  musigma   (ren_ne tau0 (ren_ne sigma0 s)) (hexp) ]
  end
  |  subst_ne ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  subst_ne ?theta0 ?t  =>  first [ unify   (subst_ne tau0 (ren_ne sigma0 s)) (hexp)|  musigma   (subst_ne tau0 (ren_ne sigma0 s)) (hexp) ]
  end
  |  subst_ne ((funcomp) (ren_ne ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  ren_ne ?theta0 ?t  =>  first [ unify   (ren_ne tau0 (subst_ne sigma0 s)) (hexp)|  musigma   (ren_ne tau0 (subst_ne sigma0 s)) (hexp) ]
  end
  |  subst_ne ((funcomp) (subst_ne ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  subst_ne ?theta0 ?t  =>  first [ unify   (subst_ne tau0 (subst_ne sigma0 s)) (hexp)|  musigma   (subst_ne tau0 (subst_ne sigma0 s)) (hexp) ]
  end
  |  (funcomp) (ren_nf ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_nf ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_nf tau0) ((funcomp) (ren_nf sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (ren_nf tau0) ((funcomp) (ren_nf sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_nf ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_nf ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_nf tau0) ((funcomp) (ren_nf sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (subst_nf tau0) ((funcomp) (ren_nf sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_nf ((funcomp) (ren_ne ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_nf ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_nf tau0) ((funcomp) (subst_nf sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (ren_nf tau0) ((funcomp) (subst_nf sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_nf ((funcomp) (subst_ne ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_nf ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_nf tau0) ((funcomp) (subst_nf sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (subst_nf tau0) ((funcomp) (subst_nf sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (ren_ne ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_ne ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_ne tau0) ((funcomp) (ren_ne sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (ren_ne tau0) ((funcomp) (ren_ne sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_ne ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_ne ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_ne tau0) ((funcomp) (ren_ne sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (subst_ne tau0) ((funcomp) (ren_ne sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_ne ((funcomp) (ren_ne ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_ne ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_ne tau0) ((funcomp) (subst_ne sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (ren_ne tau0) ((funcomp) (subst_ne sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_ne ((funcomp) (subst_ne ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_ne ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_ne tau0) ((funcomp) (subst_ne sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (subst_ne tau0) ((funcomp) (subst_ne sigma0) sigmas)) (hexp) ]
  end
  |  (scons) (ren_nf ?sigma0 ?s) ((funcomp) (ren_nf ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (ren_nf ?tau0) ?thetah  =>  first [ unify   ((funcomp) (ren_nf sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (ren_nf sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (subst_nf ?sigma0 ?s) ((funcomp) (subst_nf ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (subst_nf ?tau0) ?thetah  =>  first [ unify   ((funcomp) (subst_nf sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (subst_nf sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (ren_ne ?sigma0 ?s) ((funcomp) (ren_ne ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (ren_ne ?tau0) ?thetah  =>  first [ unify   ((funcomp) (ren_ne sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (ren_ne sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (subst_ne ?sigma0 ?s) ((funcomp) (subst_ne ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (subst_ne ?tau0) ?thetah  =>  first [ unify   ((funcomp) (subst_ne sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (subst_ne sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  val ?s0  =>  match   hexp  with
  |  val ?t0  =>  musigma   (s0) (t0)
  end
  |  lam ?s0  =>  match   hexp  with
  |  lam ?t0  =>  musigma   (s0) (t0)
  end
  |  subst_nf ?sigma0 ?s  =>  match   hexp  with
  |  subst_nf ?tau0 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0)
  end
  |  ren_nf ?sigma0 ?s  =>  match   hexp  with
  |  ren_nf ?tau0 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0)
  end
  |  (funcomp) (subst_nf ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_nf ?tau0) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0)
  end
  |  (funcomp) (ren_nf ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_nf ?tau0) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0)
  end
  |  app ?s0 ?s1  =>  match   hexp  with
  |  app ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  subst_ne ?sigma0 ?s  =>  match   hexp  with
  |  subst_ne ?tau0 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0)
  end
  |  ren_ne ?sigma0 ?s  =>  match   hexp  with
  |  ren_ne ?tau0 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0)
  end
  |  (funcomp) (subst_ne ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_ne ?tau0) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0)
  end
  |  (funcomp) (ren_ne ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_ne ?tau0) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0)
  end
  end.

Ltac  heuristics gexp hexp :=
  match   gexp  with
  |  ?s  =>  unify   (gexp) (hexp)
  |  (funcomp) (subst_nf ((funcomp) var_ne ?sigma0)) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_nf ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (subst_nf ((funcomp) var_ne sigma0)) sigma = (funcomp) (ren_nf sigma0) sigma) as eq by (renamify; reflexivity); rewrite   (eq); unify   ((funcomp) (ren_nf sigma0) sigma) (hexp); clear eq
  end
  |  subst_nf ((funcomp) var_ne ?sigma0) ?s  =>  match   hexp  with
  |  ren_nf ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (subst_nf ((funcomp) var_ne sigma0) s = ren_nf sigma0 s) as eq by (renamify; reflexivity); rewrite   (eq); unify   (ren_nf sigma0 s) (hexp); clear eq
  end
  |  (funcomp) (subst_ne ((funcomp) var_ne ?sigma0)) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_ne ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (subst_ne ((funcomp) var_ne sigma0)) sigma = (funcomp) (ren_ne sigma0) sigma) as eq by (renamify; reflexivity); rewrite   (eq); unify   ((funcomp) (ren_ne sigma0) sigma) (hexp); clear eq
  end
  |  subst_ne ((funcomp) var_ne ?sigma0) ?s  =>  match   hexp  with
  |  ren_ne ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (subst_ne ((funcomp) var_ne sigma0) s = ren_ne sigma0 s) as eq by (renamify; reflexivity); rewrite   (eq); unify   (ren_ne sigma0 s) (hexp); clear eq
  end
  |  (funcomp) (ren_nf ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_nf ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_nf sigma0) sigma = (funcomp) (subst_nf ((funcomp) var_ne sigma0)) sigma) as eq by (substify; reflexivity); rewrite   (eq); unify   ((funcomp) (subst_nf ((funcomp) var_ne sigma0)) sigma) (hexp); clear eq
  end
  |  ren_nf ?sigma0 ?s  =>  match   hexp  with
  |  subst_nf ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (ren_nf sigma0 s = subst_nf ((funcomp) var_ne sigma0) s) as eq by (substify; reflexivity); rewrite   (eq); unify   (subst_nf ((funcomp) var_ne sigma0) s) (hexp); clear eq
  end
  |  (funcomp) (ren_ne ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_ne ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_ne sigma0) sigma = (funcomp) (subst_ne ((funcomp) var_ne sigma0)) sigma) as eq by (substify; reflexivity); rewrite   (eq); unify   ((funcomp) (subst_ne ((funcomp) var_ne sigma0)) sigma) (hexp); clear eq
  end
  |  ren_ne ?sigma0 ?s  =>  match   hexp  with
  |  subst_ne ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (ren_ne sigma0 s = subst_ne ((funcomp) var_ne sigma0) s) as eq by (substify; reflexivity); rewrite   (eq); unify   (subst_ne ((funcomp) var_ne sigma0) s) (hexp); clear eq
  end
  |  ?s  =>  musigma   (gexp) (hexp)
  |  subst_nf ((scons) ?sne0 ((funcomp) var_ne ?sigmane)) ?snf  =>  match   hexp  with
  |  subst_nf ((scons) ?tne0 var_ne) ?tnf  =>  unify   (subst_nf ((scons) sne0 var_ne) (ren_nf ((scons) (var_zero) ((funcomp) (shift) sigmane)) snf)) (hexp)
  end
  |  subst_nf ((scons) ?sne0 ?sigmane) ?snf  =>  match   hexp  with
  |  subst_nf ((scons) ?tne0 var_ne) ?tnf  =>  unify   (subst_nf ((scons) sne0 var_ne) (subst_nf ((scons) (var_ne (var_zero)) ((funcomp) (ren_ne (shift)) sigmane)) snf)) (hexp)
  end
  |  ?s  =>  match   hexp  with
  |  subst_nf ?sigma0 ?t  =>  unify   (subst_nf var_ne s) (hexp)
  |  ren_nf ?sigma0 ?t  =>  unify   (ren_nf (id) s) (hexp)
  |  subst_ne ?sigma0 ?t  =>  unify   (subst_ne var_ne s) (hexp)
  |  ren_ne ?sigma0 ?t  =>  unify   (ren_ne (id) s) (hexp)
  end
  |  val ?s0  =>  match   hexp  with
  |  val ?t0  =>  heuristics   (s0) (t0)
  end
  |  lam ?s0  =>  match   hexp  with
  |  lam ?t0  =>  heuristics   (s0) (t0)
  end
  |  subst_nf ?sigma0 ?s  =>  match   hexp  with
  |  subst_nf ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  ren_nf ?sigma0 ?s  =>  match   hexp  with
  |  ren_nf ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (subst_nf ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_nf ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (ren_nf ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_nf ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  |  app ?s0 ?s1  =>  match   hexp  with
  |  app ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  subst_ne ?sigma0 ?s  =>  match   hexp  with
  |  subst_ne ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  ren_ne ?sigma0 ?s  =>  match   hexp  with
  |  ren_ne ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (subst_ne ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_ne ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (ren_ne ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_ne ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
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
