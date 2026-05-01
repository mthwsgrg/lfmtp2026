Require Export fintype.



Section ty.
Inductive ty (nty : nat) : Type :=
  | var_ty : (fin) (nty) -> ty (nty)
  | arr : ty  (nty) -> ty  (nty) -> ty (nty)
  | all : ty  ((S) nty) -> ty (nty).

Lemma congr_arr { mty : nat } { s0 : ty  (mty) } { s1 : ty  (mty) } { t0 : ty  (mty) } { t1 : ty  (mty) } (H1 : s0 = t0) (H2 : s1 = t1) : arr (mty) s0 s1 = arr (mty) t0 t1 .
Proof. congruence. Qed.

Lemma congr_all { mty : nat } { s0 : ty  ((S) mty) } { t0 : ty  ((S) mty) } (H1 : s0 = t0) : all (mty) s0 = all (mty) t0 .
Proof. congruence. Qed.

Definition upRen_ty_ty { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Fixpoint ren_ty { mty : nat } { nty : nat } (xity : (fin) (mty) -> (fin) (nty)) (s : ty (mty)) : ty (nty) :=
    match s return ty (nty) with
    | var_ty (_) s => (var_ty (nty)) (xity s)
    | arr (_) s0 s1 => arr (nty) ((ren_ty xity) s0) ((ren_ty xity) s1)
    | all (_) s0 => all (nty) ((ren_ty (upRen_ty_ty xity)) s0)
    end.

Definition up_ty_ty { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) : (fin) ((S) (m)) -> ty ((S) nty) :=
  (scons) ((var_ty ((S) nty)) (var_zero)) ((funcomp) (ren_ty (shift)) sigma).

Fixpoint subst_ty { mty : nat } { nty : nat } (sigmaty : (fin) (mty) -> ty (nty)) (s : ty (mty)) : ty (nty) :=
    match s return ty (nty) with
    | var_ty (_) s => sigmaty s
    | arr (_) s0 s1 => arr (nty) ((subst_ty sigmaty) s0) ((subst_ty sigmaty) s1)
    | all (_) s0 => all (nty) ((subst_ty (up_ty_ty sigmaty)) s0)
    end.

Definition upId_ty_ty { mty : nat } (sigma : (fin) (mty) -> ty (mty)) (Eq : forall x, sigma x = (var_ty (mty)) x) : forall x, (up_ty_ty sigma) x = (var_ty ((S) mty)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_ty (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint idSubst_ty { mty : nat } (sigmaty : (fin) (mty) -> ty (mty)) (Eqty : forall x, sigmaty x = (var_ty (mty)) x) (s : ty (mty)) : subst_ty sigmaty s = s :=
    match s return subst_ty sigmaty s = s with
    | var_ty (_) s => Eqty s
    | arr (_) s0 s1 => congr_arr ((idSubst_ty sigmaty Eqty) s0) ((idSubst_ty sigmaty Eqty) s1)
    | all (_) s0 => congr_all ((idSubst_ty (up_ty_ty sigmaty) (upId_ty_ty (_) Eqty)) s0)
    end.

Definition upExtRen_ty_ty { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_ty_ty xi) x = (upRen_ty_ty zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint extRen_ty { mty : nat } { nty : nat } (xity : (fin) (mty) -> (fin) (nty)) (zetaty : (fin) (mty) -> (fin) (nty)) (Eqty : forall x, xity x = zetaty x) (s : ty (mty)) : ren_ty xity s = ren_ty zetaty s :=
    match s return ren_ty xity s = ren_ty zetaty s with
    | var_ty (_) s => (ap) (var_ty (nty)) (Eqty s)
    | arr (_) s0 s1 => congr_arr ((extRen_ty xity zetaty Eqty) s0) ((extRen_ty xity zetaty Eqty) s1)
    | all (_) s0 => congr_all ((extRen_ty (upRen_ty_ty xity) (upRen_ty_ty zetaty) (upExtRen_ty_ty (_) (_) Eqty)) s0)
    end.

Definition upExt_ty_ty { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) (tau : (fin) (m) -> ty (nty)) (Eq : forall x, sigma x = tau x) : forall x, (up_ty_ty sigma) x = (up_ty_ty tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_ty (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint ext_ty { mty : nat } { nty : nat } (sigmaty : (fin) (mty) -> ty (nty)) (tauty : (fin) (mty) -> ty (nty)) (Eqty : forall x, sigmaty x = tauty x) (s : ty (mty)) : subst_ty sigmaty s = subst_ty tauty s :=
    match s return subst_ty sigmaty s = subst_ty tauty s with
    | var_ty (_) s => Eqty s
    | arr (_) s0 s1 => congr_arr ((ext_ty sigmaty tauty Eqty) s0) ((ext_ty sigmaty tauty Eqty) s1)
    | all (_) s0 => congr_all ((ext_ty (up_ty_ty sigmaty) (up_ty_ty tauty) (upExt_ty_ty (_) (_) Eqty)) s0)
    end.

Definition up_ren_ren_ty_ty { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_ty_ty tau) (upRen_ty_ty xi)) x = (upRen_ty_ty theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_ty { kty : nat } { lty : nat } { mty : nat } (xity : (fin) (mty) -> (fin) (kty)) (zetaty : (fin) (kty) -> (fin) (lty)) (rhoty : (fin) (mty) -> (fin) (lty)) (Eqty : forall x, ((funcomp) zetaty xity) x = rhoty x) (s : ty (mty)) : ren_ty zetaty (ren_ty xity s) = ren_ty rhoty s :=
    match s return ren_ty zetaty (ren_ty xity s) = ren_ty rhoty s with
    | var_ty (_) s => (ap) (var_ty (lty)) (Eqty s)
    | arr (_) s0 s1 => congr_arr ((compRenRen_ty xity zetaty rhoty Eqty) s0) ((compRenRen_ty xity zetaty rhoty Eqty) s1)
    | all (_) s0 => congr_all ((compRenRen_ty (upRen_ty_ty xity) (upRen_ty_ty zetaty) (upRen_ty_ty rhoty) (up_ren_ren (_) (_) (_) Eqty)) s0)
    end.

Definition up_ren_subst_ty_ty { k : nat } { l : nat } { mty : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_ty_ty tau) (upRen_ty_ty xi)) x = (up_ty_ty theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_ty (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint compRenSubst_ty { kty : nat } { lty : nat } { mty : nat } (xity : (fin) (mty) -> (fin) (kty)) (tauty : (fin) (kty) -> ty (lty)) (thetaty : (fin) (mty) -> ty (lty)) (Eqty : forall x, ((funcomp) tauty xity) x = thetaty x) (s : ty (mty)) : subst_ty tauty (ren_ty xity s) = subst_ty thetaty s :=
    match s return subst_ty tauty (ren_ty xity s) = subst_ty thetaty s with
    | var_ty (_) s => Eqty s
    | arr (_) s0 s1 => congr_arr ((compRenSubst_ty xity tauty thetaty Eqty) s0) ((compRenSubst_ty xity tauty thetaty Eqty) s1)
    | all (_) s0 => congr_all ((compRenSubst_ty (upRen_ty_ty xity) (up_ty_ty tauty) (up_ty_ty thetaty) (up_ren_subst_ty_ty (_) (_) (_) Eqty)) s0)
    end.

Definition up_subst_ren_ty_ty { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (zetaty : (fin) (lty) -> (fin) (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (ren_ty zetaty) sigma) x = theta x) : forall x, ((funcomp) (ren_ty (upRen_ty_ty zetaty)) (up_ty_ty sigma)) x = (up_ty_ty theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_ty (shift) (upRen_ty_ty zetaty) ((funcomp) (shift) zetaty) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_ty zetaty (shift) ((funcomp) (shift) zetaty) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_ty (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstRen_ty { kty : nat } { lty : nat } { mty : nat } (sigmaty : (fin) (mty) -> ty (kty)) (zetaty : (fin) (kty) -> (fin) (lty)) (thetaty : (fin) (mty) -> ty (lty)) (Eqty : forall x, ((funcomp) (ren_ty zetaty) sigmaty) x = thetaty x) (s : ty (mty)) : ren_ty zetaty (subst_ty sigmaty s) = subst_ty thetaty s :=
    match s return ren_ty zetaty (subst_ty sigmaty s) = subst_ty thetaty s with
    | var_ty (_) s => Eqty s
    | arr (_) s0 s1 => congr_arr ((compSubstRen_ty sigmaty zetaty thetaty Eqty) s0) ((compSubstRen_ty sigmaty zetaty thetaty Eqty) s1)
    | all (_) s0 => congr_all ((compSubstRen_ty (up_ty_ty sigmaty) (upRen_ty_ty zetaty) (up_ty_ty thetaty) (up_subst_ren_ty_ty (_) (_) (_) Eqty)) s0)
    end.

Definition up_subst_subst_ty_ty { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (tauty : (fin) (lty) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (subst_ty tauty) sigma) x = theta x) : forall x, ((funcomp) (subst_ty (up_ty_ty tauty)) (up_ty_ty sigma)) x = (up_ty_ty theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_ty (shift) (up_ty_ty tauty) ((funcomp) (up_ty_ty tauty) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_ty tauty (shift) ((funcomp) (ren_ty (shift)) tauty) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_ty (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstSubst_ty { kty : nat } { lty : nat } { mty : nat } (sigmaty : (fin) (mty) -> ty (kty)) (tauty : (fin) (kty) -> ty (lty)) (thetaty : (fin) (mty) -> ty (lty)) (Eqty : forall x, ((funcomp) (subst_ty tauty) sigmaty) x = thetaty x) (s : ty (mty)) : subst_ty tauty (subst_ty sigmaty s) = subst_ty thetaty s :=
    match s return subst_ty tauty (subst_ty sigmaty s) = subst_ty thetaty s with
    | var_ty (_) s => Eqty s
    | arr (_) s0 s1 => congr_arr ((compSubstSubst_ty sigmaty tauty thetaty Eqty) s0) ((compSubstSubst_ty sigmaty tauty thetaty Eqty) s1)
    | all (_) s0 => congr_all ((compSubstSubst_ty (up_ty_ty sigmaty) (up_ty_ty tauty) (up_ty_ty thetaty) (up_subst_subst_ty_ty (_) (_) (_) Eqty)) s0)
    end.

Definition rinstInst_up_ty_ty { m : nat } { nty : nat } (xi : (fin) (m) -> (fin) (nty)) (sigma : (fin) (m) -> ty (nty)) (Eq : forall x, ((funcomp) (var_ty (nty)) xi) x = sigma x) : forall x, ((funcomp) (var_ty ((S) nty)) (upRen_ty_ty xi)) x = (up_ty_ty sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_ty (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint rinst_inst_ty { mty : nat } { nty : nat } (xity : (fin) (mty) -> (fin) (nty)) (sigmaty : (fin) (mty) -> ty (nty)) (Eqty : forall x, ((funcomp) (var_ty (nty)) xity) x = sigmaty x) (s : ty (mty)) : ren_ty xity s = subst_ty sigmaty s :=
    match s return ren_ty xity s = subst_ty sigmaty s with
    | var_ty (_) s => Eqty s
    | arr (_) s0 s1 => congr_arr ((rinst_inst_ty xity sigmaty Eqty) s0) ((rinst_inst_ty xity sigmaty Eqty) s1)
    | all (_) s0 => congr_all ((rinst_inst_ty (upRen_ty_ty xity) (up_ty_ty sigmaty) (rinstInst_up_ty_ty (_) (_) Eqty)) s0)
    end.

Lemma rinstInst_ty { mty : nat } { nty : nat } (xity : (fin) (mty) -> (fin) (nty)) : ren_ty xity = subst_ty ((funcomp) (var_ty (nty)) xity) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_ty xity (_) (fun n => eq_refl) x)). Qed.

Lemma instId_ty { mty : nat } : subst_ty (var_ty (mty)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_ty (var_ty (mty)) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_ty { mty : nat } : @ren_ty (mty) (mty) (id) = id .
Proof. exact ((eq_trans) (rinstInst_ty ((id) (_))) instId_ty). Qed.

Lemma varL_ty { mty : nat } { nty : nat } (sigmaty : (fin) (mty) -> ty (nty)) : (funcomp) (subst_ty sigmaty) (var_ty (mty)) = sigmaty .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_ty { mty : nat } { nty : nat } (xity : (fin) (mty) -> (fin) (nty)) : (funcomp) (ren_ty xity) (var_ty (mty)) = (funcomp) (var_ty (nty)) xity .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_ty { kty : nat } { lty : nat } { mty : nat } (sigmaty : (fin) (mty) -> ty (kty)) (tauty : (fin) (kty) -> ty (lty)) (s : ty (mty)) : subst_ty tauty (subst_ty sigmaty s) = subst_ty ((funcomp) (subst_ty tauty) sigmaty) s .
Proof. exact (compSubstSubst_ty sigmaty tauty (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_ty { kty : nat } { lty : nat } { mty : nat } (sigmaty : (fin) (mty) -> ty (kty)) (tauty : (fin) (kty) -> ty (lty)) : (funcomp) (subst_ty tauty) (subst_ty sigmaty) = subst_ty ((funcomp) (subst_ty tauty) sigmaty) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_ty sigmaty tauty n)). Qed.

Lemma compRen_ty { kty : nat } { lty : nat } { mty : nat } (sigmaty : (fin) (mty) -> ty (kty)) (zetaty : (fin) (kty) -> (fin) (lty)) (s : ty (mty)) : ren_ty zetaty (subst_ty sigmaty s) = subst_ty ((funcomp) (ren_ty zetaty) sigmaty) s .
Proof. exact (compSubstRen_ty sigmaty zetaty (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_ty { kty : nat } { lty : nat } { mty : nat } (sigmaty : (fin) (mty) -> ty (kty)) (zetaty : (fin) (kty) -> (fin) (lty)) : (funcomp) (ren_ty zetaty) (subst_ty sigmaty) = subst_ty ((funcomp) (ren_ty zetaty) sigmaty) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_ty sigmaty zetaty n)). Qed.

Lemma renComp_ty { kty : nat } { lty : nat } { mty : nat } (xity : (fin) (mty) -> (fin) (kty)) (tauty : (fin) (kty) -> ty (lty)) (s : ty (mty)) : subst_ty tauty (ren_ty xity s) = subst_ty ((funcomp) tauty xity) s .
Proof. exact (compRenSubst_ty xity tauty (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_ty { kty : nat } { lty : nat } { mty : nat } (xity : (fin) (mty) -> (fin) (kty)) (tauty : (fin) (kty) -> ty (lty)) : (funcomp) (subst_ty tauty) (ren_ty xity) = subst_ty ((funcomp) tauty xity) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_ty xity tauty n)). Qed.

Lemma renRen_ty { kty : nat } { lty : nat } { mty : nat } (xity : (fin) (mty) -> (fin) (kty)) (zetaty : (fin) (kty) -> (fin) (lty)) (s : ty (mty)) : ren_ty zetaty (ren_ty xity s) = ren_ty ((funcomp) zetaty xity) s .
Proof. exact (compRenRen_ty xity zetaty (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_ty { kty : nat } { lty : nat } { mty : nat } (xity : (fin) (mty) -> (fin) (kty)) (zetaty : (fin) (kty) -> (fin) (lty)) : (funcomp) (ren_ty zetaty) (ren_ty xity) = ren_ty ((funcomp) zetaty xity) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_ty xity zetaty n)). Qed.

End ty.

Section tmvl.
Inductive tm (nty ntm nvl : nat) : Type :=
  | var_tm : (fin) (ntm) -> tm (nty) (ntm) (nvl)
  | app : tm  (nty) (ntm) (nvl) -> tm  (nty) (ntm) (nvl) -> tm (nty) (ntm) (nvl)
  | tapp : tm  (nty) (ntm) (nvl) -> ty  (nty) -> tm (nty) (ntm) (nvl)
  | vt : vl  (nty) (ntm) (nvl) -> tm (nty) (ntm) (nvl)
 with vl (nty ntm nvl : nat) : Type :=
  | var_vl : (fin) (nvl) -> vl (nty) (ntm) (nvl)
  | lam : ty  (nty) -> tm  (nty) ((S) ntm) ((S) nvl) -> vl (nty) (ntm) (nvl)
  | tlam : tm  ((S) nty) (ntm) (nvl) -> vl (nty) (ntm) (nvl).

Lemma congr_app { mty mtm mvl : nat } { s0 : tm  (mty) (mtm) (mvl) } { s1 : tm  (mty) (mtm) (mvl) } { t0 : tm  (mty) (mtm) (mvl) } { t1 : tm  (mty) (mtm) (mvl) } (H1 : s0 = t0) (H2 : s1 = t1) : app (mty) (mtm) (mvl) s0 s1 = app (mty) (mtm) (mvl) t0 t1 .
Proof. congruence. Qed.

Lemma congr_tapp { mty mtm mvl : nat } { s0 : tm  (mty) (mtm) (mvl) } { s1 : ty  (mty) } { t0 : tm  (mty) (mtm) (mvl) } { t1 : ty  (mty) } (H1 : s0 = t0) (H2 : s1 = t1) : tapp (mty) (mtm) (mvl) s0 s1 = tapp (mty) (mtm) (mvl) t0 t1 .
Proof. congruence. Qed.

Lemma congr_vt { mty mtm mvl : nat } { s0 : vl  (mty) (mtm) (mvl) } { t0 : vl  (mty) (mtm) (mvl) } (H1 : s0 = t0) : vt (mty) (mtm) (mvl) s0 = vt (mty) (mtm) (mvl) t0 .
Proof. congruence. Qed.

Lemma congr_lam { mty mtm mvl : nat } { s0 : ty  (mty) } { s1 : tm  (mty) ((S) mtm) ((S) mvl) } { t0 : ty  (mty) } { t1 : tm  (mty) ((S) mtm) ((S) mvl) } (H1 : s0 = t0) (H2 : s1 = t1) : lam (mty) (mtm) (mvl) s0 s1 = lam (mty) (mtm) (mvl) t0 t1 .
Proof. congruence. Qed.

Lemma congr_tlam { mty mtm mvl : nat } { s0 : tm  ((S) mty) (mtm) (mvl) } { t0 : tm  ((S) mty) (mtm) (mvl) } (H1 : s0 = t0) : tlam (mty) (mtm) (mvl) s0 = tlam (mty) (mtm) (mvl) t0 .
Proof. congruence. Qed.

Definition upRen_ty_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (m) -> (fin) (n) :=
  xi.

Definition upRen_ty_vl { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (m) -> (fin) (n) :=
  xi.

Definition upRen_tm_ty { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (m) -> (fin) (n) :=
  xi.

Definition upRen_tm_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Definition upRen_tm_vl { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (m) -> (fin) (n) :=
  xi.

Definition upRen_vl_ty { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (m) -> (fin) (n) :=
  xi.

Definition upRen_vl_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (m) -> (fin) (n) :=
  xi.

Definition upRen_vl_vl { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Fixpoint ren_tm { mty mtm mvl : nat } { nty ntm nvl : nat } (xity : (fin) (mty) -> (fin) (nty)) (xitm : (fin) (mtm) -> (fin) (ntm)) (xivl : (fin) (mvl) -> (fin) (nvl)) (s : tm (mty) (mtm) (mvl)) : tm (nty) (ntm) (nvl) :=
    match s return tm (nty) (ntm) (nvl) with
    | var_tm (_) (_) (_) s => (var_tm (nty) (ntm) (nvl)) (xitm s)
    | app (_) (_) (_) s0 s1 => app (nty) (ntm) (nvl) ((ren_tm xity xitm xivl) s0) ((ren_tm xity xitm xivl) s1)
    | tapp (_) (_) (_) s0 s1 => tapp (nty) (ntm) (nvl) ((ren_tm xity xitm xivl) s0) ((ren_ty xity) s1)
    | vt (_) (_) (_) s0 => vt (nty) (ntm) (nvl) ((ren_vl xity xitm xivl) s0)
    end
 with ren_vl { mty mtm mvl : nat } { nty ntm nvl : nat } (xity : (fin) (mty) -> (fin) (nty)) (xitm : (fin) (mtm) -> (fin) (ntm)) (xivl : (fin) (mvl) -> (fin) (nvl)) (s : vl (mty) (mtm) (mvl)) : vl (nty) (ntm) (nvl) :=
    match s return vl (nty) (ntm) (nvl) with
    | var_vl (_) (_) (_) s => (var_vl (nty) (ntm) (nvl)) (xivl s)
    | lam (_) (_) (_) s0 s1 => lam (nty) (ntm) (nvl) ((ren_ty xity) s0) ((ren_tm (upRen_tm_ty (upRen_vl_ty xity)) (upRen_tm_tm (upRen_vl_tm xitm)) (upRen_tm_vl (upRen_vl_vl xivl))) s1)
    | tlam (_) (_) (_) s0 => tlam (nty) (ntm) (nvl) ((ren_tm (upRen_ty_ty xity) (upRen_ty_tm xitm) (upRen_ty_vl xivl)) s0)
    end.

Definition up_ty_tm { m : nat } { nty ntm nvl : nat } (sigma : (fin) (m) -> tm (nty) (ntm) (nvl)) : (fin) (m) -> tm ((S) nty) (ntm) (nvl) :=
  (funcomp) (ren_tm (shift) (id) (id)) sigma.

Definition up_ty_vl { m : nat } { nty ntm nvl : nat } (sigma : (fin) (m) -> vl (nty) (ntm) (nvl)) : (fin) (m) -> vl ((S) nty) (ntm) (nvl) :=
  (funcomp) (ren_vl (shift) (id) (id)) sigma.

Definition up_tm_ty { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) : (fin) (m) -> ty (nty) :=
  (funcomp) (ren_ty (id)) sigma.

Definition up_tm_tm { m : nat } { nty ntm nvl : nat } (sigma : (fin) (m) -> tm (nty) (ntm) (nvl)) : (fin) ((S) (m)) -> tm (nty) ((S) ntm) (nvl) :=
  (scons) ((var_tm (nty) ((S) ntm) (nvl)) (var_zero)) ((funcomp) (ren_tm (id) (shift) (id)) sigma).

Definition up_tm_vl { m : nat } { nty ntm nvl : nat } (sigma : (fin) (m) -> vl (nty) (ntm) (nvl)) : (fin) (m) -> vl (nty) ((S) ntm) (nvl) :=
  (funcomp) (ren_vl (id) (shift) (id)) sigma.

Definition up_vl_ty { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) : (fin) (m) -> ty (nty) :=
  (funcomp) (ren_ty (id)) sigma.

Definition up_vl_tm { m : nat } { nty ntm nvl : nat } (sigma : (fin) (m) -> tm (nty) (ntm) (nvl)) : (fin) (m) -> tm (nty) (ntm) ((S) nvl) :=
  (funcomp) (ren_tm (id) (id) (shift)) sigma.

Definition up_vl_vl { m : nat } { nty ntm nvl : nat } (sigma : (fin) (m) -> vl (nty) (ntm) (nvl)) : (fin) ((S) (m)) -> vl (nty) (ntm) ((S) nvl) :=
  (scons) ((var_vl (nty) (ntm) ((S) nvl)) (var_zero)) ((funcomp) (ren_vl (id) (id) (shift)) sigma).

Fixpoint subst_tm { mty mtm mvl : nat } { nty ntm nvl : nat } (sigmaty : (fin) (mty) -> ty (nty)) (sigmatm : (fin) (mtm) -> tm (nty) (ntm) (nvl)) (sigmavl : (fin) (mvl) -> vl (nty) (ntm) (nvl)) (s : tm (mty) (mtm) (mvl)) : tm (nty) (ntm) (nvl) :=
    match s return tm (nty) (ntm) (nvl) with
    | var_tm (_) (_) (_) s => sigmatm s
    | app (_) (_) (_) s0 s1 => app (nty) (ntm) (nvl) ((subst_tm sigmaty sigmatm sigmavl) s0) ((subst_tm sigmaty sigmatm sigmavl) s1)
    | tapp (_) (_) (_) s0 s1 => tapp (nty) (ntm) (nvl) ((subst_tm sigmaty sigmatm sigmavl) s0) ((subst_ty sigmaty) s1)
    | vt (_) (_) (_) s0 => vt (nty) (ntm) (nvl) ((subst_vl sigmaty sigmatm sigmavl) s0)
    end
 with subst_vl { mty mtm mvl : nat } { nty ntm nvl : nat } (sigmaty : (fin) (mty) -> ty (nty)) (sigmatm : (fin) (mtm) -> tm (nty) (ntm) (nvl)) (sigmavl : (fin) (mvl) -> vl (nty) (ntm) (nvl)) (s : vl (mty) (mtm) (mvl)) : vl (nty) (ntm) (nvl) :=
    match s return vl (nty) (ntm) (nvl) with
    | var_vl (_) (_) (_) s => sigmavl s
    | lam (_) (_) (_) s0 s1 => lam (nty) (ntm) (nvl) ((subst_ty sigmaty) s0) ((subst_tm (up_tm_ty (up_vl_ty sigmaty)) (up_tm_tm (up_vl_tm sigmatm)) (up_tm_vl (up_vl_vl sigmavl))) s1)
    | tlam (_) (_) (_) s0 => tlam (nty) (ntm) (nvl) ((subst_tm (up_ty_ty sigmaty) (up_ty_tm sigmatm) (up_ty_vl sigmavl)) s0)
    end.

Definition upId_ty_tm { mty mtm mvl : nat } (sigma : (fin) (mtm) -> tm (mty) (mtm) (mvl)) (Eq : forall x, sigma x = (var_tm (mty) (mtm) (mvl)) x) : forall x, (up_ty_tm sigma) x = (var_tm ((S) mty) (mtm) (mvl)) x :=
  fun n => (ap) (ren_tm (shift) (id) (id)) (Eq n).

Definition upId_ty_vl { mty mtm mvl : nat } (sigma : (fin) (mvl) -> vl (mty) (mtm) (mvl)) (Eq : forall x, sigma x = (var_vl (mty) (mtm) (mvl)) x) : forall x, (up_ty_vl sigma) x = (var_vl ((S) mty) (mtm) (mvl)) x :=
  fun n => (ap) (ren_vl (shift) (id) (id)) (Eq n).

Definition upId_tm_ty { mty : nat } (sigma : (fin) (mty) -> ty (mty)) (Eq : forall x, sigma x = (var_ty (mty)) x) : forall x, (up_tm_ty sigma) x = (var_ty (mty)) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition upId_tm_tm { mty mtm mvl : nat } (sigma : (fin) (mtm) -> tm (mty) (mtm) (mvl)) (Eq : forall x, sigma x = (var_tm (mty) (mtm) (mvl)) x) : forall x, (up_tm_tm sigma) x = (var_tm (mty) ((S) mtm) (mvl)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (id) (shift) (id)) (Eq fin_n)
  | None  => eq_refl
  end.

Definition upId_tm_vl { mty mtm mvl : nat } (sigma : (fin) (mvl) -> vl (mty) (mtm) (mvl)) (Eq : forall x, sigma x = (var_vl (mty) (mtm) (mvl)) x) : forall x, (up_tm_vl sigma) x = (var_vl (mty) ((S) mtm) (mvl)) x :=
  fun n => (ap) (ren_vl (id) (shift) (id)) (Eq n).

Definition upId_vl_ty { mty : nat } (sigma : (fin) (mty) -> ty (mty)) (Eq : forall x, sigma x = (var_ty (mty)) x) : forall x, (up_vl_ty sigma) x = (var_ty (mty)) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition upId_vl_tm { mty mtm mvl : nat } (sigma : (fin) (mtm) -> tm (mty) (mtm) (mvl)) (Eq : forall x, sigma x = (var_tm (mty) (mtm) (mvl)) x) : forall x, (up_vl_tm sigma) x = (var_tm (mty) (mtm) ((S) mvl)) x :=
  fun n => (ap) (ren_tm (id) (id) (shift)) (Eq n).

Definition upId_vl_vl { mty mtm mvl : nat } (sigma : (fin) (mvl) -> vl (mty) (mtm) (mvl)) (Eq : forall x, sigma x = (var_vl (mty) (mtm) (mvl)) x) : forall x, (up_vl_vl sigma) x = (var_vl (mty) (mtm) ((S) mvl)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_vl (id) (id) (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint idSubst_tm { mty mtm mvl : nat } (sigmaty : (fin) (mty) -> ty (mty)) (sigmatm : (fin) (mtm) -> tm (mty) (mtm) (mvl)) (sigmavl : (fin) (mvl) -> vl (mty) (mtm) (mvl)) (Eqty : forall x, sigmaty x = (var_ty (mty)) x) (Eqtm : forall x, sigmatm x = (var_tm (mty) (mtm) (mvl)) x) (Eqvl : forall x, sigmavl x = (var_vl (mty) (mtm) (mvl)) x) (s : tm (mty) (mtm) (mvl)) : subst_tm sigmaty sigmatm sigmavl s = s :=
    match s return subst_tm sigmaty sigmatm sigmavl s = s with
    | var_tm (_) (_) (_) s => Eqtm s
    | app (_) (_) (_) s0 s1 => congr_app ((idSubst_tm sigmaty sigmatm sigmavl Eqty Eqtm Eqvl) s0) ((idSubst_tm sigmaty sigmatm sigmavl Eqty Eqtm Eqvl) s1)
    | tapp (_) (_) (_) s0 s1 => congr_tapp ((idSubst_tm sigmaty sigmatm sigmavl Eqty Eqtm Eqvl) s0) ((idSubst_ty sigmaty Eqty) s1)
    | vt (_) (_) (_) s0 => congr_vt ((idSubst_vl sigmaty sigmatm sigmavl Eqty Eqtm Eqvl) s0)
    end
 with idSubst_vl { mty mtm mvl : nat } (sigmaty : (fin) (mty) -> ty (mty)) (sigmatm : (fin) (mtm) -> tm (mty) (mtm) (mvl)) (sigmavl : (fin) (mvl) -> vl (mty) (mtm) (mvl)) (Eqty : forall x, sigmaty x = (var_ty (mty)) x) (Eqtm : forall x, sigmatm x = (var_tm (mty) (mtm) (mvl)) x) (Eqvl : forall x, sigmavl x = (var_vl (mty) (mtm) (mvl)) x) (s : vl (mty) (mtm) (mvl)) : subst_vl sigmaty sigmatm sigmavl s = s :=
    match s return subst_vl sigmaty sigmatm sigmavl s = s with
    | var_vl (_) (_) (_) s => Eqvl s
    | lam (_) (_) (_) s0 s1 => congr_lam ((idSubst_ty sigmaty Eqty) s0) ((idSubst_tm (up_tm_ty (up_vl_ty sigmaty)) (up_tm_tm (up_vl_tm sigmatm)) (up_tm_vl (up_vl_vl sigmavl)) (upId_tm_ty (_) (upId_vl_ty (_) Eqty)) (upId_tm_tm (_) (upId_vl_tm (_) Eqtm)) (upId_tm_vl (_) (upId_vl_vl (_) Eqvl))) s1)
    | tlam (_) (_) (_) s0 => congr_tlam ((idSubst_tm (up_ty_ty sigmaty) (up_ty_tm sigmatm) (up_ty_vl sigmavl) (upId_ty_ty (_) Eqty) (upId_ty_tm (_) Eqtm) (upId_ty_vl (_) Eqvl)) s0)
    end.

Definition upExtRen_ty_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_ty_tm xi) x = (upRen_ty_tm zeta) x :=
  fun n => Eq n.

Definition upExtRen_ty_vl { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_ty_vl xi) x = (upRen_ty_vl zeta) x :=
  fun n => Eq n.

Definition upExtRen_tm_ty { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_tm_ty xi) x = (upRen_tm_ty zeta) x :=
  fun n => Eq n.

Definition upExtRen_tm_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_tm_tm xi) x = (upRen_tm_tm zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Definition upExtRen_tm_vl { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_tm_vl xi) x = (upRen_tm_vl zeta) x :=
  fun n => Eq n.

Definition upExtRen_vl_ty { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_vl_ty xi) x = (upRen_vl_ty zeta) x :=
  fun n => Eq n.

Definition upExtRen_vl_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_vl_tm xi) x = (upRen_vl_tm zeta) x :=
  fun n => Eq n.

Definition upExtRen_vl_vl { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_vl_vl xi) x = (upRen_vl_vl zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint extRen_tm { mty mtm mvl : nat } { nty ntm nvl : nat } (xity : (fin) (mty) -> (fin) (nty)) (xitm : (fin) (mtm) -> (fin) (ntm)) (xivl : (fin) (mvl) -> (fin) (nvl)) (zetaty : (fin) (mty) -> (fin) (nty)) (zetatm : (fin) (mtm) -> (fin) (ntm)) (zetavl : (fin) (mvl) -> (fin) (nvl)) (Eqty : forall x, xity x = zetaty x) (Eqtm : forall x, xitm x = zetatm x) (Eqvl : forall x, xivl x = zetavl x) (s : tm (mty) (mtm) (mvl)) : ren_tm xity xitm xivl s = ren_tm zetaty zetatm zetavl s :=
    match s return ren_tm xity xitm xivl s = ren_tm zetaty zetatm zetavl s with
    | var_tm (_) (_) (_) s => (ap) (var_tm (nty) (ntm) (nvl)) (Eqtm s)
    | app (_) (_) (_) s0 s1 => congr_app ((extRen_tm xity xitm xivl zetaty zetatm zetavl Eqty Eqtm Eqvl) s0) ((extRen_tm xity xitm xivl zetaty zetatm zetavl Eqty Eqtm Eqvl) s1)
    | tapp (_) (_) (_) s0 s1 => congr_tapp ((extRen_tm xity xitm xivl zetaty zetatm zetavl Eqty Eqtm Eqvl) s0) ((extRen_ty xity zetaty Eqty) s1)
    | vt (_) (_) (_) s0 => congr_vt ((extRen_vl xity xitm xivl zetaty zetatm zetavl Eqty Eqtm Eqvl) s0)
    end
 with extRen_vl { mty mtm mvl : nat } { nty ntm nvl : nat } (xity : (fin) (mty) -> (fin) (nty)) (xitm : (fin) (mtm) -> (fin) (ntm)) (xivl : (fin) (mvl) -> (fin) (nvl)) (zetaty : (fin) (mty) -> (fin) (nty)) (zetatm : (fin) (mtm) -> (fin) (ntm)) (zetavl : (fin) (mvl) -> (fin) (nvl)) (Eqty : forall x, xity x = zetaty x) (Eqtm : forall x, xitm x = zetatm x) (Eqvl : forall x, xivl x = zetavl x) (s : vl (mty) (mtm) (mvl)) : ren_vl xity xitm xivl s = ren_vl zetaty zetatm zetavl s :=
    match s return ren_vl xity xitm xivl s = ren_vl zetaty zetatm zetavl s with
    | var_vl (_) (_) (_) s => (ap) (var_vl (nty) (ntm) (nvl)) (Eqvl s)
    | lam (_) (_) (_) s0 s1 => congr_lam ((extRen_ty xity zetaty Eqty) s0) ((extRen_tm (upRen_tm_ty (upRen_vl_ty xity)) (upRen_tm_tm (upRen_vl_tm xitm)) (upRen_tm_vl (upRen_vl_vl xivl)) (upRen_tm_ty (upRen_vl_ty zetaty)) (upRen_tm_tm (upRen_vl_tm zetatm)) (upRen_tm_vl (upRen_vl_vl zetavl)) (upExtRen_tm_ty (_) (_) (upExtRen_vl_ty (_) (_) Eqty)) (upExtRen_tm_tm (_) (_) (upExtRen_vl_tm (_) (_) Eqtm)) (upExtRen_tm_vl (_) (_) (upExtRen_vl_vl (_) (_) Eqvl))) s1)
    | tlam (_) (_) (_) s0 => congr_tlam ((extRen_tm (upRen_ty_ty xity) (upRen_ty_tm xitm) (upRen_ty_vl xivl) (upRen_ty_ty zetaty) (upRen_ty_tm zetatm) (upRen_ty_vl zetavl) (upExtRen_ty_ty (_) (_) Eqty) (upExtRen_ty_tm (_) (_) Eqtm) (upExtRen_ty_vl (_) (_) Eqvl)) s0)
    end.

Definition upExt_ty_tm { m : nat } { nty ntm nvl : nat } (sigma : (fin) (m) -> tm (nty) (ntm) (nvl)) (tau : (fin) (m) -> tm (nty) (ntm) (nvl)) (Eq : forall x, sigma x = tau x) : forall x, (up_ty_tm sigma) x = (up_ty_tm tau) x :=
  fun n => (ap) (ren_tm (shift) (id) (id)) (Eq n).

Definition upExt_ty_vl { m : nat } { nty ntm nvl : nat } (sigma : (fin) (m) -> vl (nty) (ntm) (nvl)) (tau : (fin) (m) -> vl (nty) (ntm) (nvl)) (Eq : forall x, sigma x = tau x) : forall x, (up_ty_vl sigma) x = (up_ty_vl tau) x :=
  fun n => (ap) (ren_vl (shift) (id) (id)) (Eq n).

Definition upExt_tm_ty { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) (tau : (fin) (m) -> ty (nty)) (Eq : forall x, sigma x = tau x) : forall x, (up_tm_ty sigma) x = (up_tm_ty tau) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition upExt_tm_tm { m : nat } { nty ntm nvl : nat } (sigma : (fin) (m) -> tm (nty) (ntm) (nvl)) (tau : (fin) (m) -> tm (nty) (ntm) (nvl)) (Eq : forall x, sigma x = tau x) : forall x, (up_tm_tm sigma) x = (up_tm_tm tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (id) (shift) (id)) (Eq fin_n)
  | None  => eq_refl
  end.

Definition upExt_tm_vl { m : nat } { nty ntm nvl : nat } (sigma : (fin) (m) -> vl (nty) (ntm) (nvl)) (tau : (fin) (m) -> vl (nty) (ntm) (nvl)) (Eq : forall x, sigma x = tau x) : forall x, (up_tm_vl sigma) x = (up_tm_vl tau) x :=
  fun n => (ap) (ren_vl (id) (shift) (id)) (Eq n).

Definition upExt_vl_ty { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) (tau : (fin) (m) -> ty (nty)) (Eq : forall x, sigma x = tau x) : forall x, (up_vl_ty sigma) x = (up_vl_ty tau) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition upExt_vl_tm { m : nat } { nty ntm nvl : nat } (sigma : (fin) (m) -> tm (nty) (ntm) (nvl)) (tau : (fin) (m) -> tm (nty) (ntm) (nvl)) (Eq : forall x, sigma x = tau x) : forall x, (up_vl_tm sigma) x = (up_vl_tm tau) x :=
  fun n => (ap) (ren_tm (id) (id) (shift)) (Eq n).

Definition upExt_vl_vl { m : nat } { nty ntm nvl : nat } (sigma : (fin) (m) -> vl (nty) (ntm) (nvl)) (tau : (fin) (m) -> vl (nty) (ntm) (nvl)) (Eq : forall x, sigma x = tau x) : forall x, (up_vl_vl sigma) x = (up_vl_vl tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_vl (id) (id) (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint ext_tm { mty mtm mvl : nat } { nty ntm nvl : nat } (sigmaty : (fin) (mty) -> ty (nty)) (sigmatm : (fin) (mtm) -> tm (nty) (ntm) (nvl)) (sigmavl : (fin) (mvl) -> vl (nty) (ntm) (nvl)) (tauty : (fin) (mty) -> ty (nty)) (tautm : (fin) (mtm) -> tm (nty) (ntm) (nvl)) (tauvl : (fin) (mvl) -> vl (nty) (ntm) (nvl)) (Eqty : forall x, sigmaty x = tauty x) (Eqtm : forall x, sigmatm x = tautm x) (Eqvl : forall x, sigmavl x = tauvl x) (s : tm (mty) (mtm) (mvl)) : subst_tm sigmaty sigmatm sigmavl s = subst_tm tauty tautm tauvl s :=
    match s return subst_tm sigmaty sigmatm sigmavl s = subst_tm tauty tautm tauvl s with
    | var_tm (_) (_) (_) s => Eqtm s
    | app (_) (_) (_) s0 s1 => congr_app ((ext_tm sigmaty sigmatm sigmavl tauty tautm tauvl Eqty Eqtm Eqvl) s0) ((ext_tm sigmaty sigmatm sigmavl tauty tautm tauvl Eqty Eqtm Eqvl) s1)
    | tapp (_) (_) (_) s0 s1 => congr_tapp ((ext_tm sigmaty sigmatm sigmavl tauty tautm tauvl Eqty Eqtm Eqvl) s0) ((ext_ty sigmaty tauty Eqty) s1)
    | vt (_) (_) (_) s0 => congr_vt ((ext_vl sigmaty sigmatm sigmavl tauty tautm tauvl Eqty Eqtm Eqvl) s0)
    end
 with ext_vl { mty mtm mvl : nat } { nty ntm nvl : nat } (sigmaty : (fin) (mty) -> ty (nty)) (sigmatm : (fin) (mtm) -> tm (nty) (ntm) (nvl)) (sigmavl : (fin) (mvl) -> vl (nty) (ntm) (nvl)) (tauty : (fin) (mty) -> ty (nty)) (tautm : (fin) (mtm) -> tm (nty) (ntm) (nvl)) (tauvl : (fin) (mvl) -> vl (nty) (ntm) (nvl)) (Eqty : forall x, sigmaty x = tauty x) (Eqtm : forall x, sigmatm x = tautm x) (Eqvl : forall x, sigmavl x = tauvl x) (s : vl (mty) (mtm) (mvl)) : subst_vl sigmaty sigmatm sigmavl s = subst_vl tauty tautm tauvl s :=
    match s return subst_vl sigmaty sigmatm sigmavl s = subst_vl tauty tautm tauvl s with
    | var_vl (_) (_) (_) s => Eqvl s
    | lam (_) (_) (_) s0 s1 => congr_lam ((ext_ty sigmaty tauty Eqty) s0) ((ext_tm (up_tm_ty (up_vl_ty sigmaty)) (up_tm_tm (up_vl_tm sigmatm)) (up_tm_vl (up_vl_vl sigmavl)) (up_tm_ty (up_vl_ty tauty)) (up_tm_tm (up_vl_tm tautm)) (up_tm_vl (up_vl_vl tauvl)) (upExt_tm_ty (_) (_) (upExt_vl_ty (_) (_) Eqty)) (upExt_tm_tm (_) (_) (upExt_vl_tm (_) (_) Eqtm)) (upExt_tm_vl (_) (_) (upExt_vl_vl (_) (_) Eqvl))) s1)
    | tlam (_) (_) (_) s0 => congr_tlam ((ext_tm (up_ty_ty sigmaty) (up_ty_tm sigmatm) (up_ty_vl sigmavl) (up_ty_ty tauty) (up_ty_tm tautm) (up_ty_vl tauvl) (upExt_ty_ty (_) (_) Eqty) (upExt_ty_tm (_) (_) Eqtm) (upExt_ty_vl (_) (_) Eqvl)) s0)
    end.

Definition up_ren_ren_ty_tm { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_ty_tm tau) (upRen_ty_tm xi)) x = (upRen_ty_tm theta) x :=
  Eq.

Definition up_ren_ren_ty_vl { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_ty_vl tau) (upRen_ty_vl xi)) x = (upRen_ty_vl theta) x :=
  Eq.

Definition up_ren_ren_tm_ty { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_tm_ty tau) (upRen_tm_ty xi)) x = (upRen_tm_ty theta) x :=
  Eq.

Definition up_ren_ren_tm_tm { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_tm_tm tau) (upRen_tm_tm xi)) x = (upRen_tm_tm theta) x :=
  up_ren_ren xi tau theta Eq.

Definition up_ren_ren_tm_vl { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_tm_vl tau) (upRen_tm_vl xi)) x = (upRen_tm_vl theta) x :=
  Eq.

Definition up_ren_ren_vl_ty { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_vl_ty tau) (upRen_vl_ty xi)) x = (upRen_vl_ty theta) x :=
  Eq.

Definition up_ren_ren_vl_tm { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_vl_tm tau) (upRen_vl_tm xi)) x = (upRen_vl_tm theta) x :=
  Eq.

Definition up_ren_ren_vl_vl { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_vl_vl tau) (upRen_vl_vl xi)) x = (upRen_vl_vl theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_tm { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (xity : (fin) (mty) -> (fin) (kty)) (xitm : (fin) (mtm) -> (fin) (ktm)) (xivl : (fin) (mvl) -> (fin) (kvl)) (zetaty : (fin) (kty) -> (fin) (lty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (rhoty : (fin) (mty) -> (fin) (lty)) (rhotm : (fin) (mtm) -> (fin) (ltm)) (rhovl : (fin) (mvl) -> (fin) (lvl)) (Eqty : forall x, ((funcomp) zetaty xity) x = rhoty x) (Eqtm : forall x, ((funcomp) zetatm xitm) x = rhotm x) (Eqvl : forall x, ((funcomp) zetavl xivl) x = rhovl x) (s : tm (mty) (mtm) (mvl)) : ren_tm zetaty zetatm zetavl (ren_tm xity xitm xivl s) = ren_tm rhoty rhotm rhovl s :=
    match s return ren_tm zetaty zetatm zetavl (ren_tm xity xitm xivl s) = ren_tm rhoty rhotm rhovl s with
    | var_tm (_) (_) (_) s => (ap) (var_tm (lty) (ltm) (lvl)) (Eqtm s)
    | app (_) (_) (_) s0 s1 => congr_app ((compRenRen_tm xity xitm xivl zetaty zetatm zetavl rhoty rhotm rhovl Eqty Eqtm Eqvl) s0) ((compRenRen_tm xity xitm xivl zetaty zetatm zetavl rhoty rhotm rhovl Eqty Eqtm Eqvl) s1)
    | tapp (_) (_) (_) s0 s1 => congr_tapp ((compRenRen_tm xity xitm xivl zetaty zetatm zetavl rhoty rhotm rhovl Eqty Eqtm Eqvl) s0) ((compRenRen_ty xity zetaty rhoty Eqty) s1)
    | vt (_) (_) (_) s0 => congr_vt ((compRenRen_vl xity xitm xivl zetaty zetatm zetavl rhoty rhotm rhovl Eqty Eqtm Eqvl) s0)
    end
 with compRenRen_vl { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (xity : (fin) (mty) -> (fin) (kty)) (xitm : (fin) (mtm) -> (fin) (ktm)) (xivl : (fin) (mvl) -> (fin) (kvl)) (zetaty : (fin) (kty) -> (fin) (lty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (rhoty : (fin) (mty) -> (fin) (lty)) (rhotm : (fin) (mtm) -> (fin) (ltm)) (rhovl : (fin) (mvl) -> (fin) (lvl)) (Eqty : forall x, ((funcomp) zetaty xity) x = rhoty x) (Eqtm : forall x, ((funcomp) zetatm xitm) x = rhotm x) (Eqvl : forall x, ((funcomp) zetavl xivl) x = rhovl x) (s : vl (mty) (mtm) (mvl)) : ren_vl zetaty zetatm zetavl (ren_vl xity xitm xivl s) = ren_vl rhoty rhotm rhovl s :=
    match s return ren_vl zetaty zetatm zetavl (ren_vl xity xitm xivl s) = ren_vl rhoty rhotm rhovl s with
    | var_vl (_) (_) (_) s => (ap) (var_vl (lty) (ltm) (lvl)) (Eqvl s)
    | lam (_) (_) (_) s0 s1 => congr_lam ((compRenRen_ty xity zetaty rhoty Eqty) s0) ((compRenRen_tm (upRen_tm_ty (upRen_vl_ty xity)) (upRen_tm_tm (upRen_vl_tm xitm)) (upRen_tm_vl (upRen_vl_vl xivl)) (upRen_tm_ty (upRen_vl_ty zetaty)) (upRen_tm_tm (upRen_vl_tm zetatm)) (upRen_tm_vl (upRen_vl_vl zetavl)) (upRen_tm_ty (upRen_vl_ty rhoty)) (upRen_tm_tm (upRen_vl_tm rhotm)) (upRen_tm_vl (upRen_vl_vl rhovl)) Eqty (up_ren_ren (_) (_) (_) Eqtm) (up_ren_ren (_) (_) (_) Eqvl)) s1)
    | tlam (_) (_) (_) s0 => congr_tlam ((compRenRen_tm (upRen_ty_ty xity) (upRen_ty_tm xitm) (upRen_ty_vl xivl) (upRen_ty_ty zetaty) (upRen_ty_tm zetatm) (upRen_ty_vl zetavl) (upRen_ty_ty rhoty) (upRen_ty_tm rhotm) (upRen_ty_vl rhovl) (up_ren_ren (_) (_) (_) Eqty) Eqtm Eqvl) s0)
    end.

Definition up_ren_subst_ty_tm { k : nat } { l : nat } { mty mtm mvl : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> tm (mty) (mtm) (mvl)) (theta : (fin) (k) -> tm (mty) (mtm) (mvl)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_ty_tm tau) (upRen_ty_tm xi)) x = (up_ty_tm theta) x :=
  fun n => (ap) (ren_tm (shift) (id) (id)) (Eq n).

Definition up_ren_subst_ty_vl { k : nat } { l : nat } { mty mtm mvl : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> vl (mty) (mtm) (mvl)) (theta : (fin) (k) -> vl (mty) (mtm) (mvl)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_ty_vl tau) (upRen_ty_vl xi)) x = (up_ty_vl theta) x :=
  fun n => (ap) (ren_vl (shift) (id) (id)) (Eq n).

Definition up_ren_subst_tm_ty { k : nat } { l : nat } { mty : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_tm_ty tau) (upRen_tm_ty xi)) x = (up_tm_ty theta) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition up_ren_subst_tm_tm { k : nat } { l : nat } { mty mtm mvl : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> tm (mty) (mtm) (mvl)) (theta : (fin) (k) -> tm (mty) (mtm) (mvl)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_tm_tm tau) (upRen_tm_tm xi)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (id) (shift) (id)) (Eq fin_n)
  | None  => eq_refl
  end.

Definition up_ren_subst_tm_vl { k : nat } { l : nat } { mty mtm mvl : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> vl (mty) (mtm) (mvl)) (theta : (fin) (k) -> vl (mty) (mtm) (mvl)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_tm_vl tau) (upRen_tm_vl xi)) x = (up_tm_vl theta) x :=
  fun n => (ap) (ren_vl (id) (shift) (id)) (Eq n).

Definition up_ren_subst_vl_ty { k : nat } { l : nat } { mty : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_vl_ty tau) (upRen_vl_ty xi)) x = (up_vl_ty theta) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition up_ren_subst_vl_tm { k : nat } { l : nat } { mty mtm mvl : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> tm (mty) (mtm) (mvl)) (theta : (fin) (k) -> tm (mty) (mtm) (mvl)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_vl_tm tau) (upRen_vl_tm xi)) x = (up_vl_tm theta) x :=
  fun n => (ap) (ren_tm (id) (id) (shift)) (Eq n).

Definition up_ren_subst_vl_vl { k : nat } { l : nat } { mty mtm mvl : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> vl (mty) (mtm) (mvl)) (theta : (fin) (k) -> vl (mty) (mtm) (mvl)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_vl_vl tau) (upRen_vl_vl xi)) x = (up_vl_vl theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_vl (id) (id) (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint compRenSubst_tm { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (xity : (fin) (mty) -> (fin) (kty)) (xitm : (fin) (mtm) -> (fin) (ktm)) (xivl : (fin) (mvl) -> (fin) (kvl)) (tauty : (fin) (kty) -> ty (lty)) (tautm : (fin) (ktm) -> tm (lty) (ltm) (lvl)) (tauvl : (fin) (kvl) -> vl (lty) (ltm) (lvl)) (thetaty : (fin) (mty) -> ty (lty)) (thetatm : (fin) (mtm) -> tm (lty) (ltm) (lvl)) (thetavl : (fin) (mvl) -> vl (lty) (ltm) (lvl)) (Eqty : forall x, ((funcomp) tauty xity) x = thetaty x) (Eqtm : forall x, ((funcomp) tautm xitm) x = thetatm x) (Eqvl : forall x, ((funcomp) tauvl xivl) x = thetavl x) (s : tm (mty) (mtm) (mvl)) : subst_tm tauty tautm tauvl (ren_tm xity xitm xivl s) = subst_tm thetaty thetatm thetavl s :=
    match s return subst_tm tauty tautm tauvl (ren_tm xity xitm xivl s) = subst_tm thetaty thetatm thetavl s with
    | var_tm (_) (_) (_) s => Eqtm s
    | app (_) (_) (_) s0 s1 => congr_app ((compRenSubst_tm xity xitm xivl tauty tautm tauvl thetaty thetatm thetavl Eqty Eqtm Eqvl) s0) ((compRenSubst_tm xity xitm xivl tauty tautm tauvl thetaty thetatm thetavl Eqty Eqtm Eqvl) s1)
    | tapp (_) (_) (_) s0 s1 => congr_tapp ((compRenSubst_tm xity xitm xivl tauty tautm tauvl thetaty thetatm thetavl Eqty Eqtm Eqvl) s0) ((compRenSubst_ty xity tauty thetaty Eqty) s1)
    | vt (_) (_) (_) s0 => congr_vt ((compRenSubst_vl xity xitm xivl tauty tautm tauvl thetaty thetatm thetavl Eqty Eqtm Eqvl) s0)
    end
 with compRenSubst_vl { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (xity : (fin) (mty) -> (fin) (kty)) (xitm : (fin) (mtm) -> (fin) (ktm)) (xivl : (fin) (mvl) -> (fin) (kvl)) (tauty : (fin) (kty) -> ty (lty)) (tautm : (fin) (ktm) -> tm (lty) (ltm) (lvl)) (tauvl : (fin) (kvl) -> vl (lty) (ltm) (lvl)) (thetaty : (fin) (mty) -> ty (lty)) (thetatm : (fin) (mtm) -> tm (lty) (ltm) (lvl)) (thetavl : (fin) (mvl) -> vl (lty) (ltm) (lvl)) (Eqty : forall x, ((funcomp) tauty xity) x = thetaty x) (Eqtm : forall x, ((funcomp) tautm xitm) x = thetatm x) (Eqvl : forall x, ((funcomp) tauvl xivl) x = thetavl x) (s : vl (mty) (mtm) (mvl)) : subst_vl tauty tautm tauvl (ren_vl xity xitm xivl s) = subst_vl thetaty thetatm thetavl s :=
    match s return subst_vl tauty tautm tauvl (ren_vl xity xitm xivl s) = subst_vl thetaty thetatm thetavl s with
    | var_vl (_) (_) (_) s => Eqvl s
    | lam (_) (_) (_) s0 s1 => congr_lam ((compRenSubst_ty xity tauty thetaty Eqty) s0) ((compRenSubst_tm (upRen_tm_ty (upRen_vl_ty xity)) (upRen_tm_tm (upRen_vl_tm xitm)) (upRen_tm_vl (upRen_vl_vl xivl)) (up_tm_ty (up_vl_ty tauty)) (up_tm_tm (up_vl_tm tautm)) (up_tm_vl (up_vl_vl tauvl)) (up_tm_ty (up_vl_ty thetaty)) (up_tm_tm (up_vl_tm thetatm)) (up_tm_vl (up_vl_vl thetavl)) (up_ren_subst_tm_ty (_) (_) (_) (up_ren_subst_vl_ty (_) (_) (_) Eqty)) (up_ren_subst_tm_tm (_) (_) (_) (up_ren_subst_vl_tm (_) (_) (_) Eqtm)) (up_ren_subst_tm_vl (_) (_) (_) (up_ren_subst_vl_vl (_) (_) (_) Eqvl))) s1)
    | tlam (_) (_) (_) s0 => congr_tlam ((compRenSubst_tm (upRen_ty_ty xity) (upRen_ty_tm xitm) (upRen_ty_vl xivl) (up_ty_ty tauty) (up_ty_tm tautm) (up_ty_vl tauvl) (up_ty_ty thetaty) (up_ty_tm thetatm) (up_ty_vl thetavl) (up_ren_subst_ty_ty (_) (_) (_) Eqty) (up_ren_subst_ty_tm (_) (_) (_) Eqtm) (up_ren_subst_ty_vl (_) (_) (_) Eqvl)) s0)
    end.

Definition up_subst_ren_ty_tm { k : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigma : (fin) (k) -> tm (lty) (ltm) (lvl)) (zetaty : (fin) (lty) -> (fin) (mty)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (zetavl : (fin) (lvl) -> (fin) (mvl)) (theta : (fin) (k) -> tm (mty) (mtm) (mvl)) (Eq : forall x, ((funcomp) (ren_tm zetaty zetatm zetavl) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRen_ty_ty zetaty) (upRen_ty_tm zetatm) (upRen_ty_vl zetavl)) (up_ty_tm sigma)) x = (up_ty_tm theta) x :=
  fun n => (eq_trans) (compRenRen_tm (shift) (id) (id) (upRen_ty_ty zetaty) (upRen_ty_tm zetatm) (upRen_ty_vl zetavl) ((funcomp) (shift) zetaty) ((funcomp) (id) zetatm) ((funcomp) (id) zetavl) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetaty zetatm zetavl (shift) (id) (id) ((funcomp) (shift) zetaty) ((funcomp) (id) zetatm) ((funcomp) (id) zetavl) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_tm (shift) (id) (id)) (Eq n))).

Definition up_subst_ren_ty_vl { k : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigma : (fin) (k) -> vl (lty) (ltm) (lvl)) (zetaty : (fin) (lty) -> (fin) (mty)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (zetavl : (fin) (lvl) -> (fin) (mvl)) (theta : (fin) (k) -> vl (mty) (mtm) (mvl)) (Eq : forall x, ((funcomp) (ren_vl zetaty zetatm zetavl) sigma) x = theta x) : forall x, ((funcomp) (ren_vl (upRen_ty_ty zetaty) (upRen_ty_tm zetatm) (upRen_ty_vl zetavl)) (up_ty_vl sigma)) x = (up_ty_vl theta) x :=
  fun n => (eq_trans) (compRenRen_vl (shift) (id) (id) (upRen_ty_ty zetaty) (upRen_ty_tm zetatm) (upRen_ty_vl zetavl) ((funcomp) (shift) zetaty) ((funcomp) (id) zetatm) ((funcomp) (id) zetavl) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_vl zetaty zetatm zetavl (shift) (id) (id) ((funcomp) (shift) zetaty) ((funcomp) (id) zetatm) ((funcomp) (id) zetavl) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_vl (shift) (id) (id)) (Eq n))).

Definition up_subst_ren_tm_ty { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (zetaty : (fin) (lty) -> (fin) (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (ren_ty zetaty) sigma) x = theta x) : forall x, ((funcomp) (ren_ty (upRen_tm_ty zetaty)) (up_tm_ty sigma)) x = (up_tm_ty theta) x :=
  fun n => (eq_trans) (compRenRen_ty (id) (upRen_tm_ty zetaty) ((funcomp) (id) zetaty) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_ty zetaty (id) ((funcomp) (id) zetaty) (fun x => eq_refl) (sigma n))) ((ap) (ren_ty (id)) (Eq n))).

Definition up_subst_ren_tm_tm { k : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigma : (fin) (k) -> tm (lty) (ltm) (lvl)) (zetaty : (fin) (lty) -> (fin) (mty)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (zetavl : (fin) (lvl) -> (fin) (mvl)) (theta : (fin) (k) -> tm (mty) (mtm) (mvl)) (Eq : forall x, ((funcomp) (ren_tm zetaty zetatm zetavl) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRen_tm_ty zetaty) (upRen_tm_tm zetatm) (upRen_tm_vl zetavl)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_tm (id) (shift) (id) (upRen_tm_ty zetaty) (upRen_tm_tm zetatm) (upRen_tm_vl zetavl) ((funcomp) (id) zetaty) ((funcomp) (shift) zetatm) ((funcomp) (id) zetavl) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetaty zetatm zetavl (id) (shift) (id) ((funcomp) (id) zetaty) ((funcomp) (shift) zetatm) ((funcomp) (id) zetavl) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_tm (id) (shift) (id)) (Eq fin_n)))
  | None  => eq_refl
  end.

Definition up_subst_ren_tm_vl { k : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigma : (fin) (k) -> vl (lty) (ltm) (lvl)) (zetaty : (fin) (lty) -> (fin) (mty)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (zetavl : (fin) (lvl) -> (fin) (mvl)) (theta : (fin) (k) -> vl (mty) (mtm) (mvl)) (Eq : forall x, ((funcomp) (ren_vl zetaty zetatm zetavl) sigma) x = theta x) : forall x, ((funcomp) (ren_vl (upRen_tm_ty zetaty) (upRen_tm_tm zetatm) (upRen_tm_vl zetavl)) (up_tm_vl sigma)) x = (up_tm_vl theta) x :=
  fun n => (eq_trans) (compRenRen_vl (id) (shift) (id) (upRen_tm_ty zetaty) (upRen_tm_tm zetatm) (upRen_tm_vl zetavl) ((funcomp) (id) zetaty) ((funcomp) (shift) zetatm) ((funcomp) (id) zetavl) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_vl zetaty zetatm zetavl (id) (shift) (id) ((funcomp) (id) zetaty) ((funcomp) (shift) zetatm) ((funcomp) (id) zetavl) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_vl (id) (shift) (id)) (Eq n))).

Definition up_subst_ren_vl_ty { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (zetaty : (fin) (lty) -> (fin) (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (ren_ty zetaty) sigma) x = theta x) : forall x, ((funcomp) (ren_ty (upRen_vl_ty zetaty)) (up_vl_ty sigma)) x = (up_vl_ty theta) x :=
  fun n => (eq_trans) (compRenRen_ty (id) (upRen_vl_ty zetaty) ((funcomp) (id) zetaty) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_ty zetaty (id) ((funcomp) (id) zetaty) (fun x => eq_refl) (sigma n))) ((ap) (ren_ty (id)) (Eq n))).

Definition up_subst_ren_vl_tm { k : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigma : (fin) (k) -> tm (lty) (ltm) (lvl)) (zetaty : (fin) (lty) -> (fin) (mty)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (zetavl : (fin) (lvl) -> (fin) (mvl)) (theta : (fin) (k) -> tm (mty) (mtm) (mvl)) (Eq : forall x, ((funcomp) (ren_tm zetaty zetatm zetavl) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRen_vl_ty zetaty) (upRen_vl_tm zetatm) (upRen_vl_vl zetavl)) (up_vl_tm sigma)) x = (up_vl_tm theta) x :=
  fun n => (eq_trans) (compRenRen_tm (id) (id) (shift) (upRen_vl_ty zetaty) (upRen_vl_tm zetatm) (upRen_vl_vl zetavl) ((funcomp) (id) zetaty) ((funcomp) (id) zetatm) ((funcomp) (shift) zetavl) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetaty zetatm zetavl (id) (id) (shift) ((funcomp) (id) zetaty) ((funcomp) (id) zetatm) ((funcomp) (shift) zetavl) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_tm (id) (id) (shift)) (Eq n))).

Definition up_subst_ren_vl_vl { k : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigma : (fin) (k) -> vl (lty) (ltm) (lvl)) (zetaty : (fin) (lty) -> (fin) (mty)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (zetavl : (fin) (lvl) -> (fin) (mvl)) (theta : (fin) (k) -> vl (mty) (mtm) (mvl)) (Eq : forall x, ((funcomp) (ren_vl zetaty zetatm zetavl) sigma) x = theta x) : forall x, ((funcomp) (ren_vl (upRen_vl_ty zetaty) (upRen_vl_tm zetatm) (upRen_vl_vl zetavl)) (up_vl_vl sigma)) x = (up_vl_vl theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_vl (id) (id) (shift) (upRen_vl_ty zetaty) (upRen_vl_tm zetatm) (upRen_vl_vl zetavl) ((funcomp) (id) zetaty) ((funcomp) (id) zetatm) ((funcomp) (shift) zetavl) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_vl zetaty zetatm zetavl (id) (id) (shift) ((funcomp) (id) zetaty) ((funcomp) (id) zetatm) ((funcomp) (shift) zetavl) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_vl (id) (id) (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstRen_tm { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigmaty : (fin) (mty) -> ty (kty)) (sigmatm : (fin) (mtm) -> tm (kty) (ktm) (kvl)) (sigmavl : (fin) (mvl) -> vl (kty) (ktm) (kvl)) (zetaty : (fin) (kty) -> (fin) (lty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (thetaty : (fin) (mty) -> ty (lty)) (thetatm : (fin) (mtm) -> tm (lty) (ltm) (lvl)) (thetavl : (fin) (mvl) -> vl (lty) (ltm) (lvl)) (Eqty : forall x, ((funcomp) (ren_ty zetaty) sigmaty) x = thetaty x) (Eqtm : forall x, ((funcomp) (ren_tm zetaty zetatm zetavl) sigmatm) x = thetatm x) (Eqvl : forall x, ((funcomp) (ren_vl zetaty zetatm zetavl) sigmavl) x = thetavl x) (s : tm (mty) (mtm) (mvl)) : ren_tm zetaty zetatm zetavl (subst_tm sigmaty sigmatm sigmavl s) = subst_tm thetaty thetatm thetavl s :=
    match s return ren_tm zetaty zetatm zetavl (subst_tm sigmaty sigmatm sigmavl s) = subst_tm thetaty thetatm thetavl s with
    | var_tm (_) (_) (_) s => Eqtm s
    | app (_) (_) (_) s0 s1 => congr_app ((compSubstRen_tm sigmaty sigmatm sigmavl zetaty zetatm zetavl thetaty thetatm thetavl Eqty Eqtm Eqvl) s0) ((compSubstRen_tm sigmaty sigmatm sigmavl zetaty zetatm zetavl thetaty thetatm thetavl Eqty Eqtm Eqvl) s1)
    | tapp (_) (_) (_) s0 s1 => congr_tapp ((compSubstRen_tm sigmaty sigmatm sigmavl zetaty zetatm zetavl thetaty thetatm thetavl Eqty Eqtm Eqvl) s0) ((compSubstRen_ty sigmaty zetaty thetaty Eqty) s1)
    | vt (_) (_) (_) s0 => congr_vt ((compSubstRen_vl sigmaty sigmatm sigmavl zetaty zetatm zetavl thetaty thetatm thetavl Eqty Eqtm Eqvl) s0)
    end
 with compSubstRen_vl { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigmaty : (fin) (mty) -> ty (kty)) (sigmatm : (fin) (mtm) -> tm (kty) (ktm) (kvl)) (sigmavl : (fin) (mvl) -> vl (kty) (ktm) (kvl)) (zetaty : (fin) (kty) -> (fin) (lty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (thetaty : (fin) (mty) -> ty (lty)) (thetatm : (fin) (mtm) -> tm (lty) (ltm) (lvl)) (thetavl : (fin) (mvl) -> vl (lty) (ltm) (lvl)) (Eqty : forall x, ((funcomp) (ren_ty zetaty) sigmaty) x = thetaty x) (Eqtm : forall x, ((funcomp) (ren_tm zetaty zetatm zetavl) sigmatm) x = thetatm x) (Eqvl : forall x, ((funcomp) (ren_vl zetaty zetatm zetavl) sigmavl) x = thetavl x) (s : vl (mty) (mtm) (mvl)) : ren_vl zetaty zetatm zetavl (subst_vl sigmaty sigmatm sigmavl s) = subst_vl thetaty thetatm thetavl s :=
    match s return ren_vl zetaty zetatm zetavl (subst_vl sigmaty sigmatm sigmavl s) = subst_vl thetaty thetatm thetavl s with
    | var_vl (_) (_) (_) s => Eqvl s
    | lam (_) (_) (_) s0 s1 => congr_lam ((compSubstRen_ty sigmaty zetaty thetaty Eqty) s0) ((compSubstRen_tm (up_tm_ty (up_vl_ty sigmaty)) (up_tm_tm (up_vl_tm sigmatm)) (up_tm_vl (up_vl_vl sigmavl)) (upRen_tm_ty (upRen_vl_ty zetaty)) (upRen_tm_tm (upRen_vl_tm zetatm)) (upRen_tm_vl (upRen_vl_vl zetavl)) (up_tm_ty (up_vl_ty thetaty)) (up_tm_tm (up_vl_tm thetatm)) (up_tm_vl (up_vl_vl thetavl)) (up_subst_ren_tm_ty (_) (_) (_) (up_subst_ren_vl_ty (_) (_) (_) Eqty)) (up_subst_ren_tm_tm (_) (_) (_) (_) (_) (up_subst_ren_vl_tm (_) (_) (_) (_) (_) Eqtm)) (up_subst_ren_tm_vl (_) (_) (_) (_) (_) (up_subst_ren_vl_vl (_) (_) (_) (_) (_) Eqvl))) s1)
    | tlam (_) (_) (_) s0 => congr_tlam ((compSubstRen_tm (up_ty_ty sigmaty) (up_ty_tm sigmatm) (up_ty_vl sigmavl) (upRen_ty_ty zetaty) (upRen_ty_tm zetatm) (upRen_ty_vl zetavl) (up_ty_ty thetaty) (up_ty_tm thetatm) (up_ty_vl thetavl) (up_subst_ren_ty_ty (_) (_) (_) Eqty) (up_subst_ren_ty_tm (_) (_) (_) (_) (_) Eqtm) (up_subst_ren_ty_vl (_) (_) (_) (_) (_) Eqvl)) s0)
    end.

Definition up_subst_subst_ty_tm { k : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigma : (fin) (k) -> tm (lty) (ltm) (lvl)) (tauty : (fin) (lty) -> ty (mty)) (tautm : (fin) (ltm) -> tm (mty) (mtm) (mvl)) (tauvl : (fin) (lvl) -> vl (mty) (mtm) (mvl)) (theta : (fin) (k) -> tm (mty) (mtm) (mvl)) (Eq : forall x, ((funcomp) (subst_tm tauty tautm tauvl) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (up_ty_ty tauty) (up_ty_tm tautm) (up_ty_vl tauvl)) (up_ty_tm sigma)) x = (up_ty_tm theta) x :=
  fun n => (eq_trans) (compRenSubst_tm (shift) (id) (id) (up_ty_ty tauty) (up_ty_tm tautm) (up_ty_vl tauvl) ((funcomp) (up_ty_ty tauty) (shift)) ((funcomp) (up_ty_tm tautm) (id)) ((funcomp) (up_ty_vl tauvl) (id)) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tauty tautm tauvl (shift) (id) (id) ((funcomp) (ren_ty (shift)) tauty) ((funcomp) (ren_tm (shift) (id) (id)) tautm) ((funcomp) (ren_vl (shift) (id) (id)) tauvl) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_tm (shift) (id) (id)) (Eq n))).

Definition up_subst_subst_ty_vl { k : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigma : (fin) (k) -> vl (lty) (ltm) (lvl)) (tauty : (fin) (lty) -> ty (mty)) (tautm : (fin) (ltm) -> tm (mty) (mtm) (mvl)) (tauvl : (fin) (lvl) -> vl (mty) (mtm) (mvl)) (theta : (fin) (k) -> vl (mty) (mtm) (mvl)) (Eq : forall x, ((funcomp) (subst_vl tauty tautm tauvl) sigma) x = theta x) : forall x, ((funcomp) (subst_vl (up_ty_ty tauty) (up_ty_tm tautm) (up_ty_vl tauvl)) (up_ty_vl sigma)) x = (up_ty_vl theta) x :=
  fun n => (eq_trans) (compRenSubst_vl (shift) (id) (id) (up_ty_ty tauty) (up_ty_tm tautm) (up_ty_vl tauvl) ((funcomp) (up_ty_ty tauty) (shift)) ((funcomp) (up_ty_tm tautm) (id)) ((funcomp) (up_ty_vl tauvl) (id)) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_vl tauty tautm tauvl (shift) (id) (id) ((funcomp) (ren_ty (shift)) tauty) ((funcomp) (ren_tm (shift) (id) (id)) tautm) ((funcomp) (ren_vl (shift) (id) (id)) tauvl) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_vl (shift) (id) (id)) (Eq n))).

Definition up_subst_subst_tm_ty { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (tauty : (fin) (lty) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (subst_ty tauty) sigma) x = theta x) : forall x, ((funcomp) (subst_ty (up_tm_ty tauty)) (up_tm_ty sigma)) x = (up_tm_ty theta) x :=
  fun n => (eq_trans) (compRenSubst_ty (id) (up_tm_ty tauty) ((funcomp) (up_tm_ty tauty) (id)) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_ty tauty (id) ((funcomp) (ren_ty (id)) tauty) (fun x => eq_refl) (sigma n))) ((ap) (ren_ty (id)) (Eq n))).

Definition up_subst_subst_tm_tm { k : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigma : (fin) (k) -> tm (lty) (ltm) (lvl)) (tauty : (fin) (lty) -> ty (mty)) (tautm : (fin) (ltm) -> tm (mty) (mtm) (mvl)) (tauvl : (fin) (lvl) -> vl (mty) (mtm) (mvl)) (theta : (fin) (k) -> tm (mty) (mtm) (mvl)) (Eq : forall x, ((funcomp) (subst_tm tauty tautm tauvl) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (up_tm_ty tauty) (up_tm_tm tautm) (up_tm_vl tauvl)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_tm (id) (shift) (id) (up_tm_ty tauty) (up_tm_tm tautm) (up_tm_vl tauvl) ((funcomp) (up_tm_ty tauty) (id)) ((funcomp) (up_tm_tm tautm) (shift)) ((funcomp) (up_tm_vl tauvl) (id)) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tauty tautm tauvl (id) (shift) (id) ((funcomp) (ren_ty (id)) tauty) ((funcomp) (ren_tm (id) (shift) (id)) tautm) ((funcomp) (ren_vl (id) (shift) (id)) tauvl) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_tm (id) (shift) (id)) (Eq fin_n)))
  | None  => eq_refl
  end.

Definition up_subst_subst_tm_vl { k : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigma : (fin) (k) -> vl (lty) (ltm) (lvl)) (tauty : (fin) (lty) -> ty (mty)) (tautm : (fin) (ltm) -> tm (mty) (mtm) (mvl)) (tauvl : (fin) (lvl) -> vl (mty) (mtm) (mvl)) (theta : (fin) (k) -> vl (mty) (mtm) (mvl)) (Eq : forall x, ((funcomp) (subst_vl tauty tautm tauvl) sigma) x = theta x) : forall x, ((funcomp) (subst_vl (up_tm_ty tauty) (up_tm_tm tautm) (up_tm_vl tauvl)) (up_tm_vl sigma)) x = (up_tm_vl theta) x :=
  fun n => (eq_trans) (compRenSubst_vl (id) (shift) (id) (up_tm_ty tauty) (up_tm_tm tautm) (up_tm_vl tauvl) ((funcomp) (up_tm_ty tauty) (id)) ((funcomp) (up_tm_tm tautm) (shift)) ((funcomp) (up_tm_vl tauvl) (id)) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_vl tauty tautm tauvl (id) (shift) (id) ((funcomp) (ren_ty (id)) tauty) ((funcomp) (ren_tm (id) (shift) (id)) tautm) ((funcomp) (ren_vl (id) (shift) (id)) tauvl) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_vl (id) (shift) (id)) (Eq n))).

Definition up_subst_subst_vl_ty { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (tauty : (fin) (lty) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (subst_ty tauty) sigma) x = theta x) : forall x, ((funcomp) (subst_ty (up_vl_ty tauty)) (up_vl_ty sigma)) x = (up_vl_ty theta) x :=
  fun n => (eq_trans) (compRenSubst_ty (id) (up_vl_ty tauty) ((funcomp) (up_vl_ty tauty) (id)) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_ty tauty (id) ((funcomp) (ren_ty (id)) tauty) (fun x => eq_refl) (sigma n))) ((ap) (ren_ty (id)) (Eq n))).

Definition up_subst_subst_vl_tm { k : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigma : (fin) (k) -> tm (lty) (ltm) (lvl)) (tauty : (fin) (lty) -> ty (mty)) (tautm : (fin) (ltm) -> tm (mty) (mtm) (mvl)) (tauvl : (fin) (lvl) -> vl (mty) (mtm) (mvl)) (theta : (fin) (k) -> tm (mty) (mtm) (mvl)) (Eq : forall x, ((funcomp) (subst_tm tauty tautm tauvl) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (up_vl_ty tauty) (up_vl_tm tautm) (up_vl_vl tauvl)) (up_vl_tm sigma)) x = (up_vl_tm theta) x :=
  fun n => (eq_trans) (compRenSubst_tm (id) (id) (shift) (up_vl_ty tauty) (up_vl_tm tautm) (up_vl_vl tauvl) ((funcomp) (up_vl_ty tauty) (id)) ((funcomp) (up_vl_tm tautm) (id)) ((funcomp) (up_vl_vl tauvl) (shift)) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tauty tautm tauvl (id) (id) (shift) ((funcomp) (ren_ty (id)) tauty) ((funcomp) (ren_tm (id) (id) (shift)) tautm) ((funcomp) (ren_vl (id) (id) (shift)) tauvl) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_tm (id) (id) (shift)) (Eq n))).

Definition up_subst_subst_vl_vl { k : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigma : (fin) (k) -> vl (lty) (ltm) (lvl)) (tauty : (fin) (lty) -> ty (mty)) (tautm : (fin) (ltm) -> tm (mty) (mtm) (mvl)) (tauvl : (fin) (lvl) -> vl (mty) (mtm) (mvl)) (theta : (fin) (k) -> vl (mty) (mtm) (mvl)) (Eq : forall x, ((funcomp) (subst_vl tauty tautm tauvl) sigma) x = theta x) : forall x, ((funcomp) (subst_vl (up_vl_ty tauty) (up_vl_tm tautm) (up_vl_vl tauvl)) (up_vl_vl sigma)) x = (up_vl_vl theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_vl (id) (id) (shift) (up_vl_ty tauty) (up_vl_tm tautm) (up_vl_vl tauvl) ((funcomp) (up_vl_ty tauty) (id)) ((funcomp) (up_vl_tm tautm) (id)) ((funcomp) (up_vl_vl tauvl) (shift)) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_vl tauty tautm tauvl (id) (id) (shift) ((funcomp) (ren_ty (id)) tauty) ((funcomp) (ren_tm (id) (id) (shift)) tautm) ((funcomp) (ren_vl (id) (id) (shift)) tauvl) (fun x => eq_refl) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_vl (id) (id) (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstSubst_tm { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigmaty : (fin) (mty) -> ty (kty)) (sigmatm : (fin) (mtm) -> tm (kty) (ktm) (kvl)) (sigmavl : (fin) (mvl) -> vl (kty) (ktm) (kvl)) (tauty : (fin) (kty) -> ty (lty)) (tautm : (fin) (ktm) -> tm (lty) (ltm) (lvl)) (tauvl : (fin) (kvl) -> vl (lty) (ltm) (lvl)) (thetaty : (fin) (mty) -> ty (lty)) (thetatm : (fin) (mtm) -> tm (lty) (ltm) (lvl)) (thetavl : (fin) (mvl) -> vl (lty) (ltm) (lvl)) (Eqty : forall x, ((funcomp) (subst_ty tauty) sigmaty) x = thetaty x) (Eqtm : forall x, ((funcomp) (subst_tm tauty tautm tauvl) sigmatm) x = thetatm x) (Eqvl : forall x, ((funcomp) (subst_vl tauty tautm tauvl) sigmavl) x = thetavl x) (s : tm (mty) (mtm) (mvl)) : subst_tm tauty tautm tauvl (subst_tm sigmaty sigmatm sigmavl s) = subst_tm thetaty thetatm thetavl s :=
    match s return subst_tm tauty tautm tauvl (subst_tm sigmaty sigmatm sigmavl s) = subst_tm thetaty thetatm thetavl s with
    | var_tm (_) (_) (_) s => Eqtm s
    | app (_) (_) (_) s0 s1 => congr_app ((compSubstSubst_tm sigmaty sigmatm sigmavl tauty tautm tauvl thetaty thetatm thetavl Eqty Eqtm Eqvl) s0) ((compSubstSubst_tm sigmaty sigmatm sigmavl tauty tautm tauvl thetaty thetatm thetavl Eqty Eqtm Eqvl) s1)
    | tapp (_) (_) (_) s0 s1 => congr_tapp ((compSubstSubst_tm sigmaty sigmatm sigmavl tauty tautm tauvl thetaty thetatm thetavl Eqty Eqtm Eqvl) s0) ((compSubstSubst_ty sigmaty tauty thetaty Eqty) s1)
    | vt (_) (_) (_) s0 => congr_vt ((compSubstSubst_vl sigmaty sigmatm sigmavl tauty tautm tauvl thetaty thetatm thetavl Eqty Eqtm Eqvl) s0)
    end
 with compSubstSubst_vl { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigmaty : (fin) (mty) -> ty (kty)) (sigmatm : (fin) (mtm) -> tm (kty) (ktm) (kvl)) (sigmavl : (fin) (mvl) -> vl (kty) (ktm) (kvl)) (tauty : (fin) (kty) -> ty (lty)) (tautm : (fin) (ktm) -> tm (lty) (ltm) (lvl)) (tauvl : (fin) (kvl) -> vl (lty) (ltm) (lvl)) (thetaty : (fin) (mty) -> ty (lty)) (thetatm : (fin) (mtm) -> tm (lty) (ltm) (lvl)) (thetavl : (fin) (mvl) -> vl (lty) (ltm) (lvl)) (Eqty : forall x, ((funcomp) (subst_ty tauty) sigmaty) x = thetaty x) (Eqtm : forall x, ((funcomp) (subst_tm tauty tautm tauvl) sigmatm) x = thetatm x) (Eqvl : forall x, ((funcomp) (subst_vl tauty tautm tauvl) sigmavl) x = thetavl x) (s : vl (mty) (mtm) (mvl)) : subst_vl tauty tautm tauvl (subst_vl sigmaty sigmatm sigmavl s) = subst_vl thetaty thetatm thetavl s :=
    match s return subst_vl tauty tautm tauvl (subst_vl sigmaty sigmatm sigmavl s) = subst_vl thetaty thetatm thetavl s with
    | var_vl (_) (_) (_) s => Eqvl s
    | lam (_) (_) (_) s0 s1 => congr_lam ((compSubstSubst_ty sigmaty tauty thetaty Eqty) s0) ((compSubstSubst_tm (up_tm_ty (up_vl_ty sigmaty)) (up_tm_tm (up_vl_tm sigmatm)) (up_tm_vl (up_vl_vl sigmavl)) (up_tm_ty (up_vl_ty tauty)) (up_tm_tm (up_vl_tm tautm)) (up_tm_vl (up_vl_vl tauvl)) (up_tm_ty (up_vl_ty thetaty)) (up_tm_tm (up_vl_tm thetatm)) (up_tm_vl (up_vl_vl thetavl)) (up_subst_subst_tm_ty (_) (_) (_) (up_subst_subst_vl_ty (_) (_) (_) Eqty)) (up_subst_subst_tm_tm (_) (_) (_) (_) (_) (up_subst_subst_vl_tm (_) (_) (_) (_) (_) Eqtm)) (up_subst_subst_tm_vl (_) (_) (_) (_) (_) (up_subst_subst_vl_vl (_) (_) (_) (_) (_) Eqvl))) s1)
    | tlam (_) (_) (_) s0 => congr_tlam ((compSubstSubst_tm (up_ty_ty sigmaty) (up_ty_tm sigmatm) (up_ty_vl sigmavl) (up_ty_ty tauty) (up_ty_tm tautm) (up_ty_vl tauvl) (up_ty_ty thetaty) (up_ty_tm thetatm) (up_ty_vl thetavl) (up_subst_subst_ty_ty (_) (_) (_) Eqty) (up_subst_subst_ty_tm (_) (_) (_) (_) (_) Eqtm) (up_subst_subst_ty_vl (_) (_) (_) (_) (_) Eqvl)) s0)
    end.

Definition rinstInst_up_ty_tm { m : nat } { nty ntm nvl : nat } (xi : (fin) (m) -> (fin) (ntm)) (sigma : (fin) (m) -> tm (nty) (ntm) (nvl)) (Eq : forall x, ((funcomp) (var_tm (nty) (ntm) (nvl)) xi) x = sigma x) : forall x, ((funcomp) (var_tm ((S) nty) (ntm) (nvl)) (upRen_ty_tm xi)) x = (up_ty_tm sigma) x :=
  fun n => (ap) (ren_tm (shift) (id) (id)) (Eq n).

Definition rinstInst_up_ty_vl { m : nat } { nty ntm nvl : nat } (xi : (fin) (m) -> (fin) (nvl)) (sigma : (fin) (m) -> vl (nty) (ntm) (nvl)) (Eq : forall x, ((funcomp) (var_vl (nty) (ntm) (nvl)) xi) x = sigma x) : forall x, ((funcomp) (var_vl ((S) nty) (ntm) (nvl)) (upRen_ty_vl xi)) x = (up_ty_vl sigma) x :=
  fun n => (ap) (ren_vl (shift) (id) (id)) (Eq n).

Definition rinstInst_up_tm_ty { m : nat } { nty : nat } (xi : (fin) (m) -> (fin) (nty)) (sigma : (fin) (m) -> ty (nty)) (Eq : forall x, ((funcomp) (var_ty (nty)) xi) x = sigma x) : forall x, ((funcomp) (var_ty (nty)) (upRen_tm_ty xi)) x = (up_tm_ty sigma) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition rinstInst_up_tm_tm { m : nat } { nty ntm nvl : nat } (xi : (fin) (m) -> (fin) (ntm)) (sigma : (fin) (m) -> tm (nty) (ntm) (nvl)) (Eq : forall x, ((funcomp) (var_tm (nty) (ntm) (nvl)) xi) x = sigma x) : forall x, ((funcomp) (var_tm (nty) ((S) ntm) (nvl)) (upRen_tm_tm xi)) x = (up_tm_tm sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (id) (shift) (id)) (Eq fin_n)
  | None  => eq_refl
  end.

Definition rinstInst_up_tm_vl { m : nat } { nty ntm nvl : nat } (xi : (fin) (m) -> (fin) (nvl)) (sigma : (fin) (m) -> vl (nty) (ntm) (nvl)) (Eq : forall x, ((funcomp) (var_vl (nty) (ntm) (nvl)) xi) x = sigma x) : forall x, ((funcomp) (var_vl (nty) ((S) ntm) (nvl)) (upRen_tm_vl xi)) x = (up_tm_vl sigma) x :=
  fun n => (ap) (ren_vl (id) (shift) (id)) (Eq n).

Definition rinstInst_up_vl_ty { m : nat } { nty : nat } (xi : (fin) (m) -> (fin) (nty)) (sigma : (fin) (m) -> ty (nty)) (Eq : forall x, ((funcomp) (var_ty (nty)) xi) x = sigma x) : forall x, ((funcomp) (var_ty (nty)) (upRen_vl_ty xi)) x = (up_vl_ty sigma) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition rinstInst_up_vl_tm { m : nat } { nty ntm nvl : nat } (xi : (fin) (m) -> (fin) (ntm)) (sigma : (fin) (m) -> tm (nty) (ntm) (nvl)) (Eq : forall x, ((funcomp) (var_tm (nty) (ntm) (nvl)) xi) x = sigma x) : forall x, ((funcomp) (var_tm (nty) (ntm) ((S) nvl)) (upRen_vl_tm xi)) x = (up_vl_tm sigma) x :=
  fun n => (ap) (ren_tm (id) (id) (shift)) (Eq n).

Definition rinstInst_up_vl_vl { m : nat } { nty ntm nvl : nat } (xi : (fin) (m) -> (fin) (nvl)) (sigma : (fin) (m) -> vl (nty) (ntm) (nvl)) (Eq : forall x, ((funcomp) (var_vl (nty) (ntm) (nvl)) xi) x = sigma x) : forall x, ((funcomp) (var_vl (nty) (ntm) ((S) nvl)) (upRen_vl_vl xi)) x = (up_vl_vl sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_vl (id) (id) (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint rinst_inst_tm { mty mtm mvl : nat } { nty ntm nvl : nat } (xity : (fin) (mty) -> (fin) (nty)) (xitm : (fin) (mtm) -> (fin) (ntm)) (xivl : (fin) (mvl) -> (fin) (nvl)) (sigmaty : (fin) (mty) -> ty (nty)) (sigmatm : (fin) (mtm) -> tm (nty) (ntm) (nvl)) (sigmavl : (fin) (mvl) -> vl (nty) (ntm) (nvl)) (Eqty : forall x, ((funcomp) (var_ty (nty)) xity) x = sigmaty x) (Eqtm : forall x, ((funcomp) (var_tm (nty) (ntm) (nvl)) xitm) x = sigmatm x) (Eqvl : forall x, ((funcomp) (var_vl (nty) (ntm) (nvl)) xivl) x = sigmavl x) (s : tm (mty) (mtm) (mvl)) : ren_tm xity xitm xivl s = subst_tm sigmaty sigmatm sigmavl s :=
    match s return ren_tm xity xitm xivl s = subst_tm sigmaty sigmatm sigmavl s with
    | var_tm (_) (_) (_) s => Eqtm s
    | app (_) (_) (_) s0 s1 => congr_app ((rinst_inst_tm xity xitm xivl sigmaty sigmatm sigmavl Eqty Eqtm Eqvl) s0) ((rinst_inst_tm xity xitm xivl sigmaty sigmatm sigmavl Eqty Eqtm Eqvl) s1)
    | tapp (_) (_) (_) s0 s1 => congr_tapp ((rinst_inst_tm xity xitm xivl sigmaty sigmatm sigmavl Eqty Eqtm Eqvl) s0) ((rinst_inst_ty xity sigmaty Eqty) s1)
    | vt (_) (_) (_) s0 => congr_vt ((rinst_inst_vl xity xitm xivl sigmaty sigmatm sigmavl Eqty Eqtm Eqvl) s0)
    end
 with rinst_inst_vl { mty mtm mvl : nat } { nty ntm nvl : nat } (xity : (fin) (mty) -> (fin) (nty)) (xitm : (fin) (mtm) -> (fin) (ntm)) (xivl : (fin) (mvl) -> (fin) (nvl)) (sigmaty : (fin) (mty) -> ty (nty)) (sigmatm : (fin) (mtm) -> tm (nty) (ntm) (nvl)) (sigmavl : (fin) (mvl) -> vl (nty) (ntm) (nvl)) (Eqty : forall x, ((funcomp) (var_ty (nty)) xity) x = sigmaty x) (Eqtm : forall x, ((funcomp) (var_tm (nty) (ntm) (nvl)) xitm) x = sigmatm x) (Eqvl : forall x, ((funcomp) (var_vl (nty) (ntm) (nvl)) xivl) x = sigmavl x) (s : vl (mty) (mtm) (mvl)) : ren_vl xity xitm xivl s = subst_vl sigmaty sigmatm sigmavl s :=
    match s return ren_vl xity xitm xivl s = subst_vl sigmaty sigmatm sigmavl s with
    | var_vl (_) (_) (_) s => Eqvl s
    | lam (_) (_) (_) s0 s1 => congr_lam ((rinst_inst_ty xity sigmaty Eqty) s0) ((rinst_inst_tm (upRen_tm_ty (upRen_vl_ty xity)) (upRen_tm_tm (upRen_vl_tm xitm)) (upRen_tm_vl (upRen_vl_vl xivl)) (up_tm_ty (up_vl_ty sigmaty)) (up_tm_tm (up_vl_tm sigmatm)) (up_tm_vl (up_vl_vl sigmavl)) (rinstInst_up_tm_ty (_) (_) (rinstInst_up_vl_ty (_) (_) Eqty)) (rinstInst_up_tm_tm (_) (_) (rinstInst_up_vl_tm (_) (_) Eqtm)) (rinstInst_up_tm_vl (_) (_) (rinstInst_up_vl_vl (_) (_) Eqvl))) s1)
    | tlam (_) (_) (_) s0 => congr_tlam ((rinst_inst_tm (upRen_ty_ty xity) (upRen_ty_tm xitm) (upRen_ty_vl xivl) (up_ty_ty sigmaty) (up_ty_tm sigmatm) (up_ty_vl sigmavl) (rinstInst_up_ty_ty (_) (_) Eqty) (rinstInst_up_ty_tm (_) (_) Eqtm) (rinstInst_up_ty_vl (_) (_) Eqvl)) s0)
    end.

Lemma rinstInst_tm { mty mtm mvl : nat } { nty ntm nvl : nat } (xity : (fin) (mty) -> (fin) (nty)) (xitm : (fin) (mtm) -> (fin) (ntm)) (xivl : (fin) (mvl) -> (fin) (nvl)) : ren_tm xity xitm xivl = subst_tm ((funcomp) (var_ty (nty)) xity) ((funcomp) (var_tm (nty) (ntm) (nvl)) xitm) ((funcomp) (var_vl (nty) (ntm) (nvl)) xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_tm xity xitm xivl (_) (_) (_) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_vl { mty mtm mvl : nat } { nty ntm nvl : nat } (xity : (fin) (mty) -> (fin) (nty)) (xitm : (fin) (mtm) -> (fin) (ntm)) (xivl : (fin) (mvl) -> (fin) (nvl)) : ren_vl xity xitm xivl = subst_vl ((funcomp) (var_ty (nty)) xity) ((funcomp) (var_tm (nty) (ntm) (nvl)) xitm) ((funcomp) (var_vl (nty) (ntm) (nvl)) xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_vl xity xitm xivl (_) (_) (_) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) x)). Qed.

Lemma instId_tm { mty mtm mvl : nat } : subst_tm (var_ty (mty)) (var_tm (mty) (mtm) (mvl)) (var_vl (mty) (mtm) (mvl)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_tm (var_ty (mty)) (var_tm (mty) (mtm) (mvl)) (var_vl (mty) (mtm) (mvl)) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) ((id) x))). Qed.

Lemma instId_vl { mty mtm mvl : nat } : subst_vl (var_ty (mty)) (var_tm (mty) (mtm) (mvl)) (var_vl (mty) (mtm) (mvl)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_vl (var_ty (mty)) (var_tm (mty) (mtm) (mvl)) (var_vl (mty) (mtm) (mvl)) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_tm { mty mtm mvl : nat } : @ren_tm (mty) (mtm) (mvl) (mty) (mtm) (mvl) (id) (id) (id) = id .
Proof. exact ((eq_trans) (rinstInst_tm ((id) (_)) ((id) (_)) ((id) (_))) instId_tm). Qed.

Lemma rinstId_vl { mty mtm mvl : nat } : @ren_vl (mty) (mtm) (mvl) (mty) (mtm) (mvl) (id) (id) (id) = id .
Proof. exact ((eq_trans) (rinstInst_vl ((id) (_)) ((id) (_)) ((id) (_))) instId_vl). Qed.

Lemma varL_tm { mty mtm mvl : nat } { nty ntm nvl : nat } (sigmaty : (fin) (mty) -> ty (nty)) (sigmatm : (fin) (mtm) -> tm (nty) (ntm) (nvl)) (sigmavl : (fin) (mvl) -> vl (nty) (ntm) (nvl)) : (funcomp) (subst_tm sigmaty sigmatm sigmavl) (var_tm (mty) (mtm) (mvl)) = sigmatm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varL_vl { mty mtm mvl : nat } { nty ntm nvl : nat } (sigmaty : (fin) (mty) -> ty (nty)) (sigmatm : (fin) (mtm) -> tm (nty) (ntm) (nvl)) (sigmavl : (fin) (mvl) -> vl (nty) (ntm) (nvl)) : (funcomp) (subst_vl sigmaty sigmatm sigmavl) (var_vl (mty) (mtm) (mvl)) = sigmavl .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_tm { mty mtm mvl : nat } { nty ntm nvl : nat } (xity : (fin) (mty) -> (fin) (nty)) (xitm : (fin) (mtm) -> (fin) (ntm)) (xivl : (fin) (mvl) -> (fin) (nvl)) : (funcomp) (ren_tm xity xitm xivl) (var_tm (mty) (mtm) (mvl)) = (funcomp) (var_tm (nty) (ntm) (nvl)) xitm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_vl { mty mtm mvl : nat } { nty ntm nvl : nat } (xity : (fin) (mty) -> (fin) (nty)) (xitm : (fin) (mtm) -> (fin) (ntm)) (xivl : (fin) (mvl) -> (fin) (nvl)) : (funcomp) (ren_vl xity xitm xivl) (var_vl (mty) (mtm) (mvl)) = (funcomp) (var_vl (nty) (ntm) (nvl)) xivl .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_tm { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigmaty : (fin) (mty) -> ty (kty)) (sigmatm : (fin) (mtm) -> tm (kty) (ktm) (kvl)) (sigmavl : (fin) (mvl) -> vl (kty) (ktm) (kvl)) (tauty : (fin) (kty) -> ty (lty)) (tautm : (fin) (ktm) -> tm (lty) (ltm) (lvl)) (tauvl : (fin) (kvl) -> vl (lty) (ltm) (lvl)) (s : tm (mty) (mtm) (mvl)) : subst_tm tauty tautm tauvl (subst_tm sigmaty sigmatm sigmavl s) = subst_tm ((funcomp) (subst_ty tauty) sigmaty) ((funcomp) (subst_tm tauty tautm tauvl) sigmatm) ((funcomp) (subst_vl tauty tautm tauvl) sigmavl) s .
Proof. exact (compSubstSubst_tm sigmaty sigmatm sigmavl tauty tautm tauvl (_) (_) (_) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compComp_vl { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigmaty : (fin) (mty) -> ty (kty)) (sigmatm : (fin) (mtm) -> tm (kty) (ktm) (kvl)) (sigmavl : (fin) (mvl) -> vl (kty) (ktm) (kvl)) (tauty : (fin) (kty) -> ty (lty)) (tautm : (fin) (ktm) -> tm (lty) (ltm) (lvl)) (tauvl : (fin) (kvl) -> vl (lty) (ltm) (lvl)) (s : vl (mty) (mtm) (mvl)) : subst_vl tauty tautm tauvl (subst_vl sigmaty sigmatm sigmavl s) = subst_vl ((funcomp) (subst_ty tauty) sigmaty) ((funcomp) (subst_tm tauty tautm tauvl) sigmatm) ((funcomp) (subst_vl tauty tautm tauvl) sigmavl) s .
Proof. exact (compSubstSubst_vl sigmaty sigmatm sigmavl tauty tautm tauvl (_) (_) (_) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compComp'_tm { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigmaty : (fin) (mty) -> ty (kty)) (sigmatm : (fin) (mtm) -> tm (kty) (ktm) (kvl)) (sigmavl : (fin) (mvl) -> vl (kty) (ktm) (kvl)) (tauty : (fin) (kty) -> ty (lty)) (tautm : (fin) (ktm) -> tm (lty) (ltm) (lvl)) (tauvl : (fin) (kvl) -> vl (lty) (ltm) (lvl)) : (funcomp) (subst_tm tauty tautm tauvl) (subst_tm sigmaty sigmatm sigmavl) = subst_tm ((funcomp) (subst_ty tauty) sigmaty) ((funcomp) (subst_tm tauty tautm tauvl) sigmatm) ((funcomp) (subst_vl tauty tautm tauvl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_tm sigmaty sigmatm sigmavl tauty tautm tauvl n)). Qed.

Lemma compComp'_vl { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigmaty : (fin) (mty) -> ty (kty)) (sigmatm : (fin) (mtm) -> tm (kty) (ktm) (kvl)) (sigmavl : (fin) (mvl) -> vl (kty) (ktm) (kvl)) (tauty : (fin) (kty) -> ty (lty)) (tautm : (fin) (ktm) -> tm (lty) (ltm) (lvl)) (tauvl : (fin) (kvl) -> vl (lty) (ltm) (lvl)) : (funcomp) (subst_vl tauty tautm tauvl) (subst_vl sigmaty sigmatm sigmavl) = subst_vl ((funcomp) (subst_ty tauty) sigmaty) ((funcomp) (subst_tm tauty tautm tauvl) sigmatm) ((funcomp) (subst_vl tauty tautm tauvl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_vl sigmaty sigmatm sigmavl tauty tautm tauvl n)). Qed.

Lemma compRen_tm { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigmaty : (fin) (mty) -> ty (kty)) (sigmatm : (fin) (mtm) -> tm (kty) (ktm) (kvl)) (sigmavl : (fin) (mvl) -> vl (kty) (ktm) (kvl)) (zetaty : (fin) (kty) -> (fin) (lty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : tm (mty) (mtm) (mvl)) : ren_tm zetaty zetatm zetavl (subst_tm sigmaty sigmatm sigmavl s) = subst_tm ((funcomp) (ren_ty zetaty) sigmaty) ((funcomp) (ren_tm zetaty zetatm zetavl) sigmatm) ((funcomp) (ren_vl zetaty zetatm zetavl) sigmavl) s .
Proof. exact (compSubstRen_tm sigmaty sigmatm sigmavl zetaty zetatm zetavl (_) (_) (_) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compRen_vl { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigmaty : (fin) (mty) -> ty (kty)) (sigmatm : (fin) (mtm) -> tm (kty) (ktm) (kvl)) (sigmavl : (fin) (mvl) -> vl (kty) (ktm) (kvl)) (zetaty : (fin) (kty) -> (fin) (lty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : vl (mty) (mtm) (mvl)) : ren_vl zetaty zetatm zetavl (subst_vl sigmaty sigmatm sigmavl s) = subst_vl ((funcomp) (ren_ty zetaty) sigmaty) ((funcomp) (ren_tm zetaty zetatm zetavl) sigmatm) ((funcomp) (ren_vl zetaty zetatm zetavl) sigmavl) s .
Proof. exact (compSubstRen_vl sigmaty sigmatm sigmavl zetaty zetatm zetavl (_) (_) (_) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compRen'_tm { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigmaty : (fin) (mty) -> ty (kty)) (sigmatm : (fin) (mtm) -> tm (kty) (ktm) (kvl)) (sigmavl : (fin) (mvl) -> vl (kty) (ktm) (kvl)) (zetaty : (fin) (kty) -> (fin) (lty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_tm zetaty zetatm zetavl) (subst_tm sigmaty sigmatm sigmavl) = subst_tm ((funcomp) (ren_ty zetaty) sigmaty) ((funcomp) (ren_tm zetaty zetatm zetavl) sigmatm) ((funcomp) (ren_vl zetaty zetatm zetavl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_tm sigmaty sigmatm sigmavl zetaty zetatm zetavl n)). Qed.

Lemma compRen'_vl { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (sigmaty : (fin) (mty) -> ty (kty)) (sigmatm : (fin) (mtm) -> tm (kty) (ktm) (kvl)) (sigmavl : (fin) (mvl) -> vl (kty) (ktm) (kvl)) (zetaty : (fin) (kty) -> (fin) (lty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_vl zetaty zetatm zetavl) (subst_vl sigmaty sigmatm sigmavl) = subst_vl ((funcomp) (ren_ty zetaty) sigmaty) ((funcomp) (ren_tm zetaty zetatm zetavl) sigmatm) ((funcomp) (ren_vl zetaty zetatm zetavl) sigmavl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_vl sigmaty sigmatm sigmavl zetaty zetatm zetavl n)). Qed.

Lemma renComp_tm { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (xity : (fin) (mty) -> (fin) (kty)) (xitm : (fin) (mtm) -> (fin) (ktm)) (xivl : (fin) (mvl) -> (fin) (kvl)) (tauty : (fin) (kty) -> ty (lty)) (tautm : (fin) (ktm) -> tm (lty) (ltm) (lvl)) (tauvl : (fin) (kvl) -> vl (lty) (ltm) (lvl)) (s : tm (mty) (mtm) (mvl)) : subst_tm tauty tautm tauvl (ren_tm xity xitm xivl s) = subst_tm ((funcomp) tauty xity) ((funcomp) tautm xitm) ((funcomp) tauvl xivl) s .
Proof. exact (compRenSubst_tm xity xitm xivl tauty tautm tauvl (_) (_) (_) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renComp_vl { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (xity : (fin) (mty) -> (fin) (kty)) (xitm : (fin) (mtm) -> (fin) (ktm)) (xivl : (fin) (mvl) -> (fin) (kvl)) (tauty : (fin) (kty) -> ty (lty)) (tautm : (fin) (ktm) -> tm (lty) (ltm) (lvl)) (tauvl : (fin) (kvl) -> vl (lty) (ltm) (lvl)) (s : vl (mty) (mtm) (mvl)) : subst_vl tauty tautm tauvl (ren_vl xity xitm xivl s) = subst_vl ((funcomp) tauty xity) ((funcomp) tautm xitm) ((funcomp) tauvl xivl) s .
Proof. exact (compRenSubst_vl xity xitm xivl tauty tautm tauvl (_) (_) (_) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renComp'_tm { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (xity : (fin) (mty) -> (fin) (kty)) (xitm : (fin) (mtm) -> (fin) (ktm)) (xivl : (fin) (mvl) -> (fin) (kvl)) (tauty : (fin) (kty) -> ty (lty)) (tautm : (fin) (ktm) -> tm (lty) (ltm) (lvl)) (tauvl : (fin) (kvl) -> vl (lty) (ltm) (lvl)) : (funcomp) (subst_tm tauty tautm tauvl) (ren_tm xity xitm xivl) = subst_tm ((funcomp) tauty xity) ((funcomp) tautm xitm) ((funcomp) tauvl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_tm xity xitm xivl tauty tautm tauvl n)). Qed.

Lemma renComp'_vl { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (xity : (fin) (mty) -> (fin) (kty)) (xitm : (fin) (mtm) -> (fin) (ktm)) (xivl : (fin) (mvl) -> (fin) (kvl)) (tauty : (fin) (kty) -> ty (lty)) (tautm : (fin) (ktm) -> tm (lty) (ltm) (lvl)) (tauvl : (fin) (kvl) -> vl (lty) (ltm) (lvl)) : (funcomp) (subst_vl tauty tautm tauvl) (ren_vl xity xitm xivl) = subst_vl ((funcomp) tauty xity) ((funcomp) tautm xitm) ((funcomp) tauvl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_vl xity xitm xivl tauty tautm tauvl n)). Qed.

Lemma renRen_tm { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (xity : (fin) (mty) -> (fin) (kty)) (xitm : (fin) (mtm) -> (fin) (ktm)) (xivl : (fin) (mvl) -> (fin) (kvl)) (zetaty : (fin) (kty) -> (fin) (lty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : tm (mty) (mtm) (mvl)) : ren_tm zetaty zetatm zetavl (ren_tm xity xitm xivl s) = ren_tm ((funcomp) zetaty xity) ((funcomp) zetatm xitm) ((funcomp) zetavl xivl) s .
Proof. exact (compRenRen_tm xity xitm xivl zetaty zetatm zetavl (_) (_) (_) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renRen_vl { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (xity : (fin) (mty) -> (fin) (kty)) (xitm : (fin) (mtm) -> (fin) (ktm)) (xivl : (fin) (mvl) -> (fin) (kvl)) (zetaty : (fin) (kty) -> (fin) (lty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetavl : (fin) (kvl) -> (fin) (lvl)) (s : vl (mty) (mtm) (mvl)) : ren_vl zetaty zetatm zetavl (ren_vl xity xitm xivl s) = ren_vl ((funcomp) zetaty xity) ((funcomp) zetatm xitm) ((funcomp) zetavl xivl) s .
Proof. exact (compRenRen_vl xity xitm xivl zetaty zetatm zetavl (_) (_) (_) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renRen'_tm { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (xity : (fin) (mty) -> (fin) (kty)) (xitm : (fin) (mtm) -> (fin) (ktm)) (xivl : (fin) (mvl) -> (fin) (kvl)) (zetaty : (fin) (kty) -> (fin) (lty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_tm zetaty zetatm zetavl) (ren_tm xity xitm xivl) = ren_tm ((funcomp) zetaty xity) ((funcomp) zetatm xitm) ((funcomp) zetavl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_tm xity xitm xivl zetaty zetatm zetavl n)). Qed.

Lemma renRen'_vl { kty ktm kvl : nat } { lty ltm lvl : nat } { mty mtm mvl : nat } (xity : (fin) (mty) -> (fin) (kty)) (xitm : (fin) (mtm) -> (fin) (ktm)) (xivl : (fin) (mvl) -> (fin) (kvl)) (zetaty : (fin) (kty) -> (fin) (lty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetavl : (fin) (kvl) -> (fin) (lvl)) : (funcomp) (ren_vl zetaty zetatm zetavl) (ren_vl xity xitm xivl) = ren_vl ((funcomp) zetaty xity) ((funcomp) zetatm xitm) ((funcomp) zetavl xivl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_vl xity xitm xivl zetaty zetatm zetavl n)). Qed.

End tmvl.

Arguments var_ty {nty}.

Arguments arr {nty}.

Arguments all {nty}.

Arguments var_tm {nty} {ntm} {nvl}.

Arguments app {nty} {ntm} {nvl}.

Arguments tapp {nty} {ntm} {nvl}.

Arguments vt {nty} {ntm} {nvl}.

Arguments var_vl {nty} {ntm} {nvl}.

Arguments lam {nty} {ntm} {nvl}.

Arguments tlam {nty} {ntm} {nvl}.

Global Instance Subst_ty { mty : nat } { nty : nat } : Subst1 ((fin) (mty) -> ty (nty)) (ty (mty)) (ty (nty)) := @subst_ty (mty) (nty) .

Global Instance Subst_tm { mty mtm mvl : nat } { nty ntm nvl : nat } : Subst3 ((fin) (mty) -> ty (nty)) ((fin) (mtm) -> tm (nty) (ntm) (nvl)) ((fin) (mvl) -> vl (nty) (ntm) (nvl)) (tm (mty) (mtm) (mvl)) (tm (nty) (ntm) (nvl)) := @subst_tm (mty) (mtm) (mvl) (nty) (ntm) (nvl) .

Global Instance Subst_vl { mty mtm mvl : nat } { nty ntm nvl : nat } : Subst3 ((fin) (mty) -> ty (nty)) ((fin) (mtm) -> tm (nty) (ntm) (nvl)) ((fin) (mvl) -> vl (nty) (ntm) (nvl)) (vl (mty) (mtm) (mvl)) (vl (nty) (ntm) (nvl)) := @subst_vl (mty) (mtm) (mvl) (nty) (ntm) (nvl) .

Global Instance Ren_ty { mty : nat } { nty : nat } : Ren1 ((fin) (mty) -> (fin) (nty)) (ty (mty)) (ty (nty)) := @ren_ty (mty) (nty) .

Global Instance Ren_tm { mty mtm mvl : nat } { nty ntm nvl : nat } : Ren3 ((fin) (mty) -> (fin) (nty)) ((fin) (mtm) -> (fin) (ntm)) ((fin) (mvl) -> (fin) (nvl)) (tm (mty) (mtm) (mvl)) (tm (nty) (ntm) (nvl)) := @ren_tm (mty) (mtm) (mvl) (nty) (ntm) (nvl) .

Global Instance Ren_vl { mty mtm mvl : nat } { nty ntm nvl : nat } : Ren3 ((fin) (mty) -> (fin) (nty)) ((fin) (mtm) -> (fin) (ntm)) ((fin) (mvl) -> (fin) (nvl)) (vl (mty) (mtm) (mvl)) (vl (nty) (ntm) (nvl)) := @ren_vl (mty) (mtm) (mvl) (nty) (ntm) (nvl) .

Global Instance VarInstance_ty { mty : nat } : Var ((fin) (mty)) (ty (mty)) := @var_ty (mty) .

Notation "x '__ty'" := (var_ty x) (at level 5, format "x __ty") : subst_scope.

Notation "x '__ty'" := (@ids (_) (_) VarInstance_ty x) (at level 5, only printing, format "x __ty") : subst_scope.

Notation "'var'" := (var_ty) (only printing, at level 1) : subst_scope.

Global Instance VarInstance_tm { mty mtm mvl : nat } : Var ((fin) (mtm)) (tm (mty) (mtm) (mvl)) := @var_tm (mty) (mtm) (mvl) .

Notation "x '__tm'" := (var_tm x) (at level 5, format "x __tm") : subst_scope.

Notation "x '__tm'" := (@ids (_) (_) VarInstance_tm x) (at level 5, only printing, format "x __tm") : subst_scope.

Notation "'var'" := (var_tm) (only printing, at level 1) : subst_scope.

Global Instance VarInstance_vl { mty mtm mvl : nat } : Var ((fin) (mvl)) (vl (mty) (mtm) (mvl)) := @var_vl (mty) (mtm) (mvl) .

Notation "x '__vl'" := (var_vl x) (at level 5, format "x __vl") : subst_scope.

Notation "x '__vl'" := (@ids (_) (_) VarInstance_vl x) (at level 5, only printing, format "x __vl") : subst_scope.

Notation "'var'" := (var_vl) (only printing, at level 1) : subst_scope.

Class Up_ty X Y := up_ty : X -> Y.

Notation "↑__ty" := (up_ty) (only printing) : subst_scope.

Class Up_tm X Y := up_tm : X -> Y.

Notation "↑__tm" := (up_tm) (only printing) : subst_scope.

Class Up_vl X Y := up_vl : X -> Y.

Notation "↑__vl" := (up_vl) (only printing) : subst_scope.

Notation "↑__ty" := (up_ty_ty) (only printing) : subst_scope.

Global Instance Up_ty_ty { m : nat } { nty : nat } : Up_ty (_) (_) := @up_ty_ty (m) (nty) .

Notation "↑__vl" := (up_vl_ty) (only printing) : subst_scope.

Global Instance Up_vl_ty { m : nat } { nty : nat } : Up_ty (_) (_) := @up_vl_ty (m) (nty) .

Notation "↑__vl" := (up_vl_tm) (only printing) : subst_scope.

Global Instance Up_vl_tm { m : nat } { nty ntm nvl : nat } : Up_tm (_) (_) := @up_vl_tm (m) (nty) (ntm) (nvl) .

Notation "↑__vl" := (up_vl_vl) (only printing) : subst_scope.

Global Instance Up_vl_vl { m : nat } { nty ntm nvl : nat } : Up_vl (_) (_) := @up_vl_vl (m) (nty) (ntm) (nvl) .

Notation "↑__tm" := (up_tm_ty) (only printing) : subst_scope.

Global Instance Up_tm_ty { m : nat } { nty : nat } : Up_ty (_) (_) := @up_tm_ty (m) (nty) .

Notation "↑__tm" := (up_tm_tm) (only printing) : subst_scope.

Global Instance Up_tm_tm { m : nat } { nty ntm nvl : nat } : Up_tm (_) (_) := @up_tm_tm (m) (nty) (ntm) (nvl) .

Notation "↑__tm" := (up_tm_vl) (only printing) : subst_scope.

Global Instance Up_tm_vl { m : nat } { nty ntm nvl : nat } : Up_vl (_) (_) := @up_tm_vl (m) (nty) (ntm) (nvl) .

Notation "↑__ty" := (up_ty_tm) (only printing) : subst_scope.

Global Instance Up_ty_tm { m : nat } { nty ntm nvl : nat } : Up_tm (_) (_) := @up_ty_tm (m) (nty) (ntm) (nvl) .

Notation "↑__ty" := (up_ty_vl) (only printing) : subst_scope.

Global Instance Up_ty_vl { m : nat } { nty ntm nvl : nat } : Up_vl (_) (_) := @up_ty_vl (m) (nty) (ntm) (nvl) .

Notation "s [ sigmaty ]" := (subst_ty sigmaty s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaty ]" := (subst_ty sigmaty) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xity ⟩" := (ren_ty xity s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xity ⟩" := (ren_ty xity) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaty ; sigmatm ; sigmavl ]" := (subst_tm sigmaty sigmatm sigmavl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaty ; sigmatm ; sigmavl ]" := (subst_tm sigmaty sigmatm sigmavl) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xity ; xitm ; xivl ⟩" := (ren_tm xity xitm xivl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xity ; xitm ; xivl ⟩" := (ren_tm xity xitm xivl) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaty ; sigmatm ; sigmavl ]" := (subst_vl sigmaty sigmatm sigmavl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaty ; sigmatm ; sigmavl ]" := (subst_vl sigmaty sigmatm sigmavl) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xity ; xitm ; xivl ⟩" := (ren_vl xity xitm xivl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xity ; xitm ; xivl ⟩" := (ren_vl xity xitm xivl) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_ty,  Subst_tm,  Subst_vl,  Ren_ty,  Ren_tm,  Ren_vl,  VarInstance_ty,  VarInstance_tm,  VarInstance_vl.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_ty,  Subst_tm,  Subst_vl,  Ren_ty,  Ren_tm,  Ren_vl,  VarInstance_ty,  VarInstance_tm,  VarInstance_vl in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_ty| progress rewrite ?compComp_ty| progress rewrite ?compComp'_ty| progress rewrite ?instId_tm| progress rewrite ?compComp_tm| progress rewrite ?compComp'_tm| progress rewrite ?instId_vl| progress rewrite ?compComp_vl| progress rewrite ?compComp'_vl| progress rewrite ?rinstId_ty| progress rewrite ?compRen_ty| progress rewrite ?compRen'_ty| progress rewrite ?renComp_ty| progress rewrite ?renComp'_ty| progress rewrite ?renRen_ty| progress rewrite ?renRen'_ty| progress rewrite ?rinstId_tm| progress rewrite ?compRen_tm| progress rewrite ?compRen'_tm| progress rewrite ?renComp_tm| progress rewrite ?renComp'_tm| progress rewrite ?renRen_tm| progress rewrite ?renRen'_tm| progress rewrite ?rinstId_vl| progress rewrite ?compRen_vl| progress rewrite ?compRen'_vl| progress rewrite ?renComp_vl| progress rewrite ?renComp'_vl| progress rewrite ?renRen_vl| progress rewrite ?renRen'_vl| progress rewrite ?varL_ty| progress rewrite ?varL_tm| progress rewrite ?varL_vl| progress rewrite ?varLRen_ty| progress rewrite ?varLRen_tm| progress rewrite ?varLRen_vl| progress (unfold up_ren, upRen_ty_ty, upRen_vl_ty, upRen_vl_tm, upRen_vl_vl, upRen_tm_ty, upRen_tm_tm, upRen_tm_vl, upRen_ty_tm, upRen_ty_vl, up_ty_ty, up_vl_ty, up_vl_tm, up_vl_vl, up_tm_ty, up_tm_tm, up_tm_vl, up_ty_tm, up_ty_vl)| progress (cbn [subst_ty subst_tm subst_vl ren_ty ren_tm ren_vl])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_ty in *| progress rewrite ?compComp_ty in *| progress rewrite ?compComp'_ty in *| progress rewrite ?instId_tm in *| progress rewrite ?compComp_tm in *| progress rewrite ?compComp'_tm in *| progress rewrite ?instId_vl in *| progress rewrite ?compComp_vl in *| progress rewrite ?compComp'_vl in *| progress rewrite ?rinstId_ty in *| progress rewrite ?compRen_ty in *| progress rewrite ?compRen'_ty in *| progress rewrite ?renComp_ty in *| progress rewrite ?renComp'_ty in *| progress rewrite ?renRen_ty in *| progress rewrite ?renRen'_ty in *| progress rewrite ?rinstId_tm in *| progress rewrite ?compRen_tm in *| progress rewrite ?compRen'_tm in *| progress rewrite ?renComp_tm in *| progress rewrite ?renComp'_tm in *| progress rewrite ?renRen_tm in *| progress rewrite ?renRen'_tm in *| progress rewrite ?rinstId_vl in *| progress rewrite ?compRen_vl in *| progress rewrite ?compRen'_vl in *| progress rewrite ?renComp_vl in *| progress rewrite ?renComp'_vl in *| progress rewrite ?renRen_vl in *| progress rewrite ?renRen'_vl in *| progress rewrite ?varL_ty in *| progress rewrite ?varL_tm in *| progress rewrite ?varL_vl in *| progress rewrite ?varLRen_ty in *| progress rewrite ?varLRen_tm in *| progress rewrite ?varLRen_vl in *| progress (unfold up_ren, upRen_ty_ty, upRen_vl_ty, upRen_vl_tm, upRen_vl_vl, upRen_tm_ty, upRen_tm_tm, upRen_tm_vl, upRen_ty_tm, upRen_ty_vl, up_ty_ty, up_vl_ty, up_vl_tm, up_vl_vl, up_tm_ty, up_tm_tm, up_tm_vl, up_ty_tm, up_ty_vl in *)| progress (cbn [subst_ty subst_tm subst_vl ren_ty ren_tm ren_vl] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_ty); try repeat (erewrite rinstInst_tm); try repeat (erewrite rinstInst_vl).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_ty); try repeat (erewrite <- rinstInst_tm); try repeat (erewrite <- rinstInst_vl).

(** as_apply follows **)

Ltac  musigma gexp hexp :=
  match   gexp  with
  |  ?s  =>  unify   (gexp) (hexp)
  |  arr (subst_ty ?sigma0 ?s0) (subst_ty ?sigma0 ?s1)  =>  first [ unify   (subst_ty sigma0 (arr s0 s1)) (hexp)|  musigma   (subst_ty sigma0 (arr s0 s1)) (hexp) ]
  |  all (subst_ty ((scons) (var_ty (var_zero)) ((funcomp) (ren_ty (shift)) ?sigma0)) ?s0)  =>  first [ unify   (subst_ty sigma0 (all s0)) (hexp)|  musigma   (subst_ty sigma0 (all s0)) (hexp) ]
  |  arr (ren_ty ?sigma0 ?s0) (ren_ty ?sigma0 ?s1)  =>  first [ unify   (ren_ty sigma0 (arr s0 s1)) (hexp)|  musigma   (ren_ty sigma0 (arr s0 s1)) (hexp) ]
  |  all (ren_ty ((scons) (var_zero) ((funcomp) (shift) ?sigma0)) ?s0)  =>  first [ unify   (ren_ty sigma0 (all s0)) (hexp)|  musigma   (ren_ty sigma0 (all s0)) (hexp) ]
  |  app (subst_tm ?sigma2 ?sigma1 ?sigma0 ?s0) (subst_tm ?sigma2 ?sigma1 ?sigma0 ?s1)  =>  first [ unify   (subst_tm sigma0 sigma1 sigma2 (app s0 s1)) (hexp)|  musigma   (subst_tm sigma0 sigma1 sigma2 (app s0 s1)) (hexp) ]
  |  tapp (subst_tm ?sigma2 ?sigma1 ?sigma0 ?s0) (subst_ty ?sigma0 ?s1)  =>  first [ unify   (subst_tm sigma0 sigma1 sigma2 (tapp s0 s1)) (hexp)|  musigma   (subst_tm sigma0 sigma1 sigma2 (tapp s0 s1)) (hexp) ]
  |  vt (subst_vl ?sigma2 ?sigma1 ?sigma0 ?s0)  =>  first [ unify   (subst_tm sigma0 sigma1 sigma2 (vt s0)) (hexp)|  musigma   (subst_tm sigma0 sigma1 sigma2 (vt s0)) (hexp) ]
  |  app (ren_tm ?sigma2 ?sigma1 ?sigma0 ?s0) (ren_tm ?sigma2 ?sigma1 ?sigma0 ?s1)  =>  first [ unify   (ren_tm sigma0 sigma1 sigma2 (app s0 s1)) (hexp)|  musigma   (ren_tm sigma0 sigma1 sigma2 (app s0 s1)) (hexp) ]
  |  tapp (ren_tm ?sigma2 ?sigma1 ?sigma0 ?s0) (ren_ty ?sigma0 ?s1)  =>  first [ unify   (ren_tm sigma0 sigma1 sigma2 (tapp s0 s1)) (hexp)|  musigma   (ren_tm sigma0 sigma1 sigma2 (tapp s0 s1)) (hexp) ]
  |  vt (ren_vl ?sigma2 ?sigma1 ?sigma0 ?s0)  =>  first [ unify   (ren_tm sigma0 sigma1 sigma2 (vt s0)) (hexp)|  musigma   (ren_tm sigma0 sigma1 sigma2 (vt s0)) (hexp) ]
  |  lam (subst_ty ?sigma0 ?s0) (subst_tm ((scons) (var_vl (var_zero)) ((funcomp) (ren_vl (id) (shift) (shift)) ?sigma2)) ((scons) (var_tm (var_zero)) ((funcomp) (ren_tm (id) (shift) (shift)) ?sigma1)) ?sigma0 ?s1)  =>  first [ unify   (subst_vl sigma0 sigma1 sigma2 (lam s0 s1)) (hexp)|  musigma   (subst_vl sigma0 sigma1 sigma2 (lam s0 s1)) (hexp) ]
  |  tlam (subst_tm ((funcomp) (ren_vl (shift) (id) (id)) ?sigma2) ((funcomp) (ren_tm (shift) (id) (id)) ?sigma1) ((scons) (var_ty (var_zero)) ((funcomp) (ren_ty (shift)) ?sigma0)) ?s0)  =>  first [ unify   (subst_vl sigma0 sigma1 sigma2 (tlam s0)) (hexp)|  musigma   (subst_vl sigma0 sigma1 sigma2 (tlam s0)) (hexp) ]
  |  lam (ren_ty ?sigma0 ?s0) (ren_tm ((scons) (var_zero) ((funcomp) (shift) ?sigma2)) ((scons) (var_zero) ((funcomp) (shift) ?sigma1)) ?sigma0 ?s1)  =>  first [ unify   (ren_vl sigma0 sigma1 sigma2 (lam s0 s1)) (hexp)|  musigma   (ren_vl sigma0 sigma1 sigma2 (lam s0 s1)) (hexp) ]
  |  tlam (ren_tm ?sigma2 ?sigma1 ((scons) (var_zero) ((funcomp) (shift) ?sigma0)) ?s0)  =>  first [ unify   (ren_vl sigma0 sigma1 sigma2 (tlam s0)) (hexp)|  musigma   (ren_vl sigma0 sigma1 sigma2 (tlam s0)) (hexp) ]
  |  ren_ty ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  ren_ty ?theta0 ?t  =>  first [ unify   (ren_ty tau0 (ren_ty sigma0 s)) (hexp)|  musigma   (ren_ty tau0 (ren_ty sigma0 s)) (hexp) ]
  end
  |  subst_ty ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  subst_ty ?theta0 ?t  =>  first [ unify   (subst_ty tau0 (ren_ty sigma0 s)) (hexp)|  musigma   (subst_ty tau0 (ren_ty sigma0 s)) (hexp) ]
  end
  |  subst_ty ((funcomp) (ren_ty ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  ren_ty ?theta0 ?t  =>  first [ unify   (ren_ty tau0 (subst_ty sigma0 s)) (hexp)|  musigma   (ren_ty tau0 (subst_ty sigma0 s)) (hexp) ]
  end
  |  subst_ty ((funcomp) (subst_ty ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  subst_ty ?theta0 ?t  =>  first [ unify   (subst_ty tau0 (subst_ty sigma0 s)) (hexp)|  musigma   (subst_ty tau0 (subst_ty sigma0 s)) (hexp) ]
  end
  |  ren_tm ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1) ((funcomp) ?tau2 ?sigma2) ?s  =>  match   hexp  with
  |  ren_tm ?theta0 ?theta1 ?theta2 ?t  =>  first [ unify   (ren_tm tau0 tau1 tau2 (ren_tm sigma0 sigma1 sigma2 s)) (hexp)|  musigma   (ren_tm tau0 tau1 tau2 (ren_tm sigma0 sigma1 sigma2 s)) (hexp) ]
  end
  |  subst_tm ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1) ((funcomp) ?tau2 ?sigma2) ?s  =>  match   hexp  with
  |  subst_tm ?theta0 ?theta1 ?theta2 ?t  =>  first [ unify   (subst_tm tau0 tau1 tau2 (ren_tm sigma0 sigma1 sigma2 s)) (hexp)|  musigma   (subst_tm tau0 tau1 tau2 (ren_tm sigma0 sigma1 sigma2 s)) (hexp) ]
  end
  |  subst_tm ((funcomp) (ren_ty ?tau0) ?sigma0) ((funcomp) (ren_tm ?tau0 ?tau1 ?tau2) ?sigma1) ((funcomp) (ren_vl ?tau0 ?tau1 ?tau2) ?sigma2) ?s  =>  match   hexp  with
  |  ren_tm ?theta0 ?theta1 ?theta2 ?t  =>  first [ unify   (ren_tm tau0 tau1 tau2 (subst_tm sigma0 sigma1 sigma2 s)) (hexp)|  musigma   (ren_tm tau0 tau1 tau2 (subst_tm sigma0 sigma1 sigma2 s)) (hexp) ]
  end
  |  subst_tm ((funcomp) (subst_ty ?tau0) ?sigma0) ((funcomp) (subst_tm ?tau0 ?tau1 ?tau2) ?sigma1) ((funcomp) (subst_vl ?tau0 ?tau1 ?tau2) ?sigma2) ?s  =>  match   hexp  with
  |  subst_tm ?theta0 ?theta1 ?theta2 ?t  =>  first [ unify   (subst_tm tau0 tau1 tau2 (subst_tm sigma0 sigma1 sigma2 s)) (hexp)|  musigma   (subst_tm tau0 tau1 tau2 (subst_tm sigma0 sigma1 sigma2 s)) (hexp) ]
  end
  |  ren_vl ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1) ((funcomp) ?tau2 ?sigma2) ?s  =>  match   hexp  with
  |  ren_vl ?theta0 ?theta1 ?theta2 ?t  =>  first [ unify   (ren_vl tau0 tau1 tau2 (ren_vl sigma0 sigma1 sigma2 s)) (hexp)|  musigma   (ren_vl tau0 tau1 tau2 (ren_vl sigma0 sigma1 sigma2 s)) (hexp) ]
  end
  |  subst_vl ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1) ((funcomp) ?tau2 ?sigma2) ?s  =>  match   hexp  with
  |  subst_vl ?theta0 ?theta1 ?theta2 ?t  =>  first [ unify   (subst_vl tau0 tau1 tau2 (ren_vl sigma0 sigma1 sigma2 s)) (hexp)|  musigma   (subst_vl tau0 tau1 tau2 (ren_vl sigma0 sigma1 sigma2 s)) (hexp) ]
  end
  |  subst_vl ((funcomp) (ren_ty ?tau0) ?sigma0) ((funcomp) (ren_tm ?tau0 ?tau1 ?tau2) ?sigma1) ((funcomp) (ren_vl ?tau0 ?tau1 ?tau2) ?sigma2) ?s  =>  match   hexp  with
  |  ren_vl ?theta0 ?theta1 ?theta2 ?t  =>  first [ unify   (ren_vl tau0 tau1 tau2 (subst_vl sigma0 sigma1 sigma2 s)) (hexp)|  musigma   (ren_vl tau0 tau1 tau2 (subst_vl sigma0 sigma1 sigma2 s)) (hexp) ]
  end
  |  subst_vl ((funcomp) (subst_ty ?tau0) ?sigma0) ((funcomp) (subst_tm ?tau0 ?tau1 ?tau2) ?sigma1) ((funcomp) (subst_vl ?tau0 ?tau1 ?tau2) ?sigma2) ?s  =>  match   hexp  with
  |  subst_vl ?theta0 ?theta1 ?theta2 ?t  =>  first [ unify   (subst_vl tau0 tau1 tau2 (subst_vl sigma0 sigma1 sigma2 s)) (hexp)|  musigma   (subst_vl tau0 tau1 tau2 (subst_vl sigma0 sigma1 sigma2 s)) (hexp) ]
  end
  |  (funcomp) (ren_ty ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_ty ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_ty tau0) ((funcomp) (ren_ty sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (ren_ty tau0) ((funcomp) (ren_ty sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_ty ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_ty ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_ty tau0) ((funcomp) (ren_ty sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (subst_ty tau0) ((funcomp) (ren_ty sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_ty ((funcomp) (ren_ty ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_ty ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_ty tau0) ((funcomp) (subst_ty sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (ren_ty tau0) ((funcomp) (subst_ty sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_ty ((funcomp) (subst_ty ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_ty ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_ty tau0) ((funcomp) (subst_ty sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (subst_ty tau0) ((funcomp) (subst_ty sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (ren_tm ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1) ((funcomp) ?tau2 ?sigma2)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_tm ?theta0 ?theta1 ?theta2) ?sigmat  =>  first [ unify   ((funcomp) (ren_tm tau0 tau1 tau2) ((funcomp) (ren_tm sigma0 sigma1 sigma2) sigmas)) (hexp)|  musigma   ((funcomp) (ren_tm tau0 tau1 tau2) ((funcomp) (ren_tm sigma0 sigma1 sigma2) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_tm ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1) ((funcomp) ?tau2 ?sigma2)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_tm ?theta0 ?theta1 ?theta2) ?sigmat  =>  first [ unify   ((funcomp) (subst_tm tau0 tau1 tau2) ((funcomp) (ren_tm sigma0 sigma1 sigma2) sigmas)) (hexp)|  musigma   ((funcomp) (subst_tm tau0 tau1 tau2) ((funcomp) (ren_tm sigma0 sigma1 sigma2) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_tm ((funcomp) (ren_ty ?tau0) ?sigma0) ((funcomp) (ren_tm ?tau0 ?tau1 ?tau2) ?sigma1) ((funcomp) (ren_vl ?tau0 ?tau1 ?tau2) ?sigma2)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_tm ?theta0 ?theta1 ?theta2) ?sigmat  =>  first [ unify   ((funcomp) (ren_tm tau0 tau1 tau2) ((funcomp) (subst_tm sigma0 sigma1 sigma2) sigmas)) (hexp)|  musigma   ((funcomp) (ren_tm tau0 tau1 tau2) ((funcomp) (subst_tm sigma0 sigma1 sigma2) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_tm ((funcomp) (subst_ty ?tau0) ?sigma0) ((funcomp) (subst_tm ?tau0 ?tau1 ?tau2) ?sigma1) ((funcomp) (subst_vl ?tau0 ?tau1 ?tau2) ?sigma2)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_tm ?theta0 ?theta1 ?theta2) ?sigmat  =>  first [ unify   ((funcomp) (subst_tm tau0 tau1 tau2) ((funcomp) (subst_tm sigma0 sigma1 sigma2) sigmas)) (hexp)|  musigma   ((funcomp) (subst_tm tau0 tau1 tau2) ((funcomp) (subst_tm sigma0 sigma1 sigma2) sigmas)) (hexp) ]
  end
  |  (funcomp) (ren_vl ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1) ((funcomp) ?tau2 ?sigma2)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_vl ?theta0 ?theta1 ?theta2) ?sigmat  =>  first [ unify   ((funcomp) (ren_vl tau0 tau1 tau2) ((funcomp) (ren_vl sigma0 sigma1 sigma2) sigmas)) (hexp)|  musigma   ((funcomp) (ren_vl tau0 tau1 tau2) ((funcomp) (ren_vl sigma0 sigma1 sigma2) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_vl ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1) ((funcomp) ?tau2 ?sigma2)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_vl ?theta0 ?theta1 ?theta2) ?sigmat  =>  first [ unify   ((funcomp) (subst_vl tau0 tau1 tau2) ((funcomp) (ren_vl sigma0 sigma1 sigma2) sigmas)) (hexp)|  musigma   ((funcomp) (subst_vl tau0 tau1 tau2) ((funcomp) (ren_vl sigma0 sigma1 sigma2) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_vl ((funcomp) (ren_ty ?tau0) ?sigma0) ((funcomp) (ren_tm ?tau0 ?tau1 ?tau2) ?sigma1) ((funcomp) (ren_vl ?tau0 ?tau1 ?tau2) ?sigma2)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_vl ?theta0 ?theta1 ?theta2) ?sigmat  =>  first [ unify   ((funcomp) (ren_vl tau0 tau1 tau2) ((funcomp) (subst_vl sigma0 sigma1 sigma2) sigmas)) (hexp)|  musigma   ((funcomp) (ren_vl tau0 tau1 tau2) ((funcomp) (subst_vl sigma0 sigma1 sigma2) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_vl ((funcomp) (subst_ty ?tau0) ?sigma0) ((funcomp) (subst_tm ?tau0 ?tau1 ?tau2) ?sigma1) ((funcomp) (subst_vl ?tau0 ?tau1 ?tau2) ?sigma2)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_vl ?theta0 ?theta1 ?theta2) ?sigmat  =>  first [ unify   ((funcomp) (subst_vl tau0 tau1 tau2) ((funcomp) (subst_vl sigma0 sigma1 sigma2) sigmas)) (hexp)|  musigma   ((funcomp) (subst_vl tau0 tau1 tau2) ((funcomp) (subst_vl sigma0 sigma1 sigma2) sigmas)) (hexp) ]
  end
  |  (scons) (ren_ty ?sigma0 ?s) ((funcomp) (ren_ty ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (ren_ty ?tau0) ?thetah  =>  first [ unify   ((funcomp) (ren_ty sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (ren_ty sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (subst_ty ?sigma0 ?s) ((funcomp) (subst_ty ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (subst_ty ?tau0) ?thetah  =>  first [ unify   ((funcomp) (subst_ty sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (subst_ty sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (ren_tm ?sigma0 ?sigma1 ?sigma2 ?s) ((funcomp) (ren_tm ?sigma0 ?sigma1 ?sigma2) ?thetag)  =>  match   hexp  with
  |  (funcomp) (ren_tm ?tau0 ?tau1 ?tau2) ?thetah  =>  first [ unify   ((funcomp) (ren_tm sigma0 sigma1 sigma2) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (ren_tm sigma0 sigma1 sigma2) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (subst_tm ?sigma0 ?sigma1 ?sigma2 ?s) ((funcomp) (subst_tm ?sigma0 ?sigma1 ?sigma2) ?thetag)  =>  match   hexp  with
  |  (funcomp) (subst_tm ?tau0 ?tau1 ?tau2) ?thetah  =>  first [ unify   ((funcomp) (subst_tm sigma0 sigma1 sigma2) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (subst_tm sigma0 sigma1 sigma2) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (ren_vl ?sigma0 ?sigma1 ?sigma2 ?s) ((funcomp) (ren_vl ?sigma0 ?sigma1 ?sigma2) ?thetag)  =>  match   hexp  with
  |  (funcomp) (ren_vl ?tau0 ?tau1 ?tau2) ?thetah  =>  first [ unify   ((funcomp) (ren_vl sigma0 sigma1 sigma2) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (ren_vl sigma0 sigma1 sigma2) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (subst_vl ?sigma0 ?sigma1 ?sigma2 ?s) ((funcomp) (subst_vl ?sigma0 ?sigma1 ?sigma2) ?thetag)  =>  match   hexp  with
  |  (funcomp) (subst_vl ?tau0 ?tau1 ?tau2) ?thetah  =>  first [ unify   ((funcomp) (subst_vl sigma0 sigma1 sigma2) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (subst_vl sigma0 sigma1 sigma2) ((scons) s thetag)) (hexp) ]
  end
  |  arr ?s0 ?s1  =>  match   hexp  with
  |  arr ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  all ?s0  =>  match   hexp  with
  |  all ?t0  =>  musigma   (s0) (t0)
  end
  |  subst_ty ?sigma0 ?s  =>  match   hexp  with
  |  subst_ty ?tau0 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0)
  end
  |  ren_ty ?sigma0 ?s  =>  match   hexp  with
  |  ren_ty ?tau0 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0)
  end
  |  (funcomp) (subst_ty ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_ty ?tau0) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0)
  end
  |  (funcomp) (ren_ty ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_ty ?tau0) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0)
  end
  |  app ?s0 ?s1  =>  match   hexp  with
  |  app ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  tapp ?s0 ?s1  =>  match   hexp  with
  |  tapp ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  vt ?s0  =>  match   hexp  with
  |  vt ?t0  =>  musigma   (s0) (t0)
  end
  |  subst_tm ?sigma0 ?sigma1 ?sigma2 ?s  =>  match   hexp  with
  |  subst_tm ?tau0 ?tau1 ?tau2 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1); musigma   (sigma2) (tau2)
  end
  |  ren_tm ?sigma0 ?sigma1 ?sigma2 ?s  =>  match   hexp  with
  |  ren_tm ?tau0 ?tau1 ?tau2 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1); musigma   (sigma2) (tau2)
  end
  |  (funcomp) (subst_tm ?sigma0 ?sigma1 ?sigma2) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_tm ?tau0 ?tau1 ?tau2) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1); musigma   (sigma2) (tau2)
  end
  |  (funcomp) (ren_tm ?sigma0 ?sigma1 ?sigma2) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_tm ?tau0 ?tau1 ?tau2) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1); musigma   (sigma2) (tau2)
  end
  |  lam ?s0 ?s1  =>  match   hexp  with
  |  lam ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  tlam ?s0  =>  match   hexp  with
  |  tlam ?t0  =>  musigma   (s0) (t0)
  end
  |  subst_vl ?sigma0 ?sigma1 ?sigma2 ?s  =>  match   hexp  with
  |  subst_vl ?tau0 ?tau1 ?tau2 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1); musigma   (sigma2) (tau2)
  end
  |  ren_vl ?sigma0 ?sigma1 ?sigma2 ?s  =>  match   hexp  with
  |  ren_vl ?tau0 ?tau1 ?tau2 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1); musigma   (sigma2) (tau2)
  end
  |  (funcomp) (subst_vl ?sigma0 ?sigma1 ?sigma2) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_vl ?tau0 ?tau1 ?tau2) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1); musigma   (sigma2) (tau2)
  end
  |  (funcomp) (ren_vl ?sigma0 ?sigma1 ?sigma2) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_vl ?tau0 ?tau1 ?tau2) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1); musigma   (sigma2) (tau2)
  end
  end.

Ltac  heuristics gexp hexp :=
  match   gexp  with
  |  ?s  =>  unify   (gexp) (hexp)
  |  (funcomp) (subst_ty ((funcomp) var_ty ?sigma0)) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_ty ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (subst_ty ((funcomp) var_ty sigma0)) sigma = (funcomp) (ren_ty sigma0) sigma) as eq by (renamify; reflexivity); rewrite   (eq); unify   ((funcomp) (ren_ty sigma0) sigma) (hexp); clear eq
  end
  |  subst_ty ((funcomp) var_ty ?sigma0) ?s  =>  match   hexp  with
  |  ren_ty ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (subst_ty ((funcomp) var_ty sigma0) s = ren_ty sigma0 s) as eq by (renamify; reflexivity); rewrite   (eq); unify   (ren_ty sigma0 s) (hexp); clear eq
  end
  |  (funcomp) (subst_tm ((funcomp) var_ty ?sigma0) ((funcomp) var_tm ?sigma1) ((funcomp) var_vl ?sigma2)) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_tm ?tau0 ?tau1 ?tau2) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (subst_tm ((funcomp) var_ty sigma0) ((funcomp) var_tm sigma1) ((funcomp) var_vl sigma2)) sigma = (funcomp) (ren_tm sigma0 sigma1 sigma2) sigma) as eq by (renamify; reflexivity); rewrite   (eq); unify   ((funcomp) (ren_tm sigma0 sigma1 sigma2) sigma) (hexp); clear eq
  end
  |  subst_tm ((funcomp) var_ty ?sigma0) ((funcomp) var_tm ?sigma1) ((funcomp) var_vl ?sigma2) ?s  =>  match   hexp  with
  |  ren_tm ?tau0 ?tau1 ?tau2 ?t  =>  let eq := fresh "eq" in
  assert (subst_tm ((funcomp) var_ty sigma0) ((funcomp) var_tm sigma1) ((funcomp) var_vl sigma2) s = ren_tm sigma0 sigma1 sigma2 s) as eq by (renamify; reflexivity); rewrite   (eq); unify   (ren_tm sigma0 sigma1 sigma2 s) (hexp); clear eq
  end
  |  (funcomp) (subst_vl ((funcomp) var_ty ?sigma0) ((funcomp) var_tm ?sigma1) ((funcomp) var_vl ?sigma2)) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_vl ?tau0 ?tau1 ?tau2) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (subst_vl ((funcomp) var_ty sigma0) ((funcomp) var_tm sigma1) ((funcomp) var_vl sigma2)) sigma = (funcomp) (ren_vl sigma0 sigma1 sigma2) sigma) as eq by (renamify; reflexivity); rewrite   (eq); unify   ((funcomp) (ren_vl sigma0 sigma1 sigma2) sigma) (hexp); clear eq
  end
  |  subst_vl ((funcomp) var_ty ?sigma0) ((funcomp) var_tm ?sigma1) ((funcomp) var_vl ?sigma2) ?s  =>  match   hexp  with
  |  ren_vl ?tau0 ?tau1 ?tau2 ?t  =>  let eq := fresh "eq" in
  assert (subst_vl ((funcomp) var_ty sigma0) ((funcomp) var_tm sigma1) ((funcomp) var_vl sigma2) s = ren_vl sigma0 sigma1 sigma2 s) as eq by (renamify; reflexivity); rewrite   (eq); unify   (ren_vl sigma0 sigma1 sigma2 s) (hexp); clear eq
  end
  |  (funcomp) (ren_ty ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_ty ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_ty sigma0) sigma = (funcomp) (subst_ty ((funcomp) var_ty sigma0)) sigma) as eq by (substify; reflexivity); rewrite   (eq); unify   ((funcomp) (subst_ty ((funcomp) var_ty sigma0)) sigma) (hexp); clear eq
  end
  |  ren_ty ?sigma0 ?s  =>  match   hexp  with
  |  subst_ty ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (ren_ty sigma0 s = subst_ty ((funcomp) var_ty sigma0) s) as eq by (substify; reflexivity); rewrite   (eq); unify   (subst_ty ((funcomp) var_ty sigma0) s) (hexp); clear eq
  end
  |  (funcomp) (ren_tm ?sigma0 ?sigma1 ?sigma2) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_tm ?tau0 ?tau1 ?tau2) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_tm sigma0 sigma1 sigma2) sigma = (funcomp) (subst_tm ((funcomp) var_ty sigma0) ((funcomp) var_tm sigma1) ((funcomp) var_vl sigma2)) sigma) as eq by (substify; reflexivity); rewrite   (eq); unify   ((funcomp) (subst_tm ((funcomp) var_ty sigma0) ((funcomp) var_tm sigma1) ((funcomp) var_vl sigma2)) sigma) (hexp); clear eq
  end
  |  ren_tm ?sigma0 ?sigma1 ?sigma2 ?s  =>  match   hexp  with
  |  subst_tm ?tau0 ?tau1 ?tau2 ?t  =>  let eq := fresh "eq" in
  assert (ren_tm sigma0 sigma1 sigma2 s = subst_tm ((funcomp) var_ty sigma0) ((funcomp) var_tm sigma1) ((funcomp) var_vl sigma2) s) as eq by (substify; reflexivity); rewrite   (eq); unify   (subst_tm ((funcomp) var_ty sigma0) ((funcomp) var_tm sigma1) ((funcomp) var_vl sigma2) s) (hexp); clear eq
  end
  |  (funcomp) (ren_vl ?sigma0 ?sigma1 ?sigma2) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_vl ?tau0 ?tau1 ?tau2) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_vl sigma0 sigma1 sigma2) sigma = (funcomp) (subst_vl ((funcomp) var_ty sigma0) ((funcomp) var_tm sigma1) ((funcomp) var_vl sigma2)) sigma) as eq by (substify; reflexivity); rewrite   (eq); unify   ((funcomp) (subst_vl ((funcomp) var_ty sigma0) ((funcomp) var_tm sigma1) ((funcomp) var_vl sigma2)) sigma) (hexp); clear eq
  end
  |  ren_vl ?sigma0 ?sigma1 ?sigma2 ?s  =>  match   hexp  with
  |  subst_vl ?tau0 ?tau1 ?tau2 ?t  =>  let eq := fresh "eq" in
  assert (ren_vl sigma0 sigma1 sigma2 s = subst_vl ((funcomp) var_ty sigma0) ((funcomp) var_tm sigma1) ((funcomp) var_vl sigma2) s) as eq by (substify; reflexivity); rewrite   (eq); unify   (subst_vl ((funcomp) var_ty sigma0) ((funcomp) var_tm sigma1) ((funcomp) var_vl sigma2) s) (hexp); clear eq
  end
  |  ?s  =>  musigma   (gexp) (hexp)
  |  subst_ty ((scons) ?sty0 ((funcomp) var_ty ?sigmaty)) ?sty  =>  match   hexp  with
  |  subst_ty ((scons) ?tty0 var_ty) ?tty  =>  unify   (subst_ty ((scons) sty0 var_ty) (ren_ty ((scons) (var_zero) ((funcomp) (shift) sigmaty)) sty)) (hexp)
  end
  |  subst_ty ((scons) ?sty0 ?sigmaty) ?sty  =>  match   hexp  with
  |  subst_ty ((scons) ?tty0 var_ty) ?tty  =>  unify   (subst_ty ((scons) sty0 var_ty) (subst_ty ((scons) (var_ty (var_zero)) ((funcomp) (ren_ty (shift)) sigmaty)) sty)) (hexp)
  end
  |  subst_tm ((funcomp) var_ty ?sigmaty) ((scons) ?stm0 ((funcomp) var_tm ?sigmatm)) ((scons) ?svl0 ((funcomp) var_vl ?sigmavl)) ?stm  =>  match   hexp  with
  |  subst_tm var_ty ((scons) ?ttm0 var_tm) ((scons) ?tvl0 var_vl) ?ttm  =>  unify   (subst_tm var_ty ((scons) stm0 var_tm) ((scons) svl0 var_vl) (ren_tm sigmaty ((scons) (var_zero) ((funcomp) (shift) sigmatm)) ((scons) (var_zero) ((funcomp) (shift) sigmavl)) stm)) (hexp)
  end
  |  subst_tm ((scons) ?sty0 ((funcomp) var_ty ?sigmaty)) ((funcomp) var_tm ?sigmatm) ((funcomp) var_vl ?sigmavl) ?stm  =>  match   hexp  with
  |  subst_tm ((scons) ?tty0 var_ty) var_tm var_vl ?ttm  =>  unify   (subst_tm ((scons) sty0 var_ty) var_tm var_vl (ren_tm ((scons) (var_zero) ((funcomp) (shift) sigmaty)) sigmatm sigmavl stm)) (hexp)
  end
  |  subst_tm ?sigmaty ((scons) ?stm0 ?sigmatm) ((scons) ?svl0 ?sigmavl) ?stm  =>  match   hexp  with
  |  subst_tm var_ty ((scons) ?ttm0 var_tm) ((scons) ?tvl0 var_vl) ?ttm  =>  unify   (subst_tm var_ty ((scons) stm0 var_tm) ((scons) svl0 var_vl) (subst_tm sigmaty ((scons) (var_tm (var_zero)) ((funcomp) (ren_tm (id) (shift) (shift)) sigmatm)) ((scons) (var_vl (var_zero)) ((funcomp) (ren_vl (id) (shift) (shift)) sigmavl)) stm)) (hexp)
  end
  |  subst_tm ((scons) ?sty0 ?sigmaty) ?sigmatm ?sigmavl ?stm  =>  match   hexp  with
  |  subst_tm ((scons) ?tty0 var_ty) var_tm var_vl ?ttm  =>  unify   (subst_tm ((scons) sty0 var_ty) var_tm var_vl (subst_tm ((scons) (var_ty (var_zero)) ((funcomp) (ren_ty (shift)) sigmaty)) ((funcomp) (ren_tm (shift) (id) (id)) sigmatm) ((funcomp) (ren_vl (shift) (id) (id)) sigmavl) stm)) (hexp)
  end
  |  ?s  =>  match   hexp  with
  |  subst_ty ?sigma0 ?t  =>  unify   (subst_ty var_ty s) (hexp)
  |  ren_ty ?sigma0 ?t  =>  unify   (ren_ty (id) s) (hexp)
  |  subst_tm ?sigma0 ?sigma1 ?sigma2 ?t  =>  unify   (subst_tm var_ty var_tm var_vl s) (hexp)
  |  ren_tm ?sigma0 ?sigma1 ?sigma2 ?t  =>  unify   (ren_tm (id) (id) (id) s) (hexp)
  |  subst_vl ?sigma0 ?sigma1 ?sigma2 ?t  =>  unify   (subst_vl var_ty var_tm var_vl s) (hexp)
  |  ren_vl ?sigma0 ?sigma1 ?sigma2 ?t  =>  unify   (ren_vl (id) (id) (id) s) (hexp)
  end
  |  arr ?s0 ?s1  =>  match   hexp  with
  |  arr ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  all ?s0  =>  match   hexp  with
  |  all ?t0  =>  heuristics   (s0) (t0)
  end
  |  subst_ty ?sigma0 ?s  =>  match   hexp  with
  |  subst_ty ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  ren_ty ?sigma0 ?s  =>  match   hexp  with
  |  ren_ty ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (subst_ty ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_ty ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (ren_ty ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_ty ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  |  app ?s0 ?s1  =>  match   hexp  with
  |  app ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  tapp ?s0 ?s1  =>  match   hexp  with
  |  tapp ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  vt ?s0  =>  match   hexp  with
  |  vt ?t0  =>  heuristics   (s0) (t0)
  end
  |  subst_tm ?sigma0 ?sigma1 ?sigma2 ?s  =>  match   hexp  with
  |  subst_tm ?tau0 ?tau1 ?tau2 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1); heuristics   (sigma2) (tau2)
  end
  |  ren_tm ?sigma0 ?sigma1 ?sigma2 ?s  =>  match   hexp  with
  |  ren_tm ?tau0 ?tau1 ?tau2 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1); heuristics   (sigma2) (tau2)
  end
  |  (funcomp) (subst_tm ?sigma0 ?sigma1 ?sigma2) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_tm ?tau0 ?tau1 ?tau2) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1); heuristics   (sigma2) (tau2)
  end
  |  (funcomp) (ren_tm ?sigma0 ?sigma1 ?sigma2) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_tm ?tau0 ?tau1 ?tau2) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1); heuristics   (sigma2) (tau2)
  end
  |  lam ?s0 ?s1  =>  match   hexp  with
  |  lam ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  tlam ?s0  =>  match   hexp  with
  |  tlam ?t0  =>  heuristics   (s0) (t0)
  end
  |  subst_vl ?sigma0 ?sigma1 ?sigma2 ?s  =>  match   hexp  with
  |  subst_vl ?tau0 ?tau1 ?tau2 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1); heuristics   (sigma2) (tau2)
  end
  |  ren_vl ?sigma0 ?sigma1 ?sigma2 ?s  =>  match   hexp  with
  |  ren_vl ?tau0 ?tau1 ?tau2 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1); heuristics   (sigma2) (tau2)
  end
  |  (funcomp) (subst_vl ?sigma0 ?sigma1 ?sigma2) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_vl ?tau0 ?tau1 ?tau2) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1); heuristics   (sigma2) (tau2)
  end
  |  (funcomp) (ren_vl ?sigma0 ?sigma1 ?sigma2) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_vl ?tau0 ?tau1 ?tau2) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1); heuristics   (sigma2) (tau2)
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
