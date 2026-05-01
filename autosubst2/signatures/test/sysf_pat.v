Require Export fintype.




Section ty.
Inductive ty (nty : nat) : Type :=
  | var_ty : (fin) (nty) -> ty (nty)
  | top : ty (nty)
  | arr : ty  (nty) -> ty  (nty) -> ty (nty)
  | all : ty  (nty) -> ty  ((S) nty) -> ty (nty)
  | recty : list (prod (nat  ) (ty  (nty))) -> ty (nty).

Lemma congr_top { mty : nat } : top (mty) = top (mty) .
Proof. congruence. Qed.

Lemma congr_arr { mty : nat } { s0 : ty  (mty) } { s1 : ty  (mty) } { t0 : ty  (mty) } { t1 : ty  (mty) } (H1 : s0 = t0) (H2 : s1 = t1) : arr (mty) s0 s1 = arr (mty) t0 t1 .
Proof. congruence. Qed.

Lemma congr_all { mty : nat } { s0 : ty  (mty) } { s1 : ty  ((S) mty) } { t0 : ty  (mty) } { t1 : ty  ((S) mty) } (H1 : s0 = t0) (H2 : s1 = t1) : all (mty) s0 s1 = all (mty) t0 t1 .
Proof. congruence. Qed.

Lemma congr_recty { mty : nat } { s0 : list (prod (nat  ) (ty  (mty))) } { t0 : list (prod (nat  ) (ty  (mty))) } (H1 : s0 = t0) : recty (mty) s0 = recty (mty) t0 .
Proof. congruence. Qed.

Definition upRen_ty_ty { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Fixpoint ren_ty { mty : nat } { nty : nat } (xity : (fin) (mty) -> (fin) (nty)) (s : ty (mty)) : ty (nty) :=
    match s return ty (nty) with
    | var_ty (_) s => (var_ty (nty)) (xity s)
    | top (_)  => top (nty)
    | arr (_) s0 s1 => arr (nty) ((ren_ty xity) s0) ((ren_ty xity) s1)
    | all (_) s0 s1 => all (nty) ((ren_ty xity) s0) ((ren_ty (upRen_ty_ty xity)) s1)
    | recty (_) s0 => recty (nty) ((list_map (prod_map (fun x => x) (ren_ty xity))) s0)
    end.

Definition up_ty_ty { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) : (fin) ((S) (m)) -> ty ((S) nty) :=
  (scons) ((var_ty ((S) nty)) (var_zero)) ((funcomp) (ren_ty (shift)) sigma).

Fixpoint subst_ty { mty : nat } { nty : nat } (sigmaty : (fin) (mty) -> ty (nty)) (s : ty (mty)) : ty (nty) :=
    match s return ty (nty) with
    | var_ty (_) s => sigmaty s
    | top (_)  => top (nty)
    | arr (_) s0 s1 => arr (nty) ((subst_ty sigmaty) s0) ((subst_ty sigmaty) s1)
    | all (_) s0 s1 => all (nty) ((subst_ty sigmaty) s0) ((subst_ty (up_ty_ty sigmaty)) s1)
    | recty (_) s0 => recty (nty) ((list_map (prod_map (fun x => x) (subst_ty sigmaty))) s0)
    end.

Definition upId_ty_ty { mty : nat } (sigma : (fin) (mty) -> ty (mty)) (Eq : forall x, sigma x = (var_ty (mty)) x) : forall x, (up_ty_ty sigma) x = (var_ty ((S) mty)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_ty (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint idSubst_ty { mty : nat } (sigmaty : (fin) (mty) -> ty (mty)) (Eqty : forall x, sigmaty x = (var_ty (mty)) x) (s : ty (mty)) : subst_ty sigmaty s = s :=
    match s return subst_ty sigmaty s = s with
    | var_ty (_) s => Eqty s
    | top (_)  => congr_top 
    | arr (_) s0 s1 => congr_arr ((idSubst_ty sigmaty Eqty) s0) ((idSubst_ty sigmaty Eqty) s1)
    | all (_) s0 s1 => congr_all ((idSubst_ty sigmaty Eqty) s0) ((idSubst_ty (up_ty_ty sigmaty) (upId_ty_ty (_) Eqty)) s1)
    | recty (_) s0 => congr_recty ((list_id (prod_id (fun x => (eq_refl) x) (idSubst_ty sigmaty Eqty))) s0)
    end.

Definition upExtRen_ty_ty { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_ty_ty xi) x = (upRen_ty_ty zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint extRen_ty { mty : nat } { nty : nat } (xity : (fin) (mty) -> (fin) (nty)) (zetaty : (fin) (mty) -> (fin) (nty)) (Eqty : forall x, xity x = zetaty x) (s : ty (mty)) : ren_ty xity s = ren_ty zetaty s :=
    match s return ren_ty xity s = ren_ty zetaty s with
    | var_ty (_) s => (ap) (var_ty (nty)) (Eqty s)
    | top (_)  => congr_top 
    | arr (_) s0 s1 => congr_arr ((extRen_ty xity zetaty Eqty) s0) ((extRen_ty xity zetaty Eqty) s1)
    | all (_) s0 s1 => congr_all ((extRen_ty xity zetaty Eqty) s0) ((extRen_ty (upRen_ty_ty xity) (upRen_ty_ty zetaty) (upExtRen_ty_ty (_) (_) Eqty)) s1)
    | recty (_) s0 => congr_recty ((list_ext (prod_ext (fun x => (eq_refl) x) (extRen_ty xity zetaty Eqty))) s0)
    end.

Definition upExt_ty_ty { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) (tau : (fin) (m) -> ty (nty)) (Eq : forall x, sigma x = tau x) : forall x, (up_ty_ty sigma) x = (up_ty_ty tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_ty (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint ext_ty { mty : nat } { nty : nat } (sigmaty : (fin) (mty) -> ty (nty)) (tauty : (fin) (mty) -> ty (nty)) (Eqty : forall x, sigmaty x = tauty x) (s : ty (mty)) : subst_ty sigmaty s = subst_ty tauty s :=
    match s return subst_ty sigmaty s = subst_ty tauty s with
    | var_ty (_) s => Eqty s
    | top (_)  => congr_top 
    | arr (_) s0 s1 => congr_arr ((ext_ty sigmaty tauty Eqty) s0) ((ext_ty sigmaty tauty Eqty) s1)
    | all (_) s0 s1 => congr_all ((ext_ty sigmaty tauty Eqty) s0) ((ext_ty (up_ty_ty sigmaty) (up_ty_ty tauty) (upExt_ty_ty (_) (_) Eqty)) s1)
    | recty (_) s0 => congr_recty ((list_ext (prod_ext (fun x => (eq_refl) x) (ext_ty sigmaty tauty Eqty))) s0)
    end.

Definition up_ren_ren_ty_ty { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_ty_ty tau) (upRen_ty_ty xi)) x = (upRen_ty_ty theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_ty { kty : nat } { lty : nat } { mty : nat } (xity : (fin) (mty) -> (fin) (kty)) (zetaty : (fin) (kty) -> (fin) (lty)) (rhoty : (fin) (mty) -> (fin) (lty)) (Eqty : forall x, ((funcomp) zetaty xity) x = rhoty x) (s : ty (mty)) : ren_ty zetaty (ren_ty xity s) = ren_ty rhoty s :=
    match s return ren_ty zetaty (ren_ty xity s) = ren_ty rhoty s with
    | var_ty (_) s => (ap) (var_ty (lty)) (Eqty s)
    | top (_)  => congr_top 
    | arr (_) s0 s1 => congr_arr ((compRenRen_ty xity zetaty rhoty Eqty) s0) ((compRenRen_ty xity zetaty rhoty Eqty) s1)
    | all (_) s0 s1 => congr_all ((compRenRen_ty xity zetaty rhoty Eqty) s0) ((compRenRen_ty (upRen_ty_ty xity) (upRen_ty_ty zetaty) (upRen_ty_ty rhoty) (up_ren_ren (_) (_) (_) Eqty)) s1)
    | recty (_) s0 => congr_recty ((list_comp (prod_comp (fun x => (eq_refl) x) (compRenRen_ty xity zetaty rhoty Eqty))) s0)
    end.

Definition up_ren_subst_ty_ty { k : nat } { l : nat } { mty : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_ty_ty tau) (upRen_ty_ty xi)) x = (up_ty_ty theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_ty (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint compRenSubst_ty { kty : nat } { lty : nat } { mty : nat } (xity : (fin) (mty) -> (fin) (kty)) (tauty : (fin) (kty) -> ty (lty)) (thetaty : (fin) (mty) -> ty (lty)) (Eqty : forall x, ((funcomp) tauty xity) x = thetaty x) (s : ty (mty)) : subst_ty tauty (ren_ty xity s) = subst_ty thetaty s :=
    match s return subst_ty tauty (ren_ty xity s) = subst_ty thetaty s with
    | var_ty (_) s => Eqty s
    | top (_)  => congr_top 
    | arr (_) s0 s1 => congr_arr ((compRenSubst_ty xity tauty thetaty Eqty) s0) ((compRenSubst_ty xity tauty thetaty Eqty) s1)
    | all (_) s0 s1 => congr_all ((compRenSubst_ty xity tauty thetaty Eqty) s0) ((compRenSubst_ty (upRen_ty_ty xity) (up_ty_ty tauty) (up_ty_ty thetaty) (up_ren_subst_ty_ty (_) (_) (_) Eqty)) s1)
    | recty (_) s0 => congr_recty ((list_comp (prod_comp (fun x => (eq_refl) x) (compRenSubst_ty xity tauty thetaty Eqty))) s0)
    end.

Definition up_subst_ren_ty_ty { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (zetaty : (fin) (lty) -> (fin) (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (ren_ty zetaty) sigma) x = theta x) : forall x, ((funcomp) (ren_ty (upRen_ty_ty zetaty)) (up_ty_ty sigma)) x = (up_ty_ty theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_ty (shift) (upRen_ty_ty zetaty) ((funcomp) (shift) zetaty) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_ty zetaty (shift) ((funcomp) (shift) zetaty) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_ty (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstRen_ty { kty : nat } { lty : nat } { mty : nat } (sigmaty : (fin) (mty) -> ty (kty)) (zetaty : (fin) (kty) -> (fin) (lty)) (thetaty : (fin) (mty) -> ty (lty)) (Eqty : forall x, ((funcomp) (ren_ty zetaty) sigmaty) x = thetaty x) (s : ty (mty)) : ren_ty zetaty (subst_ty sigmaty s) = subst_ty thetaty s :=
    match s return ren_ty zetaty (subst_ty sigmaty s) = subst_ty thetaty s with
    | var_ty (_) s => Eqty s
    | top (_)  => congr_top 
    | arr (_) s0 s1 => congr_arr ((compSubstRen_ty sigmaty zetaty thetaty Eqty) s0) ((compSubstRen_ty sigmaty zetaty thetaty Eqty) s1)
    | all (_) s0 s1 => congr_all ((compSubstRen_ty sigmaty zetaty thetaty Eqty) s0) ((compSubstRen_ty (up_ty_ty sigmaty) (upRen_ty_ty zetaty) (up_ty_ty thetaty) (up_subst_ren_ty_ty (_) (_) (_) Eqty)) s1)
    | recty (_) s0 => congr_recty ((list_comp (prod_comp (fun x => (eq_refl) x) (compSubstRen_ty sigmaty zetaty thetaty Eqty))) s0)
    end.

Definition up_subst_subst_ty_ty { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (tauty : (fin) (lty) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (subst_ty tauty) sigma) x = theta x) : forall x, ((funcomp) (subst_ty (up_ty_ty tauty)) (up_ty_ty sigma)) x = (up_ty_ty theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_ty (shift) (up_ty_ty tauty) ((funcomp) (up_ty_ty tauty) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_ty tauty (shift) ((funcomp) (ren_ty (shift)) tauty) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_ty (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstSubst_ty { kty : nat } { lty : nat } { mty : nat } (sigmaty : (fin) (mty) -> ty (kty)) (tauty : (fin) (kty) -> ty (lty)) (thetaty : (fin) (mty) -> ty (lty)) (Eqty : forall x, ((funcomp) (subst_ty tauty) sigmaty) x = thetaty x) (s : ty (mty)) : subst_ty tauty (subst_ty sigmaty s) = subst_ty thetaty s :=
    match s return subst_ty tauty (subst_ty sigmaty s) = subst_ty thetaty s with
    | var_ty (_) s => Eqty s
    | top (_)  => congr_top 
    | arr (_) s0 s1 => congr_arr ((compSubstSubst_ty sigmaty tauty thetaty Eqty) s0) ((compSubstSubst_ty sigmaty tauty thetaty Eqty) s1)
    | all (_) s0 s1 => congr_all ((compSubstSubst_ty sigmaty tauty thetaty Eqty) s0) ((compSubstSubst_ty (up_ty_ty sigmaty) (up_ty_ty tauty) (up_ty_ty thetaty) (up_subst_subst_ty_ty (_) (_) (_) Eqty)) s1)
    | recty (_) s0 => congr_recty ((list_comp (prod_comp (fun x => (eq_refl) x) (compSubstSubst_ty sigmaty tauty thetaty Eqty))) s0)
    end.

Definition rinstInst_up_ty_ty { m : nat } { nty : nat } (xi : (fin) (m) -> (fin) (nty)) (sigma : (fin) (m) -> ty (nty)) (Eq : forall x, ((funcomp) (var_ty (nty)) xi) x = sigma x) : forall x, ((funcomp) (var_ty ((S) nty)) (upRen_ty_ty xi)) x = (up_ty_ty sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_ty (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint rinst_inst_ty { mty : nat } { nty : nat } (xity : (fin) (mty) -> (fin) (nty)) (sigmaty : (fin) (mty) -> ty (nty)) (Eqty : forall x, ((funcomp) (var_ty (nty)) xity) x = sigmaty x) (s : ty (mty)) : ren_ty xity s = subst_ty sigmaty s :=
    match s return ren_ty xity s = subst_ty sigmaty s with
    | var_ty (_) s => Eqty s
    | top (_)  => congr_top 
    | arr (_) s0 s1 => congr_arr ((rinst_inst_ty xity sigmaty Eqty) s0) ((rinst_inst_ty xity sigmaty Eqty) s1)
    | all (_) s0 s1 => congr_all ((rinst_inst_ty xity sigmaty Eqty) s0) ((rinst_inst_ty (upRen_ty_ty xity) (up_ty_ty sigmaty) (rinstInst_up_ty_ty (_) (_) Eqty)) s1)
    | recty (_) s0 => congr_recty ((list_ext (prod_ext (fun x => (eq_refl) x) (rinst_inst_ty xity sigmaty Eqty))) s0)
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

Section tm.
Inductive tm (nty ntm : nat) : Type :=
  | var_tm : (fin) (ntm) -> tm (nty) (ntm)
  | app : tm  (nty) (ntm) -> tm  (nty) (ntm) -> tm (nty) (ntm)
  | tapp : tm  (nty) (ntm) -> ty  (nty) -> tm (nty) (ntm)
  | abs : ty  (nty) -> tm  (nty) ((S) ntm) -> tm (nty) (ntm)
  | tabs : ty  (nty) -> tm  ((S) nty) (ntm) -> tm (nty) (ntm)
  | rectm : list (prod (nat  ) (tm  (nty) (ntm))) -> tm (nty) (ntm)
  | proj : tm  (nty) (ntm) -> nat   -> tm (nty) (ntm)
  | letpat
  : forall (p : nat), tm  (nty) (ntm) -> cod (fin p) (ty  (nty)) -> cod (fin p) (list (nat  )) -> tm  (nty) (p + ntm) -> tm (nty) (ntm).

Lemma congr_app { mty mtm : nat } { s0 : tm  (mty) (mtm) } { s1 : tm  (mty) (mtm) } { t0 : tm  (mty) (mtm) } { t1 : tm  (mty) (mtm) } (H1 : s0 = t0) (H2 : s1 = t1) : app (mty) (mtm) s0 s1 = app (mty) (mtm) t0 t1 .
Proof. congruence. Qed.

Lemma congr_tapp { mty mtm : nat } { s0 : tm  (mty) (mtm) } { s1 : ty  (mty) } { t0 : tm  (mty) (mtm) } { t1 : ty  (mty) } (H1 : s0 = t0) (H2 : s1 = t1) : tapp (mty) (mtm) s0 s1 = tapp (mty) (mtm) t0 t1 .
Proof. congruence. Qed.

Lemma congr_abs { mty mtm : nat } { s0 : ty  (mty) } { s1 : tm  (mty) ((S) mtm) } { t0 : ty  (mty) } { t1 : tm  (mty) ((S) mtm) } (H1 : s0 = t0) (H2 : s1 = t1) : abs (mty) (mtm) s0 s1 = abs (mty) (mtm) t0 t1 .
Proof. congruence. Qed.

Lemma congr_tabs { mty mtm : nat } { s0 : ty  (mty) } { s1 : tm  ((S) mty) (mtm) } { t0 : ty  (mty) } { t1 : tm  ((S) mty) (mtm) } (H1 : s0 = t0) (H2 : s1 = t1) : tabs (mty) (mtm) s0 s1 = tabs (mty) (mtm) t0 t1 .
Proof. congruence. Qed.

Lemma congr_rectm { mty mtm : nat } { s0 : list (prod (nat  ) (tm  (mty) (mtm))) } { t0 : list (prod (nat  ) (tm  (mty) (mtm))) } (H1 : s0 = t0) : rectm (mty) (mtm) s0 = rectm (mty) (mtm) t0 .
Proof. congruence. Qed.

Lemma congr_proj { mty mtm : nat } { s0 : tm  (mty) (mtm) } { s1 : nat   } { t0 : tm  (mty) (mtm) } { t1 : nat   } (H1 : s0 = t0) (H2 : s1 = t1) : proj (mty) (mtm) s0 s1 = proj (mty) (mtm) t0 t1 .
Proof. congruence. Qed.

Lemma congr_letpat { p : nat } { mty mtm : nat } { s0 : tm  (mty) (mtm) } { s1 : cod (fin p) (ty  (mty)) } { s2 : cod (fin p) (list (nat  )) } { s3 : tm  (mty) (p + mtm) } { t0 : tm  (mty) (mtm) } { t1 : cod (fin p) (ty  (mty)) } { t2 : cod (fin p) (list (nat  )) } { t3 : tm  (mty) (p + mtm) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) : letpat (mty) (mtm) p s0 s1 s2 s3 = letpat (mty) (mtm) p t0 t1 t2 t3 .
Proof. congruence. Qed.

Definition upRen_ty_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (m) -> (fin) (n) :=
  xi.

Definition upRen_tm_ty { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (m) -> (fin) (n) :=
  xi.

Definition upRen_tm_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Definition upRenList_tm_ty (p : nat) { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (m) -> (fin) (n) :=
  xi.

Definition upRenList_tm_tm (p : nat) { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (p + (m)) -> (fin) (p + (n)) :=
  upRen_p p xi.

Fixpoint ren_tm { mty mtm : nat } { nty ntm : nat } (xity : (fin) (mty) -> (fin) (nty)) (xitm : (fin) (mtm) -> (fin) (ntm)) (s : tm (mty) (mtm)) : tm (nty) (ntm) :=
    match s return tm (nty) (ntm) with
    | var_tm (_) (_) s => (var_tm (nty) (ntm)) (xitm s)
    | app (_) (_) s0 s1 => app (nty) (ntm) ((ren_tm xity xitm) s0) ((ren_tm xity xitm) s1)
    | tapp (_) (_) s0 s1 => tapp (nty) (ntm) ((ren_tm xity xitm) s0) ((ren_ty xity) s1)
    | abs (_) (_) s0 s1 => abs (nty) (ntm) ((ren_ty xity) s0) ((ren_tm (upRen_tm_ty xity) (upRen_tm_tm xitm)) s1)
    | tabs (_) (_) s0 s1 => tabs (nty) (ntm) ((ren_ty xity) s0) ((ren_tm (upRen_ty_ty xity) (upRen_ty_tm xitm)) s1)
    | rectm (_) (_) s0 => rectm (nty) (ntm) ((list_map (prod_map (fun x => x) (ren_tm xity xitm))) s0)
    | proj (_) (_) s0 s1 => proj (nty) (ntm) ((ren_tm xity xitm) s0) ((fun x => x) s1)
    | letpat (_) (_) p s0 s1 s2 s3 => letpat (nty) (ntm) p ((ren_tm xity xitm) s0) ((cod_map (ren_ty xity)) s1) ((cod_map (list_map (fun x => x))) s2) ((ren_tm (upRenList_tm_ty p xity) (upRenList_tm_tm p xitm)) s3)
    end.

Definition up_ty_tm { m : nat } { nty ntm : nat } (sigma : (fin) (m) -> tm (nty) (ntm)) : (fin) (m) -> tm ((S) nty) (ntm) :=
  (funcomp) (ren_tm (shift) (id)) sigma.

Definition up_tm_ty { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) : (fin) (m) -> ty (nty) :=
  (funcomp) (ren_ty (id)) sigma.

Definition up_tm_tm { m : nat } { nty ntm : nat } (sigma : (fin) (m) -> tm (nty) (ntm)) : (fin) ((S) (m)) -> tm (nty) ((S) ntm) :=
  (scons) ((var_tm (nty) ((S) ntm)) (var_zero)) ((funcomp) (ren_tm (id) (shift)) sigma).

Definition upList_tm_ty (p : nat) { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) : (fin) (m) -> ty (nty) :=
  (funcomp) (ren_ty (id)) sigma.

Definition upList_tm_tm (p : nat) { m : nat } { nty ntm : nat } (sigma : (fin) (m) -> tm (nty) (ntm)) : (fin) (p + (m)) -> tm (nty) (p + ntm) :=
  scons_p  p ((funcomp) (var_tm (nty) (p + ntm)) (zero_p p)) ((funcomp) (ren_tm (id) (shift_p p)) sigma).

Fixpoint subst_tm { mty mtm : nat } { nty ntm : nat } (sigmaty : (fin) (mty) -> ty (nty)) (sigmatm : (fin) (mtm) -> tm (nty) (ntm)) (s : tm (mty) (mtm)) : tm (nty) (ntm) :=
    match s return tm (nty) (ntm) with
    | var_tm (_) (_) s => sigmatm s
    | app (_) (_) s0 s1 => app (nty) (ntm) ((subst_tm sigmaty sigmatm) s0) ((subst_tm sigmaty sigmatm) s1)
    | tapp (_) (_) s0 s1 => tapp (nty) (ntm) ((subst_tm sigmaty sigmatm) s0) ((subst_ty sigmaty) s1)
    | abs (_) (_) s0 s1 => abs (nty) (ntm) ((subst_ty sigmaty) s0) ((subst_tm (up_tm_ty sigmaty) (up_tm_tm sigmatm)) s1)
    | tabs (_) (_) s0 s1 => tabs (nty) (ntm) ((subst_ty sigmaty) s0) ((subst_tm (up_ty_ty sigmaty) (up_ty_tm sigmatm)) s1)
    | rectm (_) (_) s0 => rectm (nty) (ntm) ((list_map (prod_map (fun x => x) (subst_tm sigmaty sigmatm))) s0)
    | proj (_) (_) s0 s1 => proj (nty) (ntm) ((subst_tm sigmaty sigmatm) s0) ((fun x => x) s1)
    | letpat (_) (_) p s0 s1 s2 s3 => letpat (nty) (ntm) p ((subst_tm sigmaty sigmatm) s0) ((cod_map (subst_ty sigmaty)) s1) ((cod_map (list_map (fun x => x))) s2) ((subst_tm (upList_tm_ty p sigmaty) (upList_tm_tm p sigmatm)) s3)
    end.

Definition upId_ty_tm { mty mtm : nat } (sigma : (fin) (mtm) -> tm (mty) (mtm)) (Eq : forall x, sigma x = (var_tm (mty) (mtm)) x) : forall x, (up_ty_tm sigma) x = (var_tm ((S) mty) (mtm)) x :=
  fun n => (ap) (ren_tm (shift) (id)) (Eq n).

Definition upId_tm_ty { mty : nat } (sigma : (fin) (mty) -> ty (mty)) (Eq : forall x, sigma x = (var_ty (mty)) x) : forall x, (up_tm_ty sigma) x = (var_ty (mty)) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition upId_tm_tm { mty mtm : nat } (sigma : (fin) (mtm) -> tm (mty) (mtm)) (Eq : forall x, sigma x = (var_tm (mty) (mtm)) x) : forall x, (up_tm_tm sigma) x = (var_tm (mty) ((S) mtm)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (id) (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Definition upIdList_tm_ty { p : nat } { mty : nat } (sigma : (fin) (mty) -> ty (mty)) (Eq : forall x, sigma x = (var_ty (mty)) x) : forall x, (upList_tm_ty p sigma) x = (var_ty (mty)) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition upIdList_tm_tm { p : nat } { mty mtm : nat } (sigma : (fin) (mtm) -> tm (mty) (mtm)) (Eq : forall x, sigma x = (var_tm (mty) (mtm)) x) : forall x, (upList_tm_tm p sigma) x = (var_tm (mty) (p + mtm)) x :=
  fun n => scons_p_eta (var_tm (mty) (p + mtm)) (fun n => (ap) (ren_tm (id) (shift_p p)) (Eq n)) (fun n => eq_refl).

Fixpoint idSubst_tm { mty mtm : nat } (sigmaty : (fin) (mty) -> ty (mty)) (sigmatm : (fin) (mtm) -> tm (mty) (mtm)) (Eqty : forall x, sigmaty x = (var_ty (mty)) x) (Eqtm : forall x, sigmatm x = (var_tm (mty) (mtm)) x) (s : tm (mty) (mtm)) : subst_tm sigmaty sigmatm s = s :=
    match s return subst_tm sigmaty sigmatm s = s with
    | var_tm (_) (_) s => Eqtm s
    | app (_) (_) s0 s1 => congr_app ((idSubst_tm sigmaty sigmatm Eqty Eqtm) s0) ((idSubst_tm sigmaty sigmatm Eqty Eqtm) s1)
    | tapp (_) (_) s0 s1 => congr_tapp ((idSubst_tm sigmaty sigmatm Eqty Eqtm) s0) ((idSubst_ty sigmaty Eqty) s1)
    | abs (_) (_) s0 s1 => congr_abs ((idSubst_ty sigmaty Eqty) s0) ((idSubst_tm (up_tm_ty sigmaty) (up_tm_tm sigmatm) (upId_tm_ty (_) Eqty) (upId_tm_tm (_) Eqtm)) s1)
    | tabs (_) (_) s0 s1 => congr_tabs ((idSubst_ty sigmaty Eqty) s0) ((idSubst_tm (up_ty_ty sigmaty) (up_ty_tm sigmatm) (upId_ty_ty (_) Eqty) (upId_ty_tm (_) Eqtm)) s1)
    | rectm (_) (_) s0 => congr_rectm ((list_id (prod_id (fun x => (eq_refl) x) (idSubst_tm sigmaty sigmatm Eqty Eqtm))) s0)
    | proj (_) (_) s0 s1 => congr_proj ((idSubst_tm sigmaty sigmatm Eqty Eqtm) s0) ((fun x => (eq_refl) x) s1)
    | letpat (_) (_) p s0 s1 s2 s3 => congr_letpat ((idSubst_tm sigmaty sigmatm Eqty Eqtm) s0) ((cod_id (idSubst_ty sigmaty Eqty)) s1) ((cod_id (list_id (fun x => (eq_refl) x))) s2) ((idSubst_tm (upList_tm_ty p sigmaty) (upList_tm_tm p sigmatm) (upIdList_tm_ty (_) Eqty) (upIdList_tm_tm (_) Eqtm)) s3)
    end.

Definition upExtRen_ty_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_ty_tm xi) x = (upRen_ty_tm zeta) x :=
  fun n => Eq n.

Definition upExtRen_tm_ty { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_tm_ty xi) x = (upRen_tm_ty zeta) x :=
  fun n => Eq n.

Definition upExtRen_tm_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_tm_tm xi) x = (upRen_tm_tm zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Definition upExtRen_list_tm_ty { p : nat } { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRenList_tm_ty p xi) x = (upRenList_tm_ty p zeta) x :=
  fun n => Eq n.

Definition upExtRen_list_tm_tm { p : nat } { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRenList_tm_tm p xi) x = (upRenList_tm_tm p zeta) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (shift_p p) (Eq n)).

Fixpoint extRen_tm { mty mtm : nat } { nty ntm : nat } (xity : (fin) (mty) -> (fin) (nty)) (xitm : (fin) (mtm) -> (fin) (ntm)) (zetaty : (fin) (mty) -> (fin) (nty)) (zetatm : (fin) (mtm) -> (fin) (ntm)) (Eqty : forall x, xity x = zetaty x) (Eqtm : forall x, xitm x = zetatm x) (s : tm (mty) (mtm)) : ren_tm xity xitm s = ren_tm zetaty zetatm s :=
    match s return ren_tm xity xitm s = ren_tm zetaty zetatm s with
    | var_tm (_) (_) s => (ap) (var_tm (nty) (ntm)) (Eqtm s)
    | app (_) (_) s0 s1 => congr_app ((extRen_tm xity xitm zetaty zetatm Eqty Eqtm) s0) ((extRen_tm xity xitm zetaty zetatm Eqty Eqtm) s1)
    | tapp (_) (_) s0 s1 => congr_tapp ((extRen_tm xity xitm zetaty zetatm Eqty Eqtm) s0) ((extRen_ty xity zetaty Eqty) s1)
    | abs (_) (_) s0 s1 => congr_abs ((extRen_ty xity zetaty Eqty) s0) ((extRen_tm (upRen_tm_ty xity) (upRen_tm_tm xitm) (upRen_tm_ty zetaty) (upRen_tm_tm zetatm) (upExtRen_tm_ty (_) (_) Eqty) (upExtRen_tm_tm (_) (_) Eqtm)) s1)
    | tabs (_) (_) s0 s1 => congr_tabs ((extRen_ty xity zetaty Eqty) s0) ((extRen_tm (upRen_ty_ty xity) (upRen_ty_tm xitm) (upRen_ty_ty zetaty) (upRen_ty_tm zetatm) (upExtRen_ty_ty (_) (_) Eqty) (upExtRen_ty_tm (_) (_) Eqtm)) s1)
    | rectm (_) (_) s0 => congr_rectm ((list_ext (prod_ext (fun x => (eq_refl) x) (extRen_tm xity xitm zetaty zetatm Eqty Eqtm))) s0)
    | proj (_) (_) s0 s1 => congr_proj ((extRen_tm xity xitm zetaty zetatm Eqty Eqtm) s0) ((fun x => (eq_refl) x) s1)
    | letpat (_) (_) p s0 s1 s2 s3 => congr_letpat ((extRen_tm xity xitm zetaty zetatm Eqty Eqtm) s0) ((cod_ext (extRen_ty xity zetaty Eqty)) s1) ((cod_ext (list_ext (fun x => (eq_refl) x))) s2) ((extRen_tm (upRenList_tm_ty p xity) (upRenList_tm_tm p xitm) (upRenList_tm_ty p zetaty) (upRenList_tm_tm p zetatm) (upExtRen_list_tm_ty (_) (_) Eqty) (upExtRen_list_tm_tm (_) (_) Eqtm)) s3)
    end.

Definition upExt_ty_tm { m : nat } { nty ntm : nat } (sigma : (fin) (m) -> tm (nty) (ntm)) (tau : (fin) (m) -> tm (nty) (ntm)) (Eq : forall x, sigma x = tau x) : forall x, (up_ty_tm sigma) x = (up_ty_tm tau) x :=
  fun n => (ap) (ren_tm (shift) (id)) (Eq n).

Definition upExt_tm_ty { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) (tau : (fin) (m) -> ty (nty)) (Eq : forall x, sigma x = tau x) : forall x, (up_tm_ty sigma) x = (up_tm_ty tau) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition upExt_tm_tm { m : nat } { nty ntm : nat } (sigma : (fin) (m) -> tm (nty) (ntm)) (tau : (fin) (m) -> tm (nty) (ntm)) (Eq : forall x, sigma x = tau x) : forall x, (up_tm_tm sigma) x = (up_tm_tm tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (id) (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Definition upExt_list_tm_ty { p : nat } { m : nat } { nty : nat } (sigma : (fin) (m) -> ty (nty)) (tau : (fin) (m) -> ty (nty)) (Eq : forall x, sigma x = tau x) : forall x, (upList_tm_ty p sigma) x = (upList_tm_ty p tau) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition upExt_list_tm_tm { p : nat } { m : nat } { nty ntm : nat } (sigma : (fin) (m) -> tm (nty) (ntm)) (tau : (fin) (m) -> tm (nty) (ntm)) (Eq : forall x, sigma x = tau x) : forall x, (upList_tm_tm p sigma) x = (upList_tm_tm p tau) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (ren_tm (id) (shift_p p)) (Eq n)).

Fixpoint ext_tm { mty mtm : nat } { nty ntm : nat } (sigmaty : (fin) (mty) -> ty (nty)) (sigmatm : (fin) (mtm) -> tm (nty) (ntm)) (tauty : (fin) (mty) -> ty (nty)) (tautm : (fin) (mtm) -> tm (nty) (ntm)) (Eqty : forall x, sigmaty x = tauty x) (Eqtm : forall x, sigmatm x = tautm x) (s : tm (mty) (mtm)) : subst_tm sigmaty sigmatm s = subst_tm tauty tautm s :=
    match s return subst_tm sigmaty sigmatm s = subst_tm tauty tautm s with
    | var_tm (_) (_) s => Eqtm s
    | app (_) (_) s0 s1 => congr_app ((ext_tm sigmaty sigmatm tauty tautm Eqty Eqtm) s0) ((ext_tm sigmaty sigmatm tauty tautm Eqty Eqtm) s1)
    | tapp (_) (_) s0 s1 => congr_tapp ((ext_tm sigmaty sigmatm tauty tautm Eqty Eqtm) s0) ((ext_ty sigmaty tauty Eqty) s1)
    | abs (_) (_) s0 s1 => congr_abs ((ext_ty sigmaty tauty Eqty) s0) ((ext_tm (up_tm_ty sigmaty) (up_tm_tm sigmatm) (up_tm_ty tauty) (up_tm_tm tautm) (upExt_tm_ty (_) (_) Eqty) (upExt_tm_tm (_) (_) Eqtm)) s1)
    | tabs (_) (_) s0 s1 => congr_tabs ((ext_ty sigmaty tauty Eqty) s0) ((ext_tm (up_ty_ty sigmaty) (up_ty_tm sigmatm) (up_ty_ty tauty) (up_ty_tm tautm) (upExt_ty_ty (_) (_) Eqty) (upExt_ty_tm (_) (_) Eqtm)) s1)
    | rectm (_) (_) s0 => congr_rectm ((list_ext (prod_ext (fun x => (eq_refl) x) (ext_tm sigmaty sigmatm tauty tautm Eqty Eqtm))) s0)
    | proj (_) (_) s0 s1 => congr_proj ((ext_tm sigmaty sigmatm tauty tautm Eqty Eqtm) s0) ((fun x => (eq_refl) x) s1)
    | letpat (_) (_) p s0 s1 s2 s3 => congr_letpat ((ext_tm sigmaty sigmatm tauty tautm Eqty Eqtm) s0) ((cod_ext (ext_ty sigmaty tauty Eqty)) s1) ((cod_ext (list_ext (fun x => (eq_refl) x))) s2) ((ext_tm (upList_tm_ty p sigmaty) (upList_tm_tm p sigmatm) (upList_tm_ty p tauty) (upList_tm_tm p tautm) (upExt_list_tm_ty (_) (_) Eqty) (upExt_list_tm_tm (_) (_) Eqtm)) s3)
    end.

Definition up_ren_ren_ty_tm { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_ty_tm tau) (upRen_ty_tm xi)) x = (upRen_ty_tm theta) x :=
  Eq.

Definition up_ren_ren_tm_ty { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_tm_ty tau) (upRen_tm_ty xi)) x = (upRen_tm_ty theta) x :=
  Eq.

Definition up_ren_ren_tm_tm { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_tm_tm tau) (upRen_tm_tm xi)) x = (upRen_tm_tm theta) x :=
  up_ren_ren xi tau theta Eq.

Definition up_ren_ren_list_tm_ty { p : nat } { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRenList_tm_ty p tau) (upRenList_tm_ty p xi)) x = (upRenList_tm_ty p theta) x :=
  Eq.

Definition up_ren_ren_list_tm_tm { p : nat } { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRenList_tm_tm p tau) (upRenList_tm_tm p xi)) x = (upRenList_tm_tm p theta) x :=
  up_ren_ren_p Eq.

Fixpoint compRenRen_tm { kty ktm : nat } { lty ltm : nat } { mty mtm : nat } (xity : (fin) (mty) -> (fin) (kty)) (xitm : (fin) (mtm) -> (fin) (ktm)) (zetaty : (fin) (kty) -> (fin) (lty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (rhoty : (fin) (mty) -> (fin) (lty)) (rhotm : (fin) (mtm) -> (fin) (ltm)) (Eqty : forall x, ((funcomp) zetaty xity) x = rhoty x) (Eqtm : forall x, ((funcomp) zetatm xitm) x = rhotm x) (s : tm (mty) (mtm)) : ren_tm zetaty zetatm (ren_tm xity xitm s) = ren_tm rhoty rhotm s :=
    match s return ren_tm zetaty zetatm (ren_tm xity xitm s) = ren_tm rhoty rhotm s with
    | var_tm (_) (_) s => (ap) (var_tm (lty) (ltm)) (Eqtm s)
    | app (_) (_) s0 s1 => congr_app ((compRenRen_tm xity xitm zetaty zetatm rhoty rhotm Eqty Eqtm) s0) ((compRenRen_tm xity xitm zetaty zetatm rhoty rhotm Eqty Eqtm) s1)
    | tapp (_) (_) s0 s1 => congr_tapp ((compRenRen_tm xity xitm zetaty zetatm rhoty rhotm Eqty Eqtm) s0) ((compRenRen_ty xity zetaty rhoty Eqty) s1)
    | abs (_) (_) s0 s1 => congr_abs ((compRenRen_ty xity zetaty rhoty Eqty) s0) ((compRenRen_tm (upRen_tm_ty xity) (upRen_tm_tm xitm) (upRen_tm_ty zetaty) (upRen_tm_tm zetatm) (upRen_tm_ty rhoty) (upRen_tm_tm rhotm) Eqty (up_ren_ren (_) (_) (_) Eqtm)) s1)
    | tabs (_) (_) s0 s1 => congr_tabs ((compRenRen_ty xity zetaty rhoty Eqty) s0) ((compRenRen_tm (upRen_ty_ty xity) (upRen_ty_tm xitm) (upRen_ty_ty zetaty) (upRen_ty_tm zetatm) (upRen_ty_ty rhoty) (upRen_ty_tm rhotm) (up_ren_ren (_) (_) (_) Eqty) Eqtm) s1)
    | rectm (_) (_) s0 => congr_rectm ((list_comp (prod_comp (fun x => (eq_refl) x) (compRenRen_tm xity xitm zetaty zetatm rhoty rhotm Eqty Eqtm))) s0)
    | proj (_) (_) s0 s1 => congr_proj ((compRenRen_tm xity xitm zetaty zetatm rhoty rhotm Eqty Eqtm) s0) ((fun x => (eq_refl) x) s1)
    | letpat (_) (_) p s0 s1 s2 s3 => congr_letpat ((compRenRen_tm xity xitm zetaty zetatm rhoty rhotm Eqty Eqtm) s0) ((cod_comp (compRenRen_ty xity zetaty rhoty Eqty)) s1) ((cod_comp (list_comp (fun x => (eq_refl) x))) s2) ((compRenRen_tm (upRenList_tm_ty p xity) (upRenList_tm_tm p xitm) (upRenList_tm_ty p zetaty) (upRenList_tm_tm p zetatm) (upRenList_tm_ty p rhoty) (upRenList_tm_tm p rhotm) Eqty (up_ren_ren_p Eqtm)) s3)
    end.

Definition up_ren_subst_ty_tm { k : nat } { l : nat } { mty mtm : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> tm (mty) (mtm)) (theta : (fin) (k) -> tm (mty) (mtm)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_ty_tm tau) (upRen_ty_tm xi)) x = (up_ty_tm theta) x :=
  fun n => (ap) (ren_tm (shift) (id)) (Eq n).

Definition up_ren_subst_tm_ty { k : nat } { l : nat } { mty : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_tm_ty tau) (upRen_tm_ty xi)) x = (up_tm_ty theta) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition up_ren_subst_tm_tm { k : nat } { l : nat } { mty mtm : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> tm (mty) (mtm)) (theta : (fin) (k) -> tm (mty) (mtm)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_tm_tm tau) (upRen_tm_tm xi)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (id) (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Definition up_ren_subst_list_tm_ty { p : nat } { k : nat } { l : nat } { mty : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upList_tm_ty p tau) (upRenList_tm_ty p xi)) x = (upList_tm_ty p theta) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition up_ren_subst_list_tm_tm { p : nat } { k : nat } { l : nat } { mty mtm : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> tm (mty) (mtm)) (theta : (fin) (k) -> tm (mty) (mtm)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upList_tm_tm p tau) (upRenList_tm_tm p xi)) x = (upList_tm_tm p theta) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (_) n) (scons_p_congr (fun z => scons_p_head' (_) (_) z) (fun z => (eq_trans) (scons_p_tail' (_) (_) (xi z)) ((ap) (ren_tm (id) (shift_p p)) (Eq z)))).

Fixpoint compRenSubst_tm { kty ktm : nat } { lty ltm : nat } { mty mtm : nat } (xity : (fin) (mty) -> (fin) (kty)) (xitm : (fin) (mtm) -> (fin) (ktm)) (tauty : (fin) (kty) -> ty (lty)) (tautm : (fin) (ktm) -> tm (lty) (ltm)) (thetaty : (fin) (mty) -> ty (lty)) (thetatm : (fin) (mtm) -> tm (lty) (ltm)) (Eqty : forall x, ((funcomp) tauty xity) x = thetaty x) (Eqtm : forall x, ((funcomp) tautm xitm) x = thetatm x) (s : tm (mty) (mtm)) : subst_tm tauty tautm (ren_tm xity xitm s) = subst_tm thetaty thetatm s :=
    match s return subst_tm tauty tautm (ren_tm xity xitm s) = subst_tm thetaty thetatm s with
    | var_tm (_) (_) s => Eqtm s
    | app (_) (_) s0 s1 => congr_app ((compRenSubst_tm xity xitm tauty tautm thetaty thetatm Eqty Eqtm) s0) ((compRenSubst_tm xity xitm tauty tautm thetaty thetatm Eqty Eqtm) s1)
    | tapp (_) (_) s0 s1 => congr_tapp ((compRenSubst_tm xity xitm tauty tautm thetaty thetatm Eqty Eqtm) s0) ((compRenSubst_ty xity tauty thetaty Eqty) s1)
    | abs (_) (_) s0 s1 => congr_abs ((compRenSubst_ty xity tauty thetaty Eqty) s0) ((compRenSubst_tm (upRen_tm_ty xity) (upRen_tm_tm xitm) (up_tm_ty tauty) (up_tm_tm tautm) (up_tm_ty thetaty) (up_tm_tm thetatm) (up_ren_subst_tm_ty (_) (_) (_) Eqty) (up_ren_subst_tm_tm (_) (_) (_) Eqtm)) s1)
    | tabs (_) (_) s0 s1 => congr_tabs ((compRenSubst_ty xity tauty thetaty Eqty) s0) ((compRenSubst_tm (upRen_ty_ty xity) (upRen_ty_tm xitm) (up_ty_ty tauty) (up_ty_tm tautm) (up_ty_ty thetaty) (up_ty_tm thetatm) (up_ren_subst_ty_ty (_) (_) (_) Eqty) (up_ren_subst_ty_tm (_) (_) (_) Eqtm)) s1)
    | rectm (_) (_) s0 => congr_rectm ((list_comp (prod_comp (fun x => (eq_refl) x) (compRenSubst_tm xity xitm tauty tautm thetaty thetatm Eqty Eqtm))) s0)
    | proj (_) (_) s0 s1 => congr_proj ((compRenSubst_tm xity xitm tauty tautm thetaty thetatm Eqty Eqtm) s0) ((fun x => (eq_refl) x) s1)
    | letpat (_) (_) p s0 s1 s2 s3 => congr_letpat ((compRenSubst_tm xity xitm tauty tautm thetaty thetatm Eqty Eqtm) s0) ((cod_comp (compRenSubst_ty xity tauty thetaty Eqty)) s1) ((cod_comp (list_comp (fun x => (eq_refl) x))) s2) ((compRenSubst_tm (upRenList_tm_ty p xity) (upRenList_tm_tm p xitm) (upList_tm_ty p tauty) (upList_tm_tm p tautm) (upList_tm_ty p thetaty) (upList_tm_tm p thetatm) (up_ren_subst_list_tm_ty (_) (_) (_) Eqty) (up_ren_subst_list_tm_tm (_) (_) (_) Eqtm)) s3)
    end.

Definition up_subst_ren_ty_tm { k : nat } { lty ltm : nat } { mty mtm : nat } (sigma : (fin) (k) -> tm (lty) (ltm)) (zetaty : (fin) (lty) -> (fin) (mty)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (theta : (fin) (k) -> tm (mty) (mtm)) (Eq : forall x, ((funcomp) (ren_tm zetaty zetatm) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRen_ty_ty zetaty) (upRen_ty_tm zetatm)) (up_ty_tm sigma)) x = (up_ty_tm theta) x :=
  fun n => (eq_trans) (compRenRen_tm (shift) (id) (upRen_ty_ty zetaty) (upRen_ty_tm zetatm) ((funcomp) (shift) zetaty) ((funcomp) (id) zetatm) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetaty zetatm (shift) (id) ((funcomp) (shift) zetaty) ((funcomp) (id) zetatm) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_tm (shift) (id)) (Eq n))).

Definition up_subst_ren_tm_ty { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (zetaty : (fin) (lty) -> (fin) (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (ren_ty zetaty) sigma) x = theta x) : forall x, ((funcomp) (ren_ty (upRen_tm_ty zetaty)) (up_tm_ty sigma)) x = (up_tm_ty theta) x :=
  fun n => (eq_trans) (compRenRen_ty (id) (upRen_tm_ty zetaty) ((funcomp) (id) zetaty) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_ty zetaty (id) ((funcomp) (id) zetaty) (fun x => eq_refl) (sigma n))) ((ap) (ren_ty (id)) (Eq n))).

Definition up_subst_ren_tm_tm { k : nat } { lty ltm : nat } { mty mtm : nat } (sigma : (fin) (k) -> tm (lty) (ltm)) (zetaty : (fin) (lty) -> (fin) (mty)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (theta : (fin) (k) -> tm (mty) (mtm)) (Eq : forall x, ((funcomp) (ren_tm zetaty zetatm) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRen_tm_ty zetaty) (upRen_tm_tm zetatm)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_tm (id) (shift) (upRen_tm_ty zetaty) (upRen_tm_tm zetatm) ((funcomp) (id) zetaty) ((funcomp) (shift) zetatm) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetaty zetatm (id) (shift) ((funcomp) (id) zetaty) ((funcomp) (shift) zetatm) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_tm (id) (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Definition up_subst_ren_list_tm_ty { p : nat } { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (zetaty : (fin) (lty) -> (fin) (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (ren_ty zetaty) sigma) x = theta x) : forall x, ((funcomp) (ren_ty (upRenList_tm_ty p zetaty)) (upList_tm_ty p sigma)) x = (upList_tm_ty p theta) x :=
  fun n => (eq_trans) (compRenRen_ty (id) (upRenList_tm_ty p zetaty) ((funcomp) (id) zetaty) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_ty zetaty (id) ((funcomp) (id) zetaty) (fun x => eq_refl) (sigma n))) ((ap) (ren_ty (id)) (Eq n))).

Definition up_subst_ren_list_tm_tm { p : nat } { k : nat } { lty ltm : nat } { mty mtm : nat } (sigma : (fin) (k) -> tm (lty) (ltm)) (zetaty : (fin) (lty) -> (fin) (mty)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (theta : (fin) (k) -> tm (mty) (mtm)) (Eq : forall x, ((funcomp) (ren_tm zetaty zetatm) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRenList_tm_ty p zetaty) (upRenList_tm_tm p zetatm)) (upList_tm_tm p sigma)) x = (upList_tm_tm p theta) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (_) n) (scons_p_congr (fun x => (ap) (var_tm (mty) (p + mtm)) (scons_p_head' (_) (_) x)) (fun n => (eq_trans) (compRenRen_tm (id) (shift_p p) (upRenList_tm_ty p zetaty) (upRenList_tm_tm p zetatm) ((funcomp) (id) zetaty) ((funcomp) (shift_p p) zetatm) (fun x => eq_refl) (fun x => scons_p_tail' (_) (_) x) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetaty zetatm (id) (shift_p p) ((funcomp) (id) zetaty) ((funcomp) (shift_p p) zetatm) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_tm (id) (shift_p p)) (Eq n))))).

Fixpoint compSubstRen_tm { kty ktm : nat } { lty ltm : nat } { mty mtm : nat } (sigmaty : (fin) (mty) -> ty (kty)) (sigmatm : (fin) (mtm) -> tm (kty) (ktm)) (zetaty : (fin) (kty) -> (fin) (lty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (thetaty : (fin) (mty) -> ty (lty)) (thetatm : (fin) (mtm) -> tm (lty) (ltm)) (Eqty : forall x, ((funcomp) (ren_ty zetaty) sigmaty) x = thetaty x) (Eqtm : forall x, ((funcomp) (ren_tm zetaty zetatm) sigmatm) x = thetatm x) (s : tm (mty) (mtm)) : ren_tm zetaty zetatm (subst_tm sigmaty sigmatm s) = subst_tm thetaty thetatm s :=
    match s return ren_tm zetaty zetatm (subst_tm sigmaty sigmatm s) = subst_tm thetaty thetatm s with
    | var_tm (_) (_) s => Eqtm s
    | app (_) (_) s0 s1 => congr_app ((compSubstRen_tm sigmaty sigmatm zetaty zetatm thetaty thetatm Eqty Eqtm) s0) ((compSubstRen_tm sigmaty sigmatm zetaty zetatm thetaty thetatm Eqty Eqtm) s1)
    | tapp (_) (_) s0 s1 => congr_tapp ((compSubstRen_tm sigmaty sigmatm zetaty zetatm thetaty thetatm Eqty Eqtm) s0) ((compSubstRen_ty sigmaty zetaty thetaty Eqty) s1)
    | abs (_) (_) s0 s1 => congr_abs ((compSubstRen_ty sigmaty zetaty thetaty Eqty) s0) ((compSubstRen_tm (up_tm_ty sigmaty) (up_tm_tm sigmatm) (upRen_tm_ty zetaty) (upRen_tm_tm zetatm) (up_tm_ty thetaty) (up_tm_tm thetatm) (up_subst_ren_tm_ty (_) (_) (_) Eqty) (up_subst_ren_tm_tm (_) (_) (_) (_) Eqtm)) s1)
    | tabs (_) (_) s0 s1 => congr_tabs ((compSubstRen_ty sigmaty zetaty thetaty Eqty) s0) ((compSubstRen_tm (up_ty_ty sigmaty) (up_ty_tm sigmatm) (upRen_ty_ty zetaty) (upRen_ty_tm zetatm) (up_ty_ty thetaty) (up_ty_tm thetatm) (up_subst_ren_ty_ty (_) (_) (_) Eqty) (up_subst_ren_ty_tm (_) (_) (_) (_) Eqtm)) s1)
    | rectm (_) (_) s0 => congr_rectm ((list_comp (prod_comp (fun x => (eq_refl) x) (compSubstRen_tm sigmaty sigmatm zetaty zetatm thetaty thetatm Eqty Eqtm))) s0)
    | proj (_) (_) s0 s1 => congr_proj ((compSubstRen_tm sigmaty sigmatm zetaty zetatm thetaty thetatm Eqty Eqtm) s0) ((fun x => (eq_refl) x) s1)
    | letpat (_) (_) p s0 s1 s2 s3 => congr_letpat ((compSubstRen_tm sigmaty sigmatm zetaty zetatm thetaty thetatm Eqty Eqtm) s0) ((cod_comp (compSubstRen_ty sigmaty zetaty thetaty Eqty)) s1) ((cod_comp (list_comp (fun x => (eq_refl) x))) s2) ((compSubstRen_tm (upList_tm_ty p sigmaty) (upList_tm_tm p sigmatm) (upRenList_tm_ty p zetaty) (upRenList_tm_tm p zetatm) (upList_tm_ty p thetaty) (upList_tm_tm p thetatm) (up_subst_ren_list_tm_ty (_) (_) (_) Eqty) (up_subst_ren_list_tm_tm (_) (_) (_) (_) Eqtm)) s3)
    end.

Definition up_subst_subst_ty_tm { k : nat } { lty ltm : nat } { mty mtm : nat } (sigma : (fin) (k) -> tm (lty) (ltm)) (tauty : (fin) (lty) -> ty (mty)) (tautm : (fin) (ltm) -> tm (mty) (mtm)) (theta : (fin) (k) -> tm (mty) (mtm)) (Eq : forall x, ((funcomp) (subst_tm tauty tautm) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (up_ty_ty tauty) (up_ty_tm tautm)) (up_ty_tm sigma)) x = (up_ty_tm theta) x :=
  fun n => (eq_trans) (compRenSubst_tm (shift) (id) (up_ty_ty tauty) (up_ty_tm tautm) ((funcomp) (up_ty_ty tauty) (shift)) ((funcomp) (up_ty_tm tautm) (id)) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tauty tautm (shift) (id) ((funcomp) (ren_ty (shift)) tauty) ((funcomp) (ren_tm (shift) (id)) tautm) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_tm (shift) (id)) (Eq n))).

Definition up_subst_subst_tm_ty { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (tauty : (fin) (lty) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (subst_ty tauty) sigma) x = theta x) : forall x, ((funcomp) (subst_ty (up_tm_ty tauty)) (up_tm_ty sigma)) x = (up_tm_ty theta) x :=
  fun n => (eq_trans) (compRenSubst_ty (id) (up_tm_ty tauty) ((funcomp) (up_tm_ty tauty) (id)) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_ty tauty (id) ((funcomp) (ren_ty (id)) tauty) (fun x => eq_refl) (sigma n))) ((ap) (ren_ty (id)) (Eq n))).

Definition up_subst_subst_tm_tm { k : nat } { lty ltm : nat } { mty mtm : nat } (sigma : (fin) (k) -> tm (lty) (ltm)) (tauty : (fin) (lty) -> ty (mty)) (tautm : (fin) (ltm) -> tm (mty) (mtm)) (theta : (fin) (k) -> tm (mty) (mtm)) (Eq : forall x, ((funcomp) (subst_tm tauty tautm) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (up_tm_ty tauty) (up_tm_tm tautm)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_tm (id) (shift) (up_tm_ty tauty) (up_tm_tm tautm) ((funcomp) (up_tm_ty tauty) (id)) ((funcomp) (up_tm_tm tautm) (shift)) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tauty tautm (id) (shift) ((funcomp) (ren_ty (id)) tauty) ((funcomp) (ren_tm (id) (shift)) tautm) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_tm (id) (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Definition up_subst_subst_list_tm_ty { p : nat } { k : nat } { lty : nat } { mty : nat } (sigma : (fin) (k) -> ty (lty)) (tauty : (fin) (lty) -> ty (mty)) (theta : (fin) (k) -> ty (mty)) (Eq : forall x, ((funcomp) (subst_ty tauty) sigma) x = theta x) : forall x, ((funcomp) (subst_ty (upList_tm_ty p tauty)) (upList_tm_ty p sigma)) x = (upList_tm_ty p theta) x :=
  fun n => (eq_trans) (compRenSubst_ty (id) (upList_tm_ty p tauty) ((funcomp) (upList_tm_ty p tauty) (id)) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_ty tauty (id) (_) (fun x => (eq_sym) (eq_refl)) (sigma n))) ((ap) (ren_ty (id)) (Eq n))).

Definition up_subst_subst_list_tm_tm { p : nat } { k : nat } { lty ltm : nat } { mty mtm : nat } (sigma : (fin) (k) -> tm (lty) (ltm)) (tauty : (fin) (lty) -> ty (mty)) (tautm : (fin) (ltm) -> tm (mty) (mtm)) (theta : (fin) (k) -> tm (mty) (mtm)) (Eq : forall x, ((funcomp) (subst_tm tauty tautm) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (upList_tm_ty p tauty) (upList_tm_tm p tautm)) (upList_tm_tm p sigma)) x = (upList_tm_tm p theta) x :=
  fun n => (eq_trans) (scons_p_comp' ((funcomp) (var_tm (lty) (p + ltm)) (zero_p p)) (_) (_) n) (scons_p_congr (fun x => scons_p_head' (_) (fun z => ren_tm (id) (shift_p p) (_)) x) (fun n => (eq_trans) (compRenSubst_tm (id) (shift_p p) (upList_tm_ty p tauty) (upList_tm_tm p tautm) ((funcomp) (upList_tm_ty p tauty) (id)) ((funcomp) (upList_tm_tm p tautm) (shift_p p)) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tauty tautm (id) (shift_p p) (_) (_) (fun x => (eq_sym) (eq_refl)) (fun x => (eq_sym) (scons_p_tail' (_) (_) x)) (sigma n))) ((ap) (ren_tm (id) (shift_p p)) (Eq n))))).

Fixpoint compSubstSubst_tm { kty ktm : nat } { lty ltm : nat } { mty mtm : nat } (sigmaty : (fin) (mty) -> ty (kty)) (sigmatm : (fin) (mtm) -> tm (kty) (ktm)) (tauty : (fin) (kty) -> ty (lty)) (tautm : (fin) (ktm) -> tm (lty) (ltm)) (thetaty : (fin) (mty) -> ty (lty)) (thetatm : (fin) (mtm) -> tm (lty) (ltm)) (Eqty : forall x, ((funcomp) (subst_ty tauty) sigmaty) x = thetaty x) (Eqtm : forall x, ((funcomp) (subst_tm tauty tautm) sigmatm) x = thetatm x) (s : tm (mty) (mtm)) : subst_tm tauty tautm (subst_tm sigmaty sigmatm s) = subst_tm thetaty thetatm s :=
    match s return subst_tm tauty tautm (subst_tm sigmaty sigmatm s) = subst_tm thetaty thetatm s with
    | var_tm (_) (_) s => Eqtm s
    | app (_) (_) s0 s1 => congr_app ((compSubstSubst_tm sigmaty sigmatm tauty tautm thetaty thetatm Eqty Eqtm) s0) ((compSubstSubst_tm sigmaty sigmatm tauty tautm thetaty thetatm Eqty Eqtm) s1)
    | tapp (_) (_) s0 s1 => congr_tapp ((compSubstSubst_tm sigmaty sigmatm tauty tautm thetaty thetatm Eqty Eqtm) s0) ((compSubstSubst_ty sigmaty tauty thetaty Eqty) s1)
    | abs (_) (_) s0 s1 => congr_abs ((compSubstSubst_ty sigmaty tauty thetaty Eqty) s0) ((compSubstSubst_tm (up_tm_ty sigmaty) (up_tm_tm sigmatm) (up_tm_ty tauty) (up_tm_tm tautm) (up_tm_ty thetaty) (up_tm_tm thetatm) (up_subst_subst_tm_ty (_) (_) (_) Eqty) (up_subst_subst_tm_tm (_) (_) (_) (_) Eqtm)) s1)
    | tabs (_) (_) s0 s1 => congr_tabs ((compSubstSubst_ty sigmaty tauty thetaty Eqty) s0) ((compSubstSubst_tm (up_ty_ty sigmaty) (up_ty_tm sigmatm) (up_ty_ty tauty) (up_ty_tm tautm) (up_ty_ty thetaty) (up_ty_tm thetatm) (up_subst_subst_ty_ty (_) (_) (_) Eqty) (up_subst_subst_ty_tm (_) (_) (_) (_) Eqtm)) s1)
    | rectm (_) (_) s0 => congr_rectm ((list_comp (prod_comp (fun x => (eq_refl) x) (compSubstSubst_tm sigmaty sigmatm tauty tautm thetaty thetatm Eqty Eqtm))) s0)
    | proj (_) (_) s0 s1 => congr_proj ((compSubstSubst_tm sigmaty sigmatm tauty tautm thetaty thetatm Eqty Eqtm) s0) ((fun x => (eq_refl) x) s1)
    | letpat (_) (_) p s0 s1 s2 s3 => congr_letpat ((compSubstSubst_tm sigmaty sigmatm tauty tautm thetaty thetatm Eqty Eqtm) s0) ((cod_comp (compSubstSubst_ty sigmaty tauty thetaty Eqty)) s1) ((cod_comp (list_comp (fun x => (eq_refl) x))) s2) ((compSubstSubst_tm (upList_tm_ty p sigmaty) (upList_tm_tm p sigmatm) (upList_tm_ty p tauty) (upList_tm_tm p tautm) (upList_tm_ty p thetaty) (upList_tm_tm p thetatm) (up_subst_subst_list_tm_ty (_) (_) (_) Eqty) (up_subst_subst_list_tm_tm (_) (_) (_) (_) Eqtm)) s3)
    end.

Definition rinstInst_up_ty_tm { m : nat } { nty ntm : nat } (xi : (fin) (m) -> (fin) (ntm)) (sigma : (fin) (m) -> tm (nty) (ntm)) (Eq : forall x, ((funcomp) (var_tm (nty) (ntm)) xi) x = sigma x) : forall x, ((funcomp) (var_tm ((S) nty) (ntm)) (upRen_ty_tm xi)) x = (up_ty_tm sigma) x :=
  fun n => (ap) (ren_tm (shift) (id)) (Eq n).

Definition rinstInst_up_tm_ty { m : nat } { nty : nat } (xi : (fin) (m) -> (fin) (nty)) (sigma : (fin) (m) -> ty (nty)) (Eq : forall x, ((funcomp) (var_ty (nty)) xi) x = sigma x) : forall x, ((funcomp) (var_ty (nty)) (upRen_tm_ty xi)) x = (up_tm_ty sigma) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition rinstInst_up_tm_tm { m : nat } { nty ntm : nat } (xi : (fin) (m) -> (fin) (ntm)) (sigma : (fin) (m) -> tm (nty) (ntm)) (Eq : forall x, ((funcomp) (var_tm (nty) (ntm)) xi) x = sigma x) : forall x, ((funcomp) (var_tm (nty) ((S) ntm)) (upRen_tm_tm xi)) x = (up_tm_tm sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (id) (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Definition rinstInst_up_list_tm_ty { p : nat } { m : nat } { nty : nat } (xi : (fin) (m) -> (fin) (nty)) (sigma : (fin) (m) -> ty (nty)) (Eq : forall x, ((funcomp) (var_ty (nty)) xi) x = sigma x) : forall x, ((funcomp) (var_ty (nty)) (upRenList_tm_ty p xi)) x = (upList_tm_ty p sigma) x :=
  fun n => (ap) (ren_ty (id)) (Eq n).

Definition rinstInst_up_list_tm_tm { p : nat } { m : nat } { nty ntm : nat } (xi : (fin) (m) -> (fin) (ntm)) (sigma : (fin) (m) -> tm (nty) (ntm)) (Eq : forall x, ((funcomp) (var_tm (nty) (ntm)) xi) x = sigma x) : forall x, ((funcomp) (var_tm (nty) (p + ntm)) (upRenList_tm_tm p xi)) x = (upList_tm_tm p sigma) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (var_tm (nty) (p + ntm)) n) (scons_p_congr (fun z => eq_refl) (fun n => (ap) (ren_tm (id) (shift_p p)) (Eq n))).

Fixpoint rinst_inst_tm { mty mtm : nat } { nty ntm : nat } (xity : (fin) (mty) -> (fin) (nty)) (xitm : (fin) (mtm) -> (fin) (ntm)) (sigmaty : (fin) (mty) -> ty (nty)) (sigmatm : (fin) (mtm) -> tm (nty) (ntm)) (Eqty : forall x, ((funcomp) (var_ty (nty)) xity) x = sigmaty x) (Eqtm : forall x, ((funcomp) (var_tm (nty) (ntm)) xitm) x = sigmatm x) (s : tm (mty) (mtm)) : ren_tm xity xitm s = subst_tm sigmaty sigmatm s :=
    match s return ren_tm xity xitm s = subst_tm sigmaty sigmatm s with
    | var_tm (_) (_) s => Eqtm s
    | app (_) (_) s0 s1 => congr_app ((rinst_inst_tm xity xitm sigmaty sigmatm Eqty Eqtm) s0) ((rinst_inst_tm xity xitm sigmaty sigmatm Eqty Eqtm) s1)
    | tapp (_) (_) s0 s1 => congr_tapp ((rinst_inst_tm xity xitm sigmaty sigmatm Eqty Eqtm) s0) ((rinst_inst_ty xity sigmaty Eqty) s1)
    | abs (_) (_) s0 s1 => congr_abs ((rinst_inst_ty xity sigmaty Eqty) s0) ((rinst_inst_tm (upRen_tm_ty xity) (upRen_tm_tm xitm) (up_tm_ty sigmaty) (up_tm_tm sigmatm) (rinstInst_up_tm_ty (_) (_) Eqty) (rinstInst_up_tm_tm (_) (_) Eqtm)) s1)
    | tabs (_) (_) s0 s1 => congr_tabs ((rinst_inst_ty xity sigmaty Eqty) s0) ((rinst_inst_tm (upRen_ty_ty xity) (upRen_ty_tm xitm) (up_ty_ty sigmaty) (up_ty_tm sigmatm) (rinstInst_up_ty_ty (_) (_) Eqty) (rinstInst_up_ty_tm (_) (_) Eqtm)) s1)
    | rectm (_) (_) s0 => congr_rectm ((list_ext (prod_ext (fun x => (eq_refl) x) (rinst_inst_tm xity xitm sigmaty sigmatm Eqty Eqtm))) s0)
    | proj (_) (_) s0 s1 => congr_proj ((rinst_inst_tm xity xitm sigmaty sigmatm Eqty Eqtm) s0) ((fun x => (eq_refl) x) s1)
    | letpat (_) (_) p s0 s1 s2 s3 => congr_letpat ((rinst_inst_tm xity xitm sigmaty sigmatm Eqty Eqtm) s0) ((cod_ext (rinst_inst_ty xity sigmaty Eqty)) s1) ((cod_ext (list_ext (fun x => (eq_refl) x))) s2) ((rinst_inst_tm (upRenList_tm_ty p xity) (upRenList_tm_tm p xitm) (upList_tm_ty p sigmaty) (upList_tm_tm p sigmatm) (rinstInst_up_list_tm_ty (_) (_) Eqty) (rinstInst_up_list_tm_tm (_) (_) Eqtm)) s3)
    end.

Lemma rinstInst_tm { mty mtm : nat } { nty ntm : nat } (xity : (fin) (mty) -> (fin) (nty)) (xitm : (fin) (mtm) -> (fin) (ntm)) : ren_tm xity xitm = subst_tm ((funcomp) (var_ty (nty)) xity) ((funcomp) (var_tm (nty) (ntm)) xitm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_tm xity xitm (_) (_) (fun n => eq_refl) (fun n => eq_refl) x)). Qed.

Lemma instId_tm { mty mtm : nat } : subst_tm (var_ty (mty)) (var_tm (mty) (mtm)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_tm (var_ty (mty)) (var_tm (mty) (mtm)) (fun n => eq_refl) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_tm { mty mtm : nat } : @ren_tm (mty) (mtm) (mty) (mtm) (id) (id) = id .
Proof. exact ((eq_trans) (rinstInst_tm ((id) (_)) ((id) (_))) instId_tm). Qed.

Lemma varL_tm { mty mtm : nat } { nty ntm : nat } (sigmaty : (fin) (mty) -> ty (nty)) (sigmatm : (fin) (mtm) -> tm (nty) (ntm)) : (funcomp) (subst_tm sigmaty sigmatm) (var_tm (mty) (mtm)) = sigmatm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_tm { mty mtm : nat } { nty ntm : nat } (xity : (fin) (mty) -> (fin) (nty)) (xitm : (fin) (mtm) -> (fin) (ntm)) : (funcomp) (ren_tm xity xitm) (var_tm (mty) (mtm)) = (funcomp) (var_tm (nty) (ntm)) xitm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_tm { kty ktm : nat } { lty ltm : nat } { mty mtm : nat } (sigmaty : (fin) (mty) -> ty (kty)) (sigmatm : (fin) (mtm) -> tm (kty) (ktm)) (tauty : (fin) (kty) -> ty (lty)) (tautm : (fin) (ktm) -> tm (lty) (ltm)) (s : tm (mty) (mtm)) : subst_tm tauty tautm (subst_tm sigmaty sigmatm s) = subst_tm ((funcomp) (subst_ty tauty) sigmaty) ((funcomp) (subst_tm tauty tautm) sigmatm) s .
Proof. exact (compSubstSubst_tm sigmaty sigmatm tauty tautm (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compComp'_tm { kty ktm : nat } { lty ltm : nat } { mty mtm : nat } (sigmaty : (fin) (mty) -> ty (kty)) (sigmatm : (fin) (mtm) -> tm (kty) (ktm)) (tauty : (fin) (kty) -> ty (lty)) (tautm : (fin) (ktm) -> tm (lty) (ltm)) : (funcomp) (subst_tm tauty tautm) (subst_tm sigmaty sigmatm) = subst_tm ((funcomp) (subst_ty tauty) sigmaty) ((funcomp) (subst_tm tauty tautm) sigmatm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_tm sigmaty sigmatm tauty tautm n)). Qed.

Lemma compRen_tm { kty ktm : nat } { lty ltm : nat } { mty mtm : nat } (sigmaty : (fin) (mty) -> ty (kty)) (sigmatm : (fin) (mtm) -> tm (kty) (ktm)) (zetaty : (fin) (kty) -> (fin) (lty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (s : tm (mty) (mtm)) : ren_tm zetaty zetatm (subst_tm sigmaty sigmatm s) = subst_tm ((funcomp) (ren_ty zetaty) sigmaty) ((funcomp) (ren_tm zetaty zetatm) sigmatm) s .
Proof. exact (compSubstRen_tm sigmaty sigmatm zetaty zetatm (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compRen'_tm { kty ktm : nat } { lty ltm : nat } { mty mtm : nat } (sigmaty : (fin) (mty) -> ty (kty)) (sigmatm : (fin) (mtm) -> tm (kty) (ktm)) (zetaty : (fin) (kty) -> (fin) (lty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) : (funcomp) (ren_tm zetaty zetatm) (subst_tm sigmaty sigmatm) = subst_tm ((funcomp) (ren_ty zetaty) sigmaty) ((funcomp) (ren_tm zetaty zetatm) sigmatm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_tm sigmaty sigmatm zetaty zetatm n)). Qed.

Lemma renComp_tm { kty ktm : nat } { lty ltm : nat } { mty mtm : nat } (xity : (fin) (mty) -> (fin) (kty)) (xitm : (fin) (mtm) -> (fin) (ktm)) (tauty : (fin) (kty) -> ty (lty)) (tautm : (fin) (ktm) -> tm (lty) (ltm)) (s : tm (mty) (mtm)) : subst_tm tauty tautm (ren_tm xity xitm s) = subst_tm ((funcomp) tauty xity) ((funcomp) tautm xitm) s .
Proof. exact (compRenSubst_tm xity xitm tauty tautm (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renComp'_tm { kty ktm : nat } { lty ltm : nat } { mty mtm : nat } (xity : (fin) (mty) -> (fin) (kty)) (xitm : (fin) (mtm) -> (fin) (ktm)) (tauty : (fin) (kty) -> ty (lty)) (tautm : (fin) (ktm) -> tm (lty) (ltm)) : (funcomp) (subst_tm tauty tautm) (ren_tm xity xitm) = subst_tm ((funcomp) tauty xity) ((funcomp) tautm xitm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_tm xity xitm tauty tautm n)). Qed.

Lemma renRen_tm { kty ktm : nat } { lty ltm : nat } { mty mtm : nat } (xity : (fin) (mty) -> (fin) (kty)) (xitm : (fin) (mtm) -> (fin) (ktm)) (zetaty : (fin) (kty) -> (fin) (lty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (s : tm (mty) (mtm)) : ren_tm zetaty zetatm (ren_tm xity xitm s) = ren_tm ((funcomp) zetaty xity) ((funcomp) zetatm xitm) s .
Proof. exact (compRenRen_tm xity xitm zetaty zetatm (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renRen'_tm { kty ktm : nat } { lty ltm : nat } { mty mtm : nat } (xity : (fin) (mty) -> (fin) (kty)) (xitm : (fin) (mtm) -> (fin) (ktm)) (zetaty : (fin) (kty) -> (fin) (lty)) (zetatm : (fin) (ktm) -> (fin) (ltm)) : (funcomp) (ren_tm zetaty zetatm) (ren_tm xity xitm) = ren_tm ((funcomp) zetaty xity) ((funcomp) zetatm xitm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_tm xity xitm zetaty zetatm n)). Qed.

End tm.

Arguments var_ty {nty}.

Arguments top {nty}.

Arguments arr {nty}.

Arguments all {nty}.

Arguments recty {nty}.

Arguments var_tm {nty} {ntm}.

Arguments app {nty} {ntm}.

Arguments tapp {nty} {ntm}.

Arguments abs {nty} {ntm}.

Arguments tabs {nty} {ntm}.

Arguments rectm {nty} {ntm}.

Arguments proj {nty} {ntm}.

Arguments letpat {nty} {ntm}.

Global Instance Subst_ty { mty : nat } { nty : nat } : Subst1 ((fin) (mty) -> ty (nty)) (ty (mty)) (ty (nty)) := @subst_ty (mty) (nty) .

Global Instance Subst_tm { mty mtm : nat } { nty ntm : nat } : Subst2 ((fin) (mty) -> ty (nty)) ((fin) (mtm) -> tm (nty) (ntm)) (tm (mty) (mtm)) (tm (nty) (ntm)) := @subst_tm (mty) (mtm) (nty) (ntm) .

Global Instance Ren_ty { mty : nat } { nty : nat } : Ren1 ((fin) (mty) -> (fin) (nty)) (ty (mty)) (ty (nty)) := @ren_ty (mty) (nty) .

Global Instance Ren_tm { mty mtm : nat } { nty ntm : nat } : Ren2 ((fin) (mty) -> (fin) (nty)) ((fin) (mtm) -> (fin) (ntm)) (tm (mty) (mtm)) (tm (nty) (ntm)) := @ren_tm (mty) (mtm) (nty) (ntm) .

Global Instance VarInstance_ty { mty : nat } : Var ((fin) (mty)) (ty (mty)) := @var_ty (mty) .

Notation "x '__ty'" := (var_ty x) (at level 5, format "x __ty") : subst_scope.

Notation "x '__ty'" := (@ids (_) (_) VarInstance_ty x) (at level 5, only printing, format "x __ty") : subst_scope.

Notation "'var'" := (var_ty) (only printing, at level 1) : subst_scope.

Global Instance VarInstance_tm { mty mtm : nat } : Var ((fin) (mtm)) (tm (mty) (mtm)) := @var_tm (mty) (mtm) .

Notation "x '__tm'" := (var_tm x) (at level 5, format "x __tm") : subst_scope.

Notation "x '__tm'" := (@ids (_) (_) VarInstance_tm x) (at level 5, only printing, format "x __tm") : subst_scope.

Notation "'var'" := (var_tm) (only printing, at level 1) : subst_scope.

Class Up_ty X Y := up_ty : X -> Y.

Notation "↑__ty" := (up_ty) (only printing) : subst_scope.

Class Up_tm X Y := up_tm : X -> Y.

Notation "↑__tm" := (up_tm) (only printing) : subst_scope.

Notation "↑__ty" := (up_ty_ty) (only printing) : subst_scope.

Global Instance Up_ty_ty { m : nat } { nty : nat } : Up_ty (_) (_) := @up_ty_ty (m) (nty) .

Notation "↑__tm" := (up_tm_ty) (only printing) : subst_scope.

Global Instance Up_tm_ty { m : nat } { nty : nat } : Up_ty (_) (_) := @up_tm_ty (m) (nty) .

Notation "↑__tm" := (up_tm_tm) (only printing) : subst_scope.

Global Instance Up_tm_tm { m : nat } { nty ntm : nat } : Up_tm (_) (_) := @up_tm_tm (m) (nty) (ntm) .

Notation "↑__ty" := (up_ty_tm) (only printing) : subst_scope.

Global Instance Up_ty_tm { m : nat } { nty ntm : nat } : Up_tm (_) (_) := @up_ty_tm (m) (nty) (ntm) .

Notation "s [ sigmaty ]" := (subst_ty sigmaty s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaty ]" := (subst_ty sigmaty) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xity ⟩" := (ren_ty xity s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xity ⟩" := (ren_ty xity) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaty ; sigmatm ]" := (subst_tm sigmaty sigmatm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaty ; sigmatm ]" := (subst_tm sigmaty sigmatm) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xity ; xitm ⟩" := (ren_tm xity xitm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xity ; xitm ⟩" := (ren_tm xity xitm) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_ty,  Subst_tm,  Ren_ty,  Ren_tm,  VarInstance_ty,  VarInstance_tm.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_ty,  Subst_tm,  Ren_ty,  Ren_tm,  VarInstance_ty,  VarInstance_tm in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_ty| progress rewrite ?compComp_ty| progress rewrite ?compComp'_ty| progress rewrite ?instId_tm| progress rewrite ?compComp_tm| progress rewrite ?compComp'_tm| progress rewrite ?rinstId_ty| progress rewrite ?compRen_ty| progress rewrite ?compRen'_ty| progress rewrite ?renComp_ty| progress rewrite ?renComp'_ty| progress rewrite ?renRen_ty| progress rewrite ?renRen'_ty| progress rewrite ?rinstId_tm| progress rewrite ?compRen_tm| progress rewrite ?compRen'_tm| progress rewrite ?renComp_tm| progress rewrite ?renComp'_tm| progress rewrite ?renRen_tm| progress rewrite ?renRen'_tm| progress rewrite ?varL_ty| progress rewrite ?varL_tm| progress rewrite ?varLRen_ty| progress rewrite ?varLRen_tm| progress (unfold up_ren, upRen_ty_ty, upRen_tm_ty, upRen_tm_tm, upRen_ty_tm, upRenList_tm_ty, upRenList_tm_tm, up_ty_ty, up_tm_ty, up_tm_tm, up_ty_tm, upList_tm_ty, upList_tm_tm)| progress (cbn [subst_ty subst_tm ren_ty ren_tm])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_ty in *| progress rewrite ?compComp_ty in *| progress rewrite ?compComp'_ty in *| progress rewrite ?instId_tm in *| progress rewrite ?compComp_tm in *| progress rewrite ?compComp'_tm in *| progress rewrite ?rinstId_ty in *| progress rewrite ?compRen_ty in *| progress rewrite ?compRen'_ty in *| progress rewrite ?renComp_ty in *| progress rewrite ?renComp'_ty in *| progress rewrite ?renRen_ty in *| progress rewrite ?renRen'_ty in *| progress rewrite ?rinstId_tm in *| progress rewrite ?compRen_tm in *| progress rewrite ?compRen'_tm in *| progress rewrite ?renComp_tm in *| progress rewrite ?renComp'_tm in *| progress rewrite ?renRen_tm in *| progress rewrite ?renRen'_tm in *| progress rewrite ?varL_ty in *| progress rewrite ?varL_tm in *| progress rewrite ?varLRen_ty in *| progress rewrite ?varLRen_tm in *| progress (unfold up_ren, upRen_ty_ty, upRen_tm_ty, upRen_tm_tm, upRen_ty_tm, upRenList_tm_ty, upRenList_tm_tm, up_ty_ty, up_tm_ty, up_tm_tm, up_ty_tm, upList_tm_ty, upList_tm_tm in *)| progress (cbn [subst_ty subst_tm ren_ty ren_tm] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_ty); try repeat (erewrite rinstInst_tm).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_ty); try repeat (erewrite <- rinstInst_tm).

(** as_apply follows **)

Ltac  musigma gexp hexp :=
  match   gexp  with
  |  ?s  =>  unify   (gexp) (hexp)
  |  arr (subst_ty ?sigma0 ?s0) (subst_ty ?sigma0 ?s1)  =>  first [ unify   (subst_ty sigma0 (arr s0 s1)) (hexp)|  musigma   (subst_ty sigma0 (arr s0 s1)) (hexp) ]
  |  all (subst_ty ?sigma0 ?s0) (subst_ty ((scons) (var_ty (var_zero)) ((funcomp) (ren_ty (shift)) ?sigma0)) ?s1)  =>  first [ unify   (subst_ty sigma0 (all s0 s1)) (hexp)|  musigma   (subst_ty sigma0 (all s0 s1)) (hexp) ]
  |  recty (list_map (prod_map (fun x => x) (subst_ty ?sigma0)) ?s0)  =>  first [ unify   (subst_ty sigma0 (recty s0)) (hexp)|  musigma   (subst_ty sigma0 (recty s0)) (hexp) ]
  |  arr (ren_ty ?sigma0 ?s0) (ren_ty ?sigma0 ?s1)  =>  first [ unify   (ren_ty sigma0 (arr s0 s1)) (hexp)|  musigma   (ren_ty sigma0 (arr s0 s1)) (hexp) ]
  |  all (ren_ty ?sigma0 ?s0) (ren_ty ((scons) (var_zero) ((funcomp) (shift) ?sigma0)) ?s1)  =>  first [ unify   (ren_ty sigma0 (all s0 s1)) (hexp)|  musigma   (ren_ty sigma0 (all s0 s1)) (hexp) ]
  |  recty (list_map (prod_map (fun x => x) (ren_ty ?sigma0)) ?s0)  =>  first [ unify   (ren_ty sigma0 (recty s0)) (hexp)|  musigma   (ren_ty sigma0 (recty s0)) (hexp) ]
  |  app (subst_tm ?sigma1 ?sigma0 ?s0) (subst_tm ?sigma1 ?sigma0 ?s1)  =>  first [ unify   (subst_tm sigma0 sigma1 (app s0 s1)) (hexp)|  musigma   (subst_tm sigma0 sigma1 (app s0 s1)) (hexp) ]
  |  tapp (subst_tm ?sigma1 ?sigma0 ?s0) (subst_ty ?sigma0 ?s1)  =>  first [ unify   (subst_tm sigma0 sigma1 (tapp s0 s1)) (hexp)|  musigma   (subst_tm sigma0 sigma1 (tapp s0 s1)) (hexp) ]
  |  abs (subst_ty ?sigma0 ?s0) (subst_tm ((scons) (var_tm (var_zero)) ((funcomp) (ren_tm (id) (shift)) ?sigma1)) ?sigma0 ?s1)  =>  first [ unify   (subst_tm sigma0 sigma1 (abs s0 s1)) (hexp)|  musigma   (subst_tm sigma0 sigma1 (abs s0 s1)) (hexp) ]
  |  tabs (subst_ty ?sigma0 ?s0) (subst_tm ((funcomp) (ren_tm (shift) (id)) ?sigma1) ((scons) (var_ty (var_zero)) ((funcomp) (ren_ty (shift)) ?sigma0)) ?s1)  =>  first [ unify   (subst_tm sigma0 sigma1 (tabs s0 s1)) (hexp)|  musigma   (subst_tm sigma0 sigma1 (tabs s0 s1)) (hexp) ]
  |  rectm (list_map (prod_map (fun x => x) (subst_tm ?sigma1 ?sigma0)) ?s0)  =>  first [ unify   (subst_tm sigma0 sigma1 (rectm s0)) (hexp)|  musigma   (subst_tm sigma0 sigma1 (rectm s0)) (hexp) ]
  |  proj (subst_tm ?sigma1 ?sigma0 ?s0) ((fun x => x) ?s1)  =>  first [ unify   (subst_tm sigma0 sigma1 (proj s0 s1)) (hexp)|  musigma   (subst_tm sigma0 sigma1 (proj s0 s1)) (hexp) ]
  |  letpat ?p (subst_tm ?sigma1 ?sigma0 ?s0) (cod_map (subst_ty ?sigma0) ?s1) (cod_map (list_map (fun x => x)) ?s2) (subst_tm (scons_p ?p ((funcomp) var_tm (zero_p ?p)) ((funcomp) (ren_tm (id) (shift_p ?p)) ?sigma1)) ?sigma0 ?s3)  =>  first [ unify   (subst_tm sigma0 sigma1 (letpat p s0 s1 s2 s3)) (hexp)|  musigma   (subst_tm sigma0 sigma1 (letpat p s0 s1 s2 s3)) (hexp) ]
  |  app (ren_tm ?sigma1 ?sigma0 ?s0) (ren_tm ?sigma1 ?sigma0 ?s1)  =>  first [ unify   (ren_tm sigma0 sigma1 (app s0 s1)) (hexp)|  musigma   (ren_tm sigma0 sigma1 (app s0 s1)) (hexp) ]
  |  tapp (ren_tm ?sigma1 ?sigma0 ?s0) (ren_ty ?sigma0 ?s1)  =>  first [ unify   (ren_tm sigma0 sigma1 (tapp s0 s1)) (hexp)|  musigma   (ren_tm sigma0 sigma1 (tapp s0 s1)) (hexp) ]
  |  abs (ren_ty ?sigma0 ?s0) (ren_tm ((scons) (var_zero) ((funcomp) (shift) ?sigma1)) ?sigma0 ?s1)  =>  first [ unify   (ren_tm sigma0 sigma1 (abs s0 s1)) (hexp)|  musigma   (ren_tm sigma0 sigma1 (abs s0 s1)) (hexp) ]
  |  tabs (ren_ty ?sigma0 ?s0) (ren_tm ?sigma1 ((scons) (var_zero) ((funcomp) (shift) ?sigma0)) ?s1)  =>  first [ unify   (ren_tm sigma0 sigma1 (tabs s0 s1)) (hexp)|  musigma   (ren_tm sigma0 sigma1 (tabs s0 s1)) (hexp) ]
  |  rectm (list_map (prod_map (fun x => x) (ren_tm ?sigma1 ?sigma0)) ?s0)  =>  first [ unify   (ren_tm sigma0 sigma1 (rectm s0)) (hexp)|  musigma   (ren_tm sigma0 sigma1 (rectm s0)) (hexp) ]
  |  proj (ren_tm ?sigma1 ?sigma0 ?s0) ((fun x => x) ?s1)  =>  first [ unify   (ren_tm sigma0 sigma1 (proj s0 s1)) (hexp)|  musigma   (ren_tm sigma0 sigma1 (proj s0 s1)) (hexp) ]
  |  letpat ?p (ren_tm ?sigma1 ?sigma0 ?s0) (cod_map (ren_ty ?sigma0) ?s1) (cod_map (list_map (fun x => x)) ?s2) (ren_tm (scons_p ?p (zero_p ?p) ((funcomp) (shift_p ?p) ?sigma1)) ?sigma0 ?s3)  =>  first [ unify   (ren_tm sigma0 sigma1 (letpat p s0 s1 s2 s3)) (hexp)|  musigma   (ren_tm sigma0 sigma1 (letpat p s0 s1 s2 s3)) (hexp) ]
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
  |  ren_tm ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1) ?s  =>  match   hexp  with
  |  ren_tm ?theta0 ?theta1 ?t  =>  first [ unify   (ren_tm tau0 tau1 (ren_tm sigma0 sigma1 s)) (hexp)|  musigma   (ren_tm tau0 tau1 (ren_tm sigma0 sigma1 s)) (hexp) ]
  end
  |  subst_tm ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1) ?s  =>  match   hexp  with
  |  subst_tm ?theta0 ?theta1 ?t  =>  first [ unify   (subst_tm tau0 tau1 (ren_tm sigma0 sigma1 s)) (hexp)|  musigma   (subst_tm tau0 tau1 (ren_tm sigma0 sigma1 s)) (hexp) ]
  end
  |  subst_tm ((funcomp) (ren_ty ?tau0) ?sigma0) ((funcomp) (ren_tm ?tau0 ?tau1) ?sigma1) ?s  =>  match   hexp  with
  |  ren_tm ?theta0 ?theta1 ?t  =>  first [ unify   (ren_tm tau0 tau1 (subst_tm sigma0 sigma1 s)) (hexp)|  musigma   (ren_tm tau0 tau1 (subst_tm sigma0 sigma1 s)) (hexp) ]
  end
  |  subst_tm ((funcomp) (subst_ty ?tau0) ?sigma0) ((funcomp) (subst_tm ?tau0 ?tau1) ?sigma1) ?s  =>  match   hexp  with
  |  subst_tm ?theta0 ?theta1 ?t  =>  first [ unify   (subst_tm tau0 tau1 (subst_tm sigma0 sigma1 s)) (hexp)|  musigma   (subst_tm tau0 tau1 (subst_tm sigma0 sigma1 s)) (hexp) ]
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
  |  (funcomp) (ren_tm ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_tm ?theta0 ?theta1) ?sigmat  =>  first [ unify   ((funcomp) (ren_tm tau0 tau1) ((funcomp) (ren_tm sigma0 sigma1) sigmas)) (hexp)|  musigma   ((funcomp) (ren_tm tau0 tau1) ((funcomp) (ren_tm sigma0 sigma1) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_tm ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_tm ?theta0 ?theta1) ?sigmat  =>  first [ unify   ((funcomp) (subst_tm tau0 tau1) ((funcomp) (ren_tm sigma0 sigma1) sigmas)) (hexp)|  musigma   ((funcomp) (subst_tm tau0 tau1) ((funcomp) (ren_tm sigma0 sigma1) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_tm ((funcomp) (ren_ty ?tau0) ?sigma0) ((funcomp) (ren_tm ?tau0 ?tau1) ?sigma1)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_tm ?theta0 ?theta1) ?sigmat  =>  first [ unify   ((funcomp) (ren_tm tau0 tau1) ((funcomp) (subst_tm sigma0 sigma1) sigmas)) (hexp)|  musigma   ((funcomp) (ren_tm tau0 tau1) ((funcomp) (subst_tm sigma0 sigma1) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_tm ((funcomp) (subst_ty ?tau0) ?sigma0) ((funcomp) (subst_tm ?tau0 ?tau1) ?sigma1)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_tm ?theta0 ?theta1) ?sigmat  =>  first [ unify   ((funcomp) (subst_tm tau0 tau1) ((funcomp) (subst_tm sigma0 sigma1) sigmas)) (hexp)|  musigma   ((funcomp) (subst_tm tau0 tau1) ((funcomp) (subst_tm sigma0 sigma1) sigmas)) (hexp) ]
  end
  |  (scons) (ren_ty ?sigma0 ?s) ((funcomp) (ren_ty ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (ren_ty ?tau0) ?thetah  =>  first [ unify   ((funcomp) (ren_ty sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (ren_ty sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (subst_ty ?sigma0 ?s) ((funcomp) (subst_ty ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (subst_ty ?tau0) ?thetah  =>  first [ unify   ((funcomp) (subst_ty sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (subst_ty sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (ren_tm ?sigma0 ?sigma1 ?s) ((funcomp) (ren_tm ?sigma0 ?sigma1) ?thetag)  =>  match   hexp  with
  |  (funcomp) (ren_tm ?tau0 ?tau1) ?thetah  =>  first [ unify   ((funcomp) (ren_tm sigma0 sigma1) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (ren_tm sigma0 sigma1) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (subst_tm ?sigma0 ?sigma1 ?s) ((funcomp) (subst_tm ?sigma0 ?sigma1) ?thetag)  =>  match   hexp  with
  |  (funcomp) (subst_tm ?tau0 ?tau1) ?thetah  =>  first [ unify   ((funcomp) (subst_tm sigma0 sigma1) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (subst_tm sigma0 sigma1) ((scons) s thetag)) (hexp) ]
  end
  |  arr ?s0 ?s1  =>  match   hexp  with
  |  arr ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  all ?s0 ?s1  =>  match   hexp  with
  |  all ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  recty ?s0  =>  match   hexp  with
  |  recty ?t0  =>  musigma   (s0) (t0)
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
  |  abs ?s0 ?s1  =>  match   hexp  with
  |  abs ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  tabs ?s0 ?s1  =>  match   hexp  with
  |  tabs ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  rectm ?s0  =>  match   hexp  with
  |  rectm ?t0  =>  musigma   (s0) (t0)
  end
  |  proj ?s0 ?s1  =>  match   hexp  with
  |  proj ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  letpat ?p ?s0 ?s1 ?s2 ?s3  =>  match   hexp  with
  |  letpat ?p_ ?t0 ?t1 ?t2 ?t3  =>  musigma   (p) (p_); musigma   (s0) (t0); musigma   (s1) (t1); musigma   (s2) (t2); musigma   (s3) (t3)
  end
  |  subst_tm ?sigma0 ?sigma1 ?s  =>  match   hexp  with
  |  subst_tm ?tau0 ?tau1 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1)
  end
  |  ren_tm ?sigma0 ?sigma1 ?s  =>  match   hexp  with
  |  ren_tm ?tau0 ?tau1 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1)
  end
  |  (funcomp) (subst_tm ?sigma0 ?sigma1) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_tm ?tau0 ?tau1) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1)
  end
  |  (funcomp) (ren_tm ?sigma0 ?sigma1) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_tm ?tau0 ?tau1) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1)
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
  |  (funcomp) (subst_tm ((funcomp) var_ty ?sigma0) ((funcomp) var_tm ?sigma1)) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_tm ?tau0 ?tau1) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (subst_tm ((funcomp) var_ty sigma0) ((funcomp) var_tm sigma1)) sigma = (funcomp) (ren_tm sigma0 sigma1) sigma) as eq by (renamify; reflexivity); rewrite   (eq); unify   ((funcomp) (ren_tm sigma0 sigma1) sigma) (hexp); clear eq
  end
  |  subst_tm ((funcomp) var_ty ?sigma0) ((funcomp) var_tm ?sigma1) ?s  =>  match   hexp  with
  |  ren_tm ?tau0 ?tau1 ?t  =>  let eq := fresh "eq" in
  assert (subst_tm ((funcomp) var_ty sigma0) ((funcomp) var_tm sigma1) s = ren_tm sigma0 sigma1 s) as eq by (renamify; reflexivity); rewrite   (eq); unify   (ren_tm sigma0 sigma1 s) (hexp); clear eq
  end
  |  (funcomp) (ren_ty ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_ty ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_ty sigma0) sigma = (funcomp) (subst_ty ((funcomp) var_ty sigma0)) sigma) as eq by (substify; reflexivity); rewrite   (eq); unify   ((funcomp) (subst_ty ((funcomp) var_ty sigma0)) sigma) (hexp); clear eq
  end
  |  ren_ty ?sigma0 ?s  =>  match   hexp  with
  |  subst_ty ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (ren_ty sigma0 s = subst_ty ((funcomp) var_ty sigma0) s) as eq by (substify; reflexivity); rewrite   (eq); unify   (subst_ty ((funcomp) var_ty sigma0) s) (hexp); clear eq
  end
  |  (funcomp) (ren_tm ?sigma0 ?sigma1) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_tm ?tau0 ?tau1) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_tm sigma0 sigma1) sigma = (funcomp) (subst_tm ((funcomp) var_ty sigma0) ((funcomp) var_tm sigma1)) sigma) as eq by (substify; reflexivity); rewrite   (eq); unify   ((funcomp) (subst_tm ((funcomp) var_ty sigma0) ((funcomp) var_tm sigma1)) sigma) (hexp); clear eq
  end
  |  ren_tm ?sigma0 ?sigma1 ?s  =>  match   hexp  with
  |  subst_tm ?tau0 ?tau1 ?t  =>  let eq := fresh "eq" in
  assert (ren_tm sigma0 sigma1 s = subst_tm ((funcomp) var_ty sigma0) ((funcomp) var_tm sigma1) s) as eq by (substify; reflexivity); rewrite   (eq); unify   (subst_tm ((funcomp) var_ty sigma0) ((funcomp) var_tm sigma1) s) (hexp); clear eq
  end
  |  ?s  =>  musigma   (gexp) (hexp)
  |  subst_ty ((scons) ?sty0 ((funcomp) var_ty ?sigmaty)) ?sty  =>  match   hexp  with
  |  subst_ty ((scons) ?tty0 var_ty) ?tty  =>  unify   (subst_ty ((scons) sty0 var_ty) (ren_ty ((scons) (var_zero) ((funcomp) (shift) sigmaty)) sty)) (hexp)
  end
  |  subst_ty ((scons) ?sty0 ?sigmaty) ?sty  =>  match   hexp  with
  |  subst_ty ((scons) ?tty0 var_ty) ?tty  =>  unify   (subst_ty ((scons) sty0 var_ty) (subst_ty ((scons) (var_ty (var_zero)) ((funcomp) (ren_ty (shift)) sigmaty)) sty)) (hexp)
  end
  |  subst_tm ((funcomp) var_ty ?sigmaty) ((scons) ?stm0 ((funcomp) var_tm ?sigmatm)) ?stm  =>  match   hexp  with
  |  subst_tm var_ty ((scons) ?ttm0 var_tm) ?ttm  =>  unify   (subst_tm var_ty ((scons) stm0 var_tm) (ren_tm sigmaty ((scons) (var_zero) ((funcomp) (shift) sigmatm)) stm)) (hexp)
  end
  |  subst_tm ((scons) ?sty0 ((funcomp) var_ty ?sigmaty)) ((funcomp) var_tm ?sigmatm) ?stm  =>  match   hexp  with
  |  subst_tm ((scons) ?tty0 var_ty) var_tm ?ttm  =>  unify   (subst_tm ((scons) sty0 var_ty) var_tm (ren_tm ((scons) (var_zero) ((funcomp) (shift) sigmaty)) sigmatm stm)) (hexp)
  end
  |  subst_tm ((funcomp) var_ty ?sigmaty) (scons_p ?p ?stm0 ((funcomp) var_tm ?sigmatm)) ?stm  =>  match   hexp  with
  |  subst_tm var_ty (scons_p ?p_ ?ttm0 var_tm) ?ttm  =>  unify   (subst_tm var_ty (scons_p p stm0 var_tm) (ren_tm sigmaty (scons_p p (zero_p p) ((funcomp) (shift_p p) sigmatm)) stm)) (hexp)
  end
  |  subst_tm ?sigmaty ((scons) ?stm0 ?sigmatm) ?stm  =>  match   hexp  with
  |  subst_tm var_ty ((scons) ?ttm0 var_tm) ?ttm  =>  unify   (subst_tm var_ty ((scons) stm0 var_tm) (subst_tm sigmaty ((scons) (var_tm (var_zero)) ((funcomp) (ren_tm (id) (shift)) sigmatm)) stm)) (hexp)
  end
  |  subst_tm ((scons) ?sty0 ?sigmaty) ?sigmatm ?stm  =>  match   hexp  with
  |  subst_tm ((scons) ?tty0 var_ty) var_tm ?ttm  =>  unify   (subst_tm ((scons) sty0 var_ty) var_tm (subst_tm ((scons) (var_ty (var_zero)) ((funcomp) (ren_ty (shift)) sigmaty)) ((funcomp) (ren_tm (shift) (id)) sigmatm) stm)) (hexp)
  end
  |  subst_tm ?sigmaty (scons_p ?p ?stm0 ?sigmatm) ?stm  =>  match   hexp  with
  |  subst_tm var_ty (scons_p ?p_ ?ttm0 var_tm) ?ttm  =>  unify   (subst_tm var_ty (scons_p p stm0 var_tm) (subst_tm sigmaty (scons_p p ((funcomp) var_tm (zero_p p)) ((funcomp) (ren_tm (id) (shift_p p)) sigmatm)) stm)) (hexp)
  end
  |  ?s  =>  match   hexp  with
  |  subst_ty ?sigma0 ?t  =>  unify   (subst_ty var_ty s) (hexp)
  |  ren_ty ?sigma0 ?t  =>  unify   (ren_ty (id) s) (hexp)
  |  subst_tm ?sigma0 ?sigma1 ?t  =>  unify   (subst_tm var_ty var_tm s) (hexp)
  |  ren_tm ?sigma0 ?sigma1 ?t  =>  unify   (ren_tm (id) (id) s) (hexp)
  end
  |  arr ?s0 ?s1  =>  match   hexp  with
  |  arr ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  all ?s0 ?s1  =>  match   hexp  with
  |  all ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  recty ?s0  =>  match   hexp  with
  |  recty ?t0  =>  heuristics   (s0) (t0)
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
  |  abs ?s0 ?s1  =>  match   hexp  with
  |  abs ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  tabs ?s0 ?s1  =>  match   hexp  with
  |  tabs ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  rectm ?s0  =>  match   hexp  with
  |  rectm ?t0  =>  heuristics   (s0) (t0)
  end
  |  proj ?s0 ?s1  =>  match   hexp  with
  |  proj ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  letpat ?p ?s0 ?s1 ?s2 ?s3  =>  match   hexp  with
  |  letpat ?p_ ?t0 ?t1 ?t2 ?t3  =>  heuristics   (p) (p_); heuristics   (s0) (t0); heuristics   (s1) (t1); heuristics   (s2) (t2); heuristics   (s3) (t3)
  end
  |  subst_tm ?sigma0 ?sigma1 ?s  =>  match   hexp  with
  |  subst_tm ?tau0 ?tau1 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1)
  end
  |  ren_tm ?sigma0 ?sigma1 ?s  =>  match   hexp  with
  |  ren_tm ?tau0 ?tau1 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1)
  end
  |  (funcomp) (subst_tm ?sigma0 ?sigma1) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_tm ?tau0 ?tau1) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1)
  end
  |  (funcomp) (ren_tm ?sigma0 ?sigma1) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_tm ?tau0 ?tau1) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1)
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
