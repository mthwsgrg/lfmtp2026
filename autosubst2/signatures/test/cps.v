Require Export fintype.



Section typ.
Inductive typ  : Type :=
  | imp : typ   -> typ   -> typ 
  | and : typ   -> typ   -> typ 
  | unit : typ .

Lemma congr_imp  { s0 : typ   } { s1 : typ   } { t0 : typ   } { t1 : typ   } (H1 : s0 = t0) (H2 : s1 = t1) : imp s0 s1 = imp t0 t1 .
Proof. congruence. Qed.

Lemma congr_and  { s0 : typ   } { s1 : typ   } { t0 : typ   } { t1 : typ   } (H1 : s0 = t0) (H2 : s1 = t1) : and s0 s1 = and t0 t1 .
Proof. congruence. Qed.

Lemma congr_unit  : unit  = unit  .
Proof. congruence. Qed.

End typ.

Section expval.
Inductive exp (nval : nat) : Type :=
  | value : val  (nval) -> exp (nval)
  | app : exp  (nval) -> exp  (nval) -> exp (nval)
  | mkpair : exp  (nval) -> exp  (nval) -> exp (nval)
  | fst : exp  (nval) -> exp (nval)
  | snd : exp  (nval) -> exp (nval)
  | letC : exp  (nval) -> exp  ((S) nval) -> exp (nval)
 with val (nval : nat) : Type :=
  | var_val : (fin) (nval) -> val (nval)
  | lam : exp  ((S) nval) -> val (nval)
  | pair : val  (nval) -> val  (nval) -> val (nval)
  | one : val (nval).

Lemma congr_value { mval : nat } { s0 : val  (mval) } { t0 : val  (mval) } (H1 : s0 = t0) : value (mval) s0 = value (mval) t0 .
Proof. congruence. Qed.

Lemma congr_app { mval : nat } { s0 : exp  (mval) } { s1 : exp  (mval) } { t0 : exp  (mval) } { t1 : exp  (mval) } (H1 : s0 = t0) (H2 : s1 = t1) : app (mval) s0 s1 = app (mval) t0 t1 .
Proof. congruence. Qed.

Lemma congr_mkpair { mval : nat } { s0 : exp  (mval) } { s1 : exp  (mval) } { t0 : exp  (mval) } { t1 : exp  (mval) } (H1 : s0 = t0) (H2 : s1 = t1) : mkpair (mval) s0 s1 = mkpair (mval) t0 t1 .
Proof. congruence. Qed.

Lemma congr_fst { mval : nat } { s0 : exp  (mval) } { t0 : exp  (mval) } (H1 : s0 = t0) : fst (mval) s0 = fst (mval) t0 .
Proof. congruence. Qed.

Lemma congr_snd { mval : nat } { s0 : exp  (mval) } { t0 : exp  (mval) } (H1 : s0 = t0) : snd (mval) s0 = snd (mval) t0 .
Proof. congruence. Qed.

Lemma congr_letC { mval : nat } { s0 : exp  (mval) } { s1 : exp  ((S) mval) } { t0 : exp  (mval) } { t1 : exp  ((S) mval) } (H1 : s0 = t0) (H2 : s1 = t1) : letC (mval) s0 s1 = letC (mval) t0 t1 .
Proof. congruence. Qed.

Lemma congr_lam { mval : nat } { s0 : exp  ((S) mval) } { t0 : exp  ((S) mval) } (H1 : s0 = t0) : lam (mval) s0 = lam (mval) t0 .
Proof. congruence. Qed.

Lemma congr_pair { mval : nat } { s0 : val  (mval) } { s1 : val  (mval) } { t0 : val  (mval) } { t1 : val  (mval) } (H1 : s0 = t0) (H2 : s1 = t1) : pair (mval) s0 s1 = pair (mval) t0 t1 .
Proof. congruence. Qed.

Lemma congr_one { mval : nat } : one (mval) = one (mval) .
Proof. congruence. Qed.

Definition upRen_val_val { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Fixpoint ren_exp { mval : nat } { nval : nat } (xival : (fin) (mval) -> (fin) (nval)) (s : exp (mval)) : exp (nval) :=
    match s return exp (nval) with
    | value (_) s0 => value (nval) ((ren_val xival) s0)
    | app (_) s0 s1 => app (nval) ((ren_exp xival) s0) ((ren_exp xival) s1)
    | mkpair (_) s0 s1 => mkpair (nval) ((ren_exp xival) s0) ((ren_exp xival) s1)
    | fst (_) s0 => fst (nval) ((ren_exp xival) s0)
    | snd (_) s0 => snd (nval) ((ren_exp xival) s0)
    | letC (_) s0 s1 => letC (nval) ((ren_exp xival) s0) ((ren_exp (upRen_val_val xival)) s1)
    end
 with ren_val { mval : nat } { nval : nat } (xival : (fin) (mval) -> (fin) (nval)) (s : val (mval)) : val (nval) :=
    match s return val (nval) with
    | var_val (_) s => (var_val (nval)) (xival s)
    | lam (_) s0 => lam (nval) ((ren_exp (upRen_val_val xival)) s0)
    | pair (_) s0 s1 => pair (nval) ((ren_val xival) s0) ((ren_val xival) s1)
    | one (_)  => one (nval)
    end.

Definition up_val_val { m : nat } { nval : nat } (sigma : (fin) (m) -> val (nval)) : (fin) ((S) (m)) -> val ((S) nval) :=
  (scons) ((var_val ((S) nval)) (var_zero)) ((funcomp) (ren_val (shift)) sigma).

Fixpoint subst_exp { mval : nat } { nval : nat } (sigmaval : (fin) (mval) -> val (nval)) (s : exp (mval)) : exp (nval) :=
    match s return exp (nval) with
    | value (_) s0 => value (nval) ((subst_val sigmaval) s0)
    | app (_) s0 s1 => app (nval) ((subst_exp sigmaval) s0) ((subst_exp sigmaval) s1)
    | mkpair (_) s0 s1 => mkpair (nval) ((subst_exp sigmaval) s0) ((subst_exp sigmaval) s1)
    | fst (_) s0 => fst (nval) ((subst_exp sigmaval) s0)
    | snd (_) s0 => snd (nval) ((subst_exp sigmaval) s0)
    | letC (_) s0 s1 => letC (nval) ((subst_exp sigmaval) s0) ((subst_exp (up_val_val sigmaval)) s1)
    end
 with subst_val { mval : nat } { nval : nat } (sigmaval : (fin) (mval) -> val (nval)) (s : val (mval)) : val (nval) :=
    match s return val (nval) with
    | var_val (_) s => sigmaval s
    | lam (_) s0 => lam (nval) ((subst_exp (up_val_val sigmaval)) s0)
    | pair (_) s0 s1 => pair (nval) ((subst_val sigmaval) s0) ((subst_val sigmaval) s1)
    | one (_)  => one (nval)
    end.

Definition upId_val_val { mval : nat } (sigma : (fin) (mval) -> val (mval)) (Eq : forall x, sigma x = (var_val (mval)) x) : forall x, (up_val_val sigma) x = (var_val ((S) mval)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_val (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint idSubst_exp { mval : nat } (sigmaval : (fin) (mval) -> val (mval)) (Eqval : forall x, sigmaval x = (var_val (mval)) x) (s : exp (mval)) : subst_exp sigmaval s = s :=
    match s return subst_exp sigmaval s = s with
    | value (_) s0 => congr_value ((idSubst_val sigmaval Eqval) s0)
    | app (_) s0 s1 => congr_app ((idSubst_exp sigmaval Eqval) s0) ((idSubst_exp sigmaval Eqval) s1)
    | mkpair (_) s0 s1 => congr_mkpair ((idSubst_exp sigmaval Eqval) s0) ((idSubst_exp sigmaval Eqval) s1)
    | fst (_) s0 => congr_fst ((idSubst_exp sigmaval Eqval) s0)
    | snd (_) s0 => congr_snd ((idSubst_exp sigmaval Eqval) s0)
    | letC (_) s0 s1 => congr_letC ((idSubst_exp sigmaval Eqval) s0) ((idSubst_exp (up_val_val sigmaval) (upId_val_val (_) Eqval)) s1)
    end
 with idSubst_val { mval : nat } (sigmaval : (fin) (mval) -> val (mval)) (Eqval : forall x, sigmaval x = (var_val (mval)) x) (s : val (mval)) : subst_val sigmaval s = s :=
    match s return subst_val sigmaval s = s with
    | var_val (_) s => Eqval s
    | lam (_) s0 => congr_lam ((idSubst_exp (up_val_val sigmaval) (upId_val_val (_) Eqval)) s0)
    | pair (_) s0 s1 => congr_pair ((idSubst_val sigmaval Eqval) s0) ((idSubst_val sigmaval Eqval) s1)
    | one (_)  => congr_one 
    end.

Definition upExtRen_val_val { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_val_val xi) x = (upRen_val_val zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint extRen_exp { mval : nat } { nval : nat } (xival : (fin) (mval) -> (fin) (nval)) (zetaval : (fin) (mval) -> (fin) (nval)) (Eqval : forall x, xival x = zetaval x) (s : exp (mval)) : ren_exp xival s = ren_exp zetaval s :=
    match s return ren_exp xival s = ren_exp zetaval s with
    | value (_) s0 => congr_value ((extRen_val xival zetaval Eqval) s0)
    | app (_) s0 s1 => congr_app ((extRen_exp xival zetaval Eqval) s0) ((extRen_exp xival zetaval Eqval) s1)
    | mkpair (_) s0 s1 => congr_mkpair ((extRen_exp xival zetaval Eqval) s0) ((extRen_exp xival zetaval Eqval) s1)
    | fst (_) s0 => congr_fst ((extRen_exp xival zetaval Eqval) s0)
    | snd (_) s0 => congr_snd ((extRen_exp xival zetaval Eqval) s0)
    | letC (_) s0 s1 => congr_letC ((extRen_exp xival zetaval Eqval) s0) ((extRen_exp (upRen_val_val xival) (upRen_val_val zetaval) (upExtRen_val_val (_) (_) Eqval)) s1)
    end
 with extRen_val { mval : nat } { nval : nat } (xival : (fin) (mval) -> (fin) (nval)) (zetaval : (fin) (mval) -> (fin) (nval)) (Eqval : forall x, xival x = zetaval x) (s : val (mval)) : ren_val xival s = ren_val zetaval s :=
    match s return ren_val xival s = ren_val zetaval s with
    | var_val (_) s => (ap) (var_val (nval)) (Eqval s)
    | lam (_) s0 => congr_lam ((extRen_exp (upRen_val_val xival) (upRen_val_val zetaval) (upExtRen_val_val (_) (_) Eqval)) s0)
    | pair (_) s0 s1 => congr_pair ((extRen_val xival zetaval Eqval) s0) ((extRen_val xival zetaval Eqval) s1)
    | one (_)  => congr_one 
    end.

Definition upExt_val_val { m : nat } { nval : nat } (sigma : (fin) (m) -> val (nval)) (tau : (fin) (m) -> val (nval)) (Eq : forall x, sigma x = tau x) : forall x, (up_val_val sigma) x = (up_val_val tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_val (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint ext_exp { mval : nat } { nval : nat } (sigmaval : (fin) (mval) -> val (nval)) (tauval : (fin) (mval) -> val (nval)) (Eqval : forall x, sigmaval x = tauval x) (s : exp (mval)) : subst_exp sigmaval s = subst_exp tauval s :=
    match s return subst_exp sigmaval s = subst_exp tauval s with
    | value (_) s0 => congr_value ((ext_val sigmaval tauval Eqval) s0)
    | app (_) s0 s1 => congr_app ((ext_exp sigmaval tauval Eqval) s0) ((ext_exp sigmaval tauval Eqval) s1)
    | mkpair (_) s0 s1 => congr_mkpair ((ext_exp sigmaval tauval Eqval) s0) ((ext_exp sigmaval tauval Eqval) s1)
    | fst (_) s0 => congr_fst ((ext_exp sigmaval tauval Eqval) s0)
    | snd (_) s0 => congr_snd ((ext_exp sigmaval tauval Eqval) s0)
    | letC (_) s0 s1 => congr_letC ((ext_exp sigmaval tauval Eqval) s0) ((ext_exp (up_val_val sigmaval) (up_val_val tauval) (upExt_val_val (_) (_) Eqval)) s1)
    end
 with ext_val { mval : nat } { nval : nat } (sigmaval : (fin) (mval) -> val (nval)) (tauval : (fin) (mval) -> val (nval)) (Eqval : forall x, sigmaval x = tauval x) (s : val (mval)) : subst_val sigmaval s = subst_val tauval s :=
    match s return subst_val sigmaval s = subst_val tauval s with
    | var_val (_) s => Eqval s
    | lam (_) s0 => congr_lam ((ext_exp (up_val_val sigmaval) (up_val_val tauval) (upExt_val_val (_) (_) Eqval)) s0)
    | pair (_) s0 s1 => congr_pair ((ext_val sigmaval tauval Eqval) s0) ((ext_val sigmaval tauval Eqval) s1)
    | one (_)  => congr_one 
    end.

Definition up_ren_ren_val_val { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_val_val tau) (upRen_val_val xi)) x = (upRen_val_val theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_exp { kval : nat } { lval : nat } { mval : nat } (xival : (fin) (mval) -> (fin) (kval)) (zetaval : (fin) (kval) -> (fin) (lval)) (rhoval : (fin) (mval) -> (fin) (lval)) (Eqval : forall x, ((funcomp) zetaval xival) x = rhoval x) (s : exp (mval)) : ren_exp zetaval (ren_exp xival s) = ren_exp rhoval s :=
    match s return ren_exp zetaval (ren_exp xival s) = ren_exp rhoval s with
    | value (_) s0 => congr_value ((compRenRen_val xival zetaval rhoval Eqval) s0)
    | app (_) s0 s1 => congr_app ((compRenRen_exp xival zetaval rhoval Eqval) s0) ((compRenRen_exp xival zetaval rhoval Eqval) s1)
    | mkpair (_) s0 s1 => congr_mkpair ((compRenRen_exp xival zetaval rhoval Eqval) s0) ((compRenRen_exp xival zetaval rhoval Eqval) s1)
    | fst (_) s0 => congr_fst ((compRenRen_exp xival zetaval rhoval Eqval) s0)
    | snd (_) s0 => congr_snd ((compRenRen_exp xival zetaval rhoval Eqval) s0)
    | letC (_) s0 s1 => congr_letC ((compRenRen_exp xival zetaval rhoval Eqval) s0) ((compRenRen_exp (upRen_val_val xival) (upRen_val_val zetaval) (upRen_val_val rhoval) (up_ren_ren (_) (_) (_) Eqval)) s1)
    end
 with compRenRen_val { kval : nat } { lval : nat } { mval : nat } (xival : (fin) (mval) -> (fin) (kval)) (zetaval : (fin) (kval) -> (fin) (lval)) (rhoval : (fin) (mval) -> (fin) (lval)) (Eqval : forall x, ((funcomp) zetaval xival) x = rhoval x) (s : val (mval)) : ren_val zetaval (ren_val xival s) = ren_val rhoval s :=
    match s return ren_val zetaval (ren_val xival s) = ren_val rhoval s with
    | var_val (_) s => (ap) (var_val (lval)) (Eqval s)
    | lam (_) s0 => congr_lam ((compRenRen_exp (upRen_val_val xival) (upRen_val_val zetaval) (upRen_val_val rhoval) (up_ren_ren (_) (_) (_) Eqval)) s0)
    | pair (_) s0 s1 => congr_pair ((compRenRen_val xival zetaval rhoval Eqval) s0) ((compRenRen_val xival zetaval rhoval Eqval) s1)
    | one (_)  => congr_one 
    end.

Definition up_ren_subst_val_val { k : nat } { l : nat } { mval : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> val (mval)) (theta : (fin) (k) -> val (mval)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_val_val tau) (upRen_val_val xi)) x = (up_val_val theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_val (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint compRenSubst_exp { kval : nat } { lval : nat } { mval : nat } (xival : (fin) (mval) -> (fin) (kval)) (tauval : (fin) (kval) -> val (lval)) (thetaval : (fin) (mval) -> val (lval)) (Eqval : forall x, ((funcomp) tauval xival) x = thetaval x) (s : exp (mval)) : subst_exp tauval (ren_exp xival s) = subst_exp thetaval s :=
    match s return subst_exp tauval (ren_exp xival s) = subst_exp thetaval s with
    | value (_) s0 => congr_value ((compRenSubst_val xival tauval thetaval Eqval) s0)
    | app (_) s0 s1 => congr_app ((compRenSubst_exp xival tauval thetaval Eqval) s0) ((compRenSubst_exp xival tauval thetaval Eqval) s1)
    | mkpair (_) s0 s1 => congr_mkpair ((compRenSubst_exp xival tauval thetaval Eqval) s0) ((compRenSubst_exp xival tauval thetaval Eqval) s1)
    | fst (_) s0 => congr_fst ((compRenSubst_exp xival tauval thetaval Eqval) s0)
    | snd (_) s0 => congr_snd ((compRenSubst_exp xival tauval thetaval Eqval) s0)
    | letC (_) s0 s1 => congr_letC ((compRenSubst_exp xival tauval thetaval Eqval) s0) ((compRenSubst_exp (upRen_val_val xival) (up_val_val tauval) (up_val_val thetaval) (up_ren_subst_val_val (_) (_) (_) Eqval)) s1)
    end
 with compRenSubst_val { kval : nat } { lval : nat } { mval : nat } (xival : (fin) (mval) -> (fin) (kval)) (tauval : (fin) (kval) -> val (lval)) (thetaval : (fin) (mval) -> val (lval)) (Eqval : forall x, ((funcomp) tauval xival) x = thetaval x) (s : val (mval)) : subst_val tauval (ren_val xival s) = subst_val thetaval s :=
    match s return subst_val tauval (ren_val xival s) = subst_val thetaval s with
    | var_val (_) s => Eqval s
    | lam (_) s0 => congr_lam ((compRenSubst_exp (upRen_val_val xival) (up_val_val tauval) (up_val_val thetaval) (up_ren_subst_val_val (_) (_) (_) Eqval)) s0)
    | pair (_) s0 s1 => congr_pair ((compRenSubst_val xival tauval thetaval Eqval) s0) ((compRenSubst_val xival tauval thetaval Eqval) s1)
    | one (_)  => congr_one 
    end.

Definition up_subst_ren_val_val { k : nat } { lval : nat } { mval : nat } (sigma : (fin) (k) -> val (lval)) (zetaval : (fin) (lval) -> (fin) (mval)) (theta : (fin) (k) -> val (mval)) (Eq : forall x, ((funcomp) (ren_val zetaval) sigma) x = theta x) : forall x, ((funcomp) (ren_val (upRen_val_val zetaval)) (up_val_val sigma)) x = (up_val_val theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_val (shift) (upRen_val_val zetaval) ((funcomp) (shift) zetaval) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_val zetaval (shift) ((funcomp) (shift) zetaval) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_val (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstRen_exp { kval : nat } { lval : nat } { mval : nat } (sigmaval : (fin) (mval) -> val (kval)) (zetaval : (fin) (kval) -> (fin) (lval)) (thetaval : (fin) (mval) -> val (lval)) (Eqval : forall x, ((funcomp) (ren_val zetaval) sigmaval) x = thetaval x) (s : exp (mval)) : ren_exp zetaval (subst_exp sigmaval s) = subst_exp thetaval s :=
    match s return ren_exp zetaval (subst_exp sigmaval s) = subst_exp thetaval s with
    | value (_) s0 => congr_value ((compSubstRen_val sigmaval zetaval thetaval Eqval) s0)
    | app (_) s0 s1 => congr_app ((compSubstRen_exp sigmaval zetaval thetaval Eqval) s0) ((compSubstRen_exp sigmaval zetaval thetaval Eqval) s1)
    | mkpair (_) s0 s1 => congr_mkpair ((compSubstRen_exp sigmaval zetaval thetaval Eqval) s0) ((compSubstRen_exp sigmaval zetaval thetaval Eqval) s1)
    | fst (_) s0 => congr_fst ((compSubstRen_exp sigmaval zetaval thetaval Eqval) s0)
    | snd (_) s0 => congr_snd ((compSubstRen_exp sigmaval zetaval thetaval Eqval) s0)
    | letC (_) s0 s1 => congr_letC ((compSubstRen_exp sigmaval zetaval thetaval Eqval) s0) ((compSubstRen_exp (up_val_val sigmaval) (upRen_val_val zetaval) (up_val_val thetaval) (up_subst_ren_val_val (_) (_) (_) Eqval)) s1)
    end
 with compSubstRen_val { kval : nat } { lval : nat } { mval : nat } (sigmaval : (fin) (mval) -> val (kval)) (zetaval : (fin) (kval) -> (fin) (lval)) (thetaval : (fin) (mval) -> val (lval)) (Eqval : forall x, ((funcomp) (ren_val zetaval) sigmaval) x = thetaval x) (s : val (mval)) : ren_val zetaval (subst_val sigmaval s) = subst_val thetaval s :=
    match s return ren_val zetaval (subst_val sigmaval s) = subst_val thetaval s with
    | var_val (_) s => Eqval s
    | lam (_) s0 => congr_lam ((compSubstRen_exp (up_val_val sigmaval) (upRen_val_val zetaval) (up_val_val thetaval) (up_subst_ren_val_val (_) (_) (_) Eqval)) s0)
    | pair (_) s0 s1 => congr_pair ((compSubstRen_val sigmaval zetaval thetaval Eqval) s0) ((compSubstRen_val sigmaval zetaval thetaval Eqval) s1)
    | one (_)  => congr_one 
    end.

Definition up_subst_subst_val_val { k : nat } { lval : nat } { mval : nat } (sigma : (fin) (k) -> val (lval)) (tauval : (fin) (lval) -> val (mval)) (theta : (fin) (k) -> val (mval)) (Eq : forall x, ((funcomp) (subst_val tauval) sigma) x = theta x) : forall x, ((funcomp) (subst_val (up_val_val tauval)) (up_val_val sigma)) x = (up_val_val theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_val (shift) (up_val_val tauval) ((funcomp) (up_val_val tauval) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_val tauval (shift) ((funcomp) (ren_val (shift)) tauval) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_val (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstSubst_exp { kval : nat } { lval : nat } { mval : nat } (sigmaval : (fin) (mval) -> val (kval)) (tauval : (fin) (kval) -> val (lval)) (thetaval : (fin) (mval) -> val (lval)) (Eqval : forall x, ((funcomp) (subst_val tauval) sigmaval) x = thetaval x) (s : exp (mval)) : subst_exp tauval (subst_exp sigmaval s) = subst_exp thetaval s :=
    match s return subst_exp tauval (subst_exp sigmaval s) = subst_exp thetaval s with
    | value (_) s0 => congr_value ((compSubstSubst_val sigmaval tauval thetaval Eqval) s0)
    | app (_) s0 s1 => congr_app ((compSubstSubst_exp sigmaval tauval thetaval Eqval) s0) ((compSubstSubst_exp sigmaval tauval thetaval Eqval) s1)
    | mkpair (_) s0 s1 => congr_mkpair ((compSubstSubst_exp sigmaval tauval thetaval Eqval) s0) ((compSubstSubst_exp sigmaval tauval thetaval Eqval) s1)
    | fst (_) s0 => congr_fst ((compSubstSubst_exp sigmaval tauval thetaval Eqval) s0)
    | snd (_) s0 => congr_snd ((compSubstSubst_exp sigmaval tauval thetaval Eqval) s0)
    | letC (_) s0 s1 => congr_letC ((compSubstSubst_exp sigmaval tauval thetaval Eqval) s0) ((compSubstSubst_exp (up_val_val sigmaval) (up_val_val tauval) (up_val_val thetaval) (up_subst_subst_val_val (_) (_) (_) Eqval)) s1)
    end
 with compSubstSubst_val { kval : nat } { lval : nat } { mval : nat } (sigmaval : (fin) (mval) -> val (kval)) (tauval : (fin) (kval) -> val (lval)) (thetaval : (fin) (mval) -> val (lval)) (Eqval : forall x, ((funcomp) (subst_val tauval) sigmaval) x = thetaval x) (s : val (mval)) : subst_val tauval (subst_val sigmaval s) = subst_val thetaval s :=
    match s return subst_val tauval (subst_val sigmaval s) = subst_val thetaval s with
    | var_val (_) s => Eqval s
    | lam (_) s0 => congr_lam ((compSubstSubst_exp (up_val_val sigmaval) (up_val_val tauval) (up_val_val thetaval) (up_subst_subst_val_val (_) (_) (_) Eqval)) s0)
    | pair (_) s0 s1 => congr_pair ((compSubstSubst_val sigmaval tauval thetaval Eqval) s0) ((compSubstSubst_val sigmaval tauval thetaval Eqval) s1)
    | one (_)  => congr_one 
    end.

Definition rinstInst_up_val_val { m : nat } { nval : nat } (xi : (fin) (m) -> (fin) (nval)) (sigma : (fin) (m) -> val (nval)) (Eq : forall x, ((funcomp) (var_val (nval)) xi) x = sigma x) : forall x, ((funcomp) (var_val ((S) nval)) (upRen_val_val xi)) x = (up_val_val sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_val (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint rinst_inst_exp { mval : nat } { nval : nat } (xival : (fin) (mval) -> (fin) (nval)) (sigmaval : (fin) (mval) -> val (nval)) (Eqval : forall x, ((funcomp) (var_val (nval)) xival) x = sigmaval x) (s : exp (mval)) : ren_exp xival s = subst_exp sigmaval s :=
    match s return ren_exp xival s = subst_exp sigmaval s with
    | value (_) s0 => congr_value ((rinst_inst_val xival sigmaval Eqval) s0)
    | app (_) s0 s1 => congr_app ((rinst_inst_exp xival sigmaval Eqval) s0) ((rinst_inst_exp xival sigmaval Eqval) s1)
    | mkpair (_) s0 s1 => congr_mkpair ((rinst_inst_exp xival sigmaval Eqval) s0) ((rinst_inst_exp xival sigmaval Eqval) s1)
    | fst (_) s0 => congr_fst ((rinst_inst_exp xival sigmaval Eqval) s0)
    | snd (_) s0 => congr_snd ((rinst_inst_exp xival sigmaval Eqval) s0)
    | letC (_) s0 s1 => congr_letC ((rinst_inst_exp xival sigmaval Eqval) s0) ((rinst_inst_exp (upRen_val_val xival) (up_val_val sigmaval) (rinstInst_up_val_val (_) (_) Eqval)) s1)
    end
 with rinst_inst_val { mval : nat } { nval : nat } (xival : (fin) (mval) -> (fin) (nval)) (sigmaval : (fin) (mval) -> val (nval)) (Eqval : forall x, ((funcomp) (var_val (nval)) xival) x = sigmaval x) (s : val (mval)) : ren_val xival s = subst_val sigmaval s :=
    match s return ren_val xival s = subst_val sigmaval s with
    | var_val (_) s => Eqval s
    | lam (_) s0 => congr_lam ((rinst_inst_exp (upRen_val_val xival) (up_val_val sigmaval) (rinstInst_up_val_val (_) (_) Eqval)) s0)
    | pair (_) s0 s1 => congr_pair ((rinst_inst_val xival sigmaval Eqval) s0) ((rinst_inst_val xival sigmaval Eqval) s1)
    | one (_)  => congr_one 
    end.

Lemma rinstInst_exp { mval : nat } { nval : nat } (xival : (fin) (mval) -> (fin) (nval)) : ren_exp xival = subst_exp ((funcomp) (var_val (nval)) xival) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_exp xival (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_val { mval : nat } { nval : nat } (xival : (fin) (mval) -> (fin) (nval)) : ren_val xival = subst_val ((funcomp) (var_val (nval)) xival) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_val xival (_) (fun n => eq_refl) x)). Qed.

Lemma instId_exp { mval : nat } : subst_exp (var_val (mval)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_exp (var_val (mval)) (fun n => eq_refl) ((id) x))). Qed.

Lemma instId_val { mval : nat } : subst_val (var_val (mval)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_val (var_val (mval)) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_exp { mval : nat } : @ren_exp (mval) (mval) (id) = id .
Proof. exact ((eq_trans) (rinstInst_exp ((id) (_))) instId_exp). Qed.

Lemma rinstId_val { mval : nat } : @ren_val (mval) (mval) (id) = id .
Proof. exact ((eq_trans) (rinstInst_val ((id) (_))) instId_val). Qed.

Lemma varL_val { mval : nat } { nval : nat } (sigmaval : (fin) (mval) -> val (nval)) : (funcomp) (subst_val sigmaval) (var_val (mval)) = sigmaval .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_val { mval : nat } { nval : nat } (xival : (fin) (mval) -> (fin) (nval)) : (funcomp) (ren_val xival) (var_val (mval)) = (funcomp) (var_val (nval)) xival .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_exp { kval : nat } { lval : nat } { mval : nat } (sigmaval : (fin) (mval) -> val (kval)) (tauval : (fin) (kval) -> val (lval)) (s : exp (mval)) : subst_exp tauval (subst_exp sigmaval s) = subst_exp ((funcomp) (subst_val tauval) sigmaval) s .
Proof. exact (compSubstSubst_exp sigmaval tauval (_) (fun n => eq_refl) s). Qed.

Lemma compComp_val { kval : nat } { lval : nat } { mval : nat } (sigmaval : (fin) (mval) -> val (kval)) (tauval : (fin) (kval) -> val (lval)) (s : val (mval)) : subst_val tauval (subst_val sigmaval s) = subst_val ((funcomp) (subst_val tauval) sigmaval) s .
Proof. exact (compSubstSubst_val sigmaval tauval (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_exp { kval : nat } { lval : nat } { mval : nat } (sigmaval : (fin) (mval) -> val (kval)) (tauval : (fin) (kval) -> val (lval)) : (funcomp) (subst_exp tauval) (subst_exp sigmaval) = subst_exp ((funcomp) (subst_val tauval) sigmaval) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_exp sigmaval tauval n)). Qed.

Lemma compComp'_val { kval : nat } { lval : nat } { mval : nat } (sigmaval : (fin) (mval) -> val (kval)) (tauval : (fin) (kval) -> val (lval)) : (funcomp) (subst_val tauval) (subst_val sigmaval) = subst_val ((funcomp) (subst_val tauval) sigmaval) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_val sigmaval tauval n)). Qed.

Lemma compRen_exp { kval : nat } { lval : nat } { mval : nat } (sigmaval : (fin) (mval) -> val (kval)) (zetaval : (fin) (kval) -> (fin) (lval)) (s : exp (mval)) : ren_exp zetaval (subst_exp sigmaval s) = subst_exp ((funcomp) (ren_val zetaval) sigmaval) s .
Proof. exact (compSubstRen_exp sigmaval zetaval (_) (fun n => eq_refl) s). Qed.

Lemma compRen_val { kval : nat } { lval : nat } { mval : nat } (sigmaval : (fin) (mval) -> val (kval)) (zetaval : (fin) (kval) -> (fin) (lval)) (s : val (mval)) : ren_val zetaval (subst_val sigmaval s) = subst_val ((funcomp) (ren_val zetaval) sigmaval) s .
Proof. exact (compSubstRen_val sigmaval zetaval (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_exp { kval : nat } { lval : nat } { mval : nat } (sigmaval : (fin) (mval) -> val (kval)) (zetaval : (fin) (kval) -> (fin) (lval)) : (funcomp) (ren_exp zetaval) (subst_exp sigmaval) = subst_exp ((funcomp) (ren_val zetaval) sigmaval) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_exp sigmaval zetaval n)). Qed.

Lemma compRen'_val { kval : nat } { lval : nat } { mval : nat } (sigmaval : (fin) (mval) -> val (kval)) (zetaval : (fin) (kval) -> (fin) (lval)) : (funcomp) (ren_val zetaval) (subst_val sigmaval) = subst_val ((funcomp) (ren_val zetaval) sigmaval) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_val sigmaval zetaval n)). Qed.

Lemma renComp_exp { kval : nat } { lval : nat } { mval : nat } (xival : (fin) (mval) -> (fin) (kval)) (tauval : (fin) (kval) -> val (lval)) (s : exp (mval)) : subst_exp tauval (ren_exp xival s) = subst_exp ((funcomp) tauval xival) s .
Proof. exact (compRenSubst_exp xival tauval (_) (fun n => eq_refl) s). Qed.

Lemma renComp_val { kval : nat } { lval : nat } { mval : nat } (xival : (fin) (mval) -> (fin) (kval)) (tauval : (fin) (kval) -> val (lval)) (s : val (mval)) : subst_val tauval (ren_val xival s) = subst_val ((funcomp) tauval xival) s .
Proof. exact (compRenSubst_val xival tauval (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_exp { kval : nat } { lval : nat } { mval : nat } (xival : (fin) (mval) -> (fin) (kval)) (tauval : (fin) (kval) -> val (lval)) : (funcomp) (subst_exp tauval) (ren_exp xival) = subst_exp ((funcomp) tauval xival) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_exp xival tauval n)). Qed.

Lemma renComp'_val { kval : nat } { lval : nat } { mval : nat } (xival : (fin) (mval) -> (fin) (kval)) (tauval : (fin) (kval) -> val (lval)) : (funcomp) (subst_val tauval) (ren_val xival) = subst_val ((funcomp) tauval xival) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_val xival tauval n)). Qed.

Lemma renRen_exp { kval : nat } { lval : nat } { mval : nat } (xival : (fin) (mval) -> (fin) (kval)) (zetaval : (fin) (kval) -> (fin) (lval)) (s : exp (mval)) : ren_exp zetaval (ren_exp xival s) = ren_exp ((funcomp) zetaval xival) s .
Proof. exact (compRenRen_exp xival zetaval (_) (fun n => eq_refl) s). Qed.

Lemma renRen_val { kval : nat } { lval : nat } { mval : nat } (xival : (fin) (mval) -> (fin) (kval)) (zetaval : (fin) (kval) -> (fin) (lval)) (s : val (mval)) : ren_val zetaval (ren_val xival s) = ren_val ((funcomp) zetaval xival) s .
Proof. exact (compRenRen_val xival zetaval (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_exp { kval : nat } { lval : nat } { mval : nat } (xival : (fin) (mval) -> (fin) (kval)) (zetaval : (fin) (kval) -> (fin) (lval)) : (funcomp) (ren_exp zetaval) (ren_exp xival) = ren_exp ((funcomp) zetaval xival) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_exp xival zetaval n)). Qed.

Lemma renRen'_val { kval : nat } { lval : nat } { mval : nat } (xival : (fin) (mval) -> (fin) (kval)) (zetaval : (fin) (kval) -> (fin) (lval)) : (funcomp) (ren_val zetaval) (ren_val xival) = ren_val ((funcomp) zetaval xival) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_val xival zetaval n)). Qed.

End expval.

Arguments value {nval}.

Arguments app {nval}.

Arguments mkpair {nval}.

Arguments fst {nval}.

Arguments snd {nval}.

Arguments letC {nval}.

Arguments var_val {nval}.

Arguments lam {nval}.

Arguments pair {nval}.

Arguments one {nval}.

Global Instance Subst_exp { mval : nat } { nval : nat } : Subst1 ((fin) (mval) -> val (nval)) (exp (mval)) (exp (nval)) := @subst_exp (mval) (nval) .

Global Instance Subst_val { mval : nat } { nval : nat } : Subst1 ((fin) (mval) -> val (nval)) (val (mval)) (val (nval)) := @subst_val (mval) (nval) .

Global Instance Ren_exp { mval : nat } { nval : nat } : Ren1 ((fin) (mval) -> (fin) (nval)) (exp (mval)) (exp (nval)) := @ren_exp (mval) (nval) .

Global Instance Ren_val { mval : nat } { nval : nat } : Ren1 ((fin) (mval) -> (fin) (nval)) (val (mval)) (val (nval)) := @ren_val (mval) (nval) .

Global Instance VarInstance_val { mval : nat } : Var ((fin) (mval)) (val (mval)) := @var_val (mval) .

Notation "x '__val'" := (var_val x) (at level 5, format "x __val") : subst_scope.

Notation "x '__val'" := (@ids (_) (_) VarInstance_val x) (at level 5, only printing, format "x __val") : subst_scope.

Notation "'var'" := (var_val) (only printing, at level 1) : subst_scope.

Class Up_val X Y := up_val : X -> Y.

Notation "↑__val" := (up_val) (only printing) : subst_scope.

Notation "↑__val" := (up_val_val) (only printing) : subst_scope.

Global Instance Up_val_val { m : nat } { nval : nat } : Up_val (_) (_) := @up_val_val (m) (nval) .

Notation "s [ sigmaval ]" := (subst_exp sigmaval s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaval ]" := (subst_exp sigmaval) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xival ⟩" := (ren_exp xival s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xival ⟩" := (ren_exp xival) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaval ]" := (subst_val sigmaval s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaval ]" := (subst_val sigmaval) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xival ⟩" := (ren_val xival s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xival ⟩" := (ren_val xival) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_exp,  Subst_val,  Ren_exp,  Ren_val,  VarInstance_val.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_exp,  Subst_val,  Ren_exp,  Ren_val,  VarInstance_val in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_exp| progress rewrite ?compComp_exp| progress rewrite ?compComp'_exp| progress rewrite ?instId_val| progress rewrite ?compComp_val| progress rewrite ?compComp'_val| progress rewrite ?rinstId_exp| progress rewrite ?compRen_exp| progress rewrite ?compRen'_exp| progress rewrite ?renComp_exp| progress rewrite ?renComp'_exp| progress rewrite ?renRen_exp| progress rewrite ?renRen'_exp| progress rewrite ?rinstId_val| progress rewrite ?compRen_val| progress rewrite ?compRen'_val| progress rewrite ?renComp_val| progress rewrite ?renComp'_val| progress rewrite ?renRen_val| progress rewrite ?renRen'_val| progress rewrite ?varL_val| progress rewrite ?varLRen_val| progress (unfold up_ren, upRen_val_val, up_val_val)| progress (cbn [subst_exp subst_val ren_exp ren_val])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_exp in *| progress rewrite ?compComp_exp in *| progress rewrite ?compComp'_exp in *| progress rewrite ?instId_val in *| progress rewrite ?compComp_val in *| progress rewrite ?compComp'_val in *| progress rewrite ?rinstId_exp in *| progress rewrite ?compRen_exp in *| progress rewrite ?compRen'_exp in *| progress rewrite ?renComp_exp in *| progress rewrite ?renComp'_exp in *| progress rewrite ?renRen_exp in *| progress rewrite ?renRen'_exp in *| progress rewrite ?rinstId_val in *| progress rewrite ?compRen_val in *| progress rewrite ?compRen'_val in *| progress rewrite ?renComp_val in *| progress rewrite ?renComp'_val in *| progress rewrite ?renRen_val in *| progress rewrite ?renRen'_val in *| progress rewrite ?varL_val in *| progress rewrite ?varLRen_val in *| progress (unfold up_ren, upRen_val_val, up_val_val in *)| progress (cbn [subst_exp subst_val ren_exp ren_val] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_exp); try repeat (erewrite rinstInst_val).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_exp); try repeat (erewrite <- rinstInst_val).

(** as_apply follows **)

Ltac  musigma gexp hexp :=
  match   gexp  with
  |  ?s  =>  unify   (gexp) (hexp)
  |  value (subst_val ?sigma0 ?s0)  =>  first [ unify   (subst_exp sigma0 (value s0)) (hexp)|  musigma   (subst_exp sigma0 (value s0)) (hexp) ]
  |  app (subst_exp ?sigma0 ?s0) (subst_exp ?sigma0 ?s1)  =>  first [ unify   (subst_exp sigma0 (app s0 s1)) (hexp)|  musigma   (subst_exp sigma0 (app s0 s1)) (hexp) ]
  |  mkpair (subst_exp ?sigma0 ?s0) (subst_exp ?sigma0 ?s1)  =>  first [ unify   (subst_exp sigma0 (mkpair s0 s1)) (hexp)|  musigma   (subst_exp sigma0 (mkpair s0 s1)) (hexp) ]
  |  fst (subst_exp ?sigma0 ?s0)  =>  first [ unify   (subst_exp sigma0 (fst s0)) (hexp)|  musigma   (subst_exp sigma0 (fst s0)) (hexp) ]
  |  snd (subst_exp ?sigma0 ?s0)  =>  first [ unify   (subst_exp sigma0 (snd s0)) (hexp)|  musigma   (subst_exp sigma0 (snd s0)) (hexp) ]
  |  letC (subst_exp ?sigma0 ?s0) (subst_exp ((scons) (var_val (var_zero)) ((funcomp) (ren_val (shift)) ?sigma0)) ?s1)  =>  first [ unify   (subst_exp sigma0 (letC s0 s1)) (hexp)|  musigma   (subst_exp sigma0 (letC s0 s1)) (hexp) ]
  |  value (ren_val ?sigma0 ?s0)  =>  first [ unify   (ren_exp sigma0 (value s0)) (hexp)|  musigma   (ren_exp sigma0 (value s0)) (hexp) ]
  |  app (ren_exp ?sigma0 ?s0) (ren_exp ?sigma0 ?s1)  =>  first [ unify   (ren_exp sigma0 (app s0 s1)) (hexp)|  musigma   (ren_exp sigma0 (app s0 s1)) (hexp) ]
  |  mkpair (ren_exp ?sigma0 ?s0) (ren_exp ?sigma0 ?s1)  =>  first [ unify   (ren_exp sigma0 (mkpair s0 s1)) (hexp)|  musigma   (ren_exp sigma0 (mkpair s0 s1)) (hexp) ]
  |  fst (ren_exp ?sigma0 ?s0)  =>  first [ unify   (ren_exp sigma0 (fst s0)) (hexp)|  musigma   (ren_exp sigma0 (fst s0)) (hexp) ]
  |  snd (ren_exp ?sigma0 ?s0)  =>  first [ unify   (ren_exp sigma0 (snd s0)) (hexp)|  musigma   (ren_exp sigma0 (snd s0)) (hexp) ]
  |  letC (ren_exp ?sigma0 ?s0) (ren_exp ((scons) (var_zero) ((funcomp) (shift) ?sigma0)) ?s1)  =>  first [ unify   (ren_exp sigma0 (letC s0 s1)) (hexp)|  musigma   (ren_exp sigma0 (letC s0 s1)) (hexp) ]
  |  lam (subst_exp ((scons) (var_val (var_zero)) ((funcomp) (ren_val (shift)) ?sigma0)) ?s0)  =>  first [ unify   (subst_val sigma0 (lam s0)) (hexp)|  musigma   (subst_val sigma0 (lam s0)) (hexp) ]
  |  pair (subst_val ?sigma0 ?s0) (subst_val ?sigma0 ?s1)  =>  first [ unify   (subst_val sigma0 (pair s0 s1)) (hexp)|  musigma   (subst_val sigma0 (pair s0 s1)) (hexp) ]
  |  lam (ren_exp ((scons) (var_zero) ((funcomp) (shift) ?sigma0)) ?s0)  =>  first [ unify   (ren_val sigma0 (lam s0)) (hexp)|  musigma   (ren_val sigma0 (lam s0)) (hexp) ]
  |  pair (ren_val ?sigma0 ?s0) (ren_val ?sigma0 ?s1)  =>  first [ unify   (ren_val sigma0 (pair s0 s1)) (hexp)|  musigma   (ren_val sigma0 (pair s0 s1)) (hexp) ]
  |  ren_exp ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  ren_exp ?theta0 ?t  =>  first [ unify   (ren_exp tau0 (ren_exp sigma0 s)) (hexp)|  musigma   (ren_exp tau0 (ren_exp sigma0 s)) (hexp) ]
  end
  |  subst_exp ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  subst_exp ?theta0 ?t  =>  first [ unify   (subst_exp tau0 (ren_exp sigma0 s)) (hexp)|  musigma   (subst_exp tau0 (ren_exp sigma0 s)) (hexp) ]
  end
  |  subst_exp ((funcomp) (ren_val ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  ren_exp ?theta0 ?t  =>  first [ unify   (ren_exp tau0 (subst_exp sigma0 s)) (hexp)|  musigma   (ren_exp tau0 (subst_exp sigma0 s)) (hexp) ]
  end
  |  subst_exp ((funcomp) (subst_val ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  subst_exp ?theta0 ?t  =>  first [ unify   (subst_exp tau0 (subst_exp sigma0 s)) (hexp)|  musigma   (subst_exp tau0 (subst_exp sigma0 s)) (hexp) ]
  end
  |  ren_val ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  ren_val ?theta0 ?t  =>  first [ unify   (ren_val tau0 (ren_val sigma0 s)) (hexp)|  musigma   (ren_val tau0 (ren_val sigma0 s)) (hexp) ]
  end
  |  subst_val ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  subst_val ?theta0 ?t  =>  first [ unify   (subst_val tau0 (ren_val sigma0 s)) (hexp)|  musigma   (subst_val tau0 (ren_val sigma0 s)) (hexp) ]
  end
  |  subst_val ((funcomp) (ren_val ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  ren_val ?theta0 ?t  =>  first [ unify   (ren_val tau0 (subst_val sigma0 s)) (hexp)|  musigma   (ren_val tau0 (subst_val sigma0 s)) (hexp) ]
  end
  |  subst_val ((funcomp) (subst_val ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  subst_val ?theta0 ?t  =>  first [ unify   (subst_val tau0 (subst_val sigma0 s)) (hexp)|  musigma   (subst_val tau0 (subst_val sigma0 s)) (hexp) ]
  end
  |  (funcomp) (ren_exp ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_exp ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_exp tau0) ((funcomp) (ren_exp sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (ren_exp tau0) ((funcomp) (ren_exp sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_exp ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_exp ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_exp tau0) ((funcomp) (ren_exp sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (subst_exp tau0) ((funcomp) (ren_exp sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_exp ((funcomp) (ren_val ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_exp ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_exp tau0) ((funcomp) (subst_exp sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (ren_exp tau0) ((funcomp) (subst_exp sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_exp ((funcomp) (subst_val ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_exp ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_exp tau0) ((funcomp) (subst_exp sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (subst_exp tau0) ((funcomp) (subst_exp sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (ren_val ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_val ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_val tau0) ((funcomp) (ren_val sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (ren_val tau0) ((funcomp) (ren_val sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_val ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_val ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_val tau0) ((funcomp) (ren_val sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (subst_val tau0) ((funcomp) (ren_val sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_val ((funcomp) (ren_val ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_val ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_val tau0) ((funcomp) (subst_val sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (ren_val tau0) ((funcomp) (subst_val sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_val ((funcomp) (subst_val ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_val ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_val tau0) ((funcomp) (subst_val sigma0) sigmas)) (hexp)|  musigma   ((funcomp) (subst_val tau0) ((funcomp) (subst_val sigma0) sigmas)) (hexp) ]
  end
  |  (scons) (ren_exp ?sigma0 ?s) ((funcomp) (ren_exp ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (ren_exp ?tau0) ?thetah  =>  first [ unify   ((funcomp) (ren_exp sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (ren_exp sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (subst_exp ?sigma0 ?s) ((funcomp) (subst_exp ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (subst_exp ?tau0) ?thetah  =>  first [ unify   ((funcomp) (subst_exp sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (subst_exp sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (ren_val ?sigma0 ?s) ((funcomp) (ren_val ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (ren_val ?tau0) ?thetah  =>  first [ unify   ((funcomp) (ren_val sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (ren_val sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (subst_val ?sigma0 ?s) ((funcomp) (subst_val ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (subst_val ?tau0) ?thetah  =>  first [ unify   ((funcomp) (subst_val sigma0) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (subst_val sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  value ?s0  =>  match   hexp  with
  |  value ?t0  =>  musigma   (s0) (t0)
  end
  |  app ?s0 ?s1  =>  match   hexp  with
  |  app ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  mkpair ?s0 ?s1  =>  match   hexp  with
  |  mkpair ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  fst ?s0  =>  match   hexp  with
  |  fst ?t0  =>  musigma   (s0) (t0)
  end
  |  snd ?s0  =>  match   hexp  with
  |  snd ?t0  =>  musigma   (s0) (t0)
  end
  |  letC ?s0 ?s1  =>  match   hexp  with
  |  letC ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  subst_exp ?sigma0 ?s  =>  match   hexp  with
  |  subst_exp ?tau0 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0)
  end
  |  ren_exp ?sigma0 ?s  =>  match   hexp  with
  |  ren_exp ?tau0 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0)
  end
  |  (funcomp) (subst_exp ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_exp ?tau0) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0)
  end
  |  (funcomp) (ren_exp ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_exp ?tau0) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0)
  end
  |  lam ?s0  =>  match   hexp  with
  |  lam ?t0  =>  musigma   (s0) (t0)
  end
  |  pair ?s0 ?s1  =>  match   hexp  with
  |  pair ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  subst_val ?sigma0 ?s  =>  match   hexp  with
  |  subst_val ?tau0 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0)
  end
  |  ren_val ?sigma0 ?s  =>  match   hexp  with
  |  ren_val ?tau0 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0)
  end
  |  (funcomp) (subst_val ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_val ?tau0) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0)
  end
  |  (funcomp) (ren_val ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_val ?tau0) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0)
  end
  end.

Ltac  heuristics gexp hexp :=
  match   gexp  with
  |  ?s  =>  unify   (gexp) (hexp)
  |  (funcomp) (subst_exp ((funcomp) var_val ?sigma0)) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_exp ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (subst_exp ((funcomp) var_val sigma0)) sigma = (funcomp) (ren_exp sigma0) sigma) as eq by (renamify; reflexivity); rewrite   (eq); unify   ((funcomp) (ren_exp sigma0) sigma) (hexp); clear eq
  end
  |  subst_exp ((funcomp) var_val ?sigma0) ?s  =>  match   hexp  with
  |  ren_exp ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (subst_exp ((funcomp) var_val sigma0) s = ren_exp sigma0 s) as eq by (renamify; reflexivity); rewrite   (eq); unify   (ren_exp sigma0 s) (hexp); clear eq
  end
  |  (funcomp) (subst_val ((funcomp) var_val ?sigma0)) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_val ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (subst_val ((funcomp) var_val sigma0)) sigma = (funcomp) (ren_val sigma0) sigma) as eq by (renamify; reflexivity); rewrite   (eq); unify   ((funcomp) (ren_val sigma0) sigma) (hexp); clear eq
  end
  |  subst_val ((funcomp) var_val ?sigma0) ?s  =>  match   hexp  with
  |  ren_val ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (subst_val ((funcomp) var_val sigma0) s = ren_val sigma0 s) as eq by (renamify; reflexivity); rewrite   (eq); unify   (ren_val sigma0 s) (hexp); clear eq
  end
  |  (funcomp) (ren_exp ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_exp ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_exp sigma0) sigma = (funcomp) (subst_exp ((funcomp) var_val sigma0)) sigma) as eq by (substify; reflexivity); rewrite   (eq); unify   ((funcomp) (subst_exp ((funcomp) var_val sigma0)) sigma) (hexp); clear eq
  end
  |  ren_exp ?sigma0 ?s  =>  match   hexp  with
  |  subst_exp ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (ren_exp sigma0 s = subst_exp ((funcomp) var_val sigma0) s) as eq by (substify; reflexivity); rewrite   (eq); unify   (subst_exp ((funcomp) var_val sigma0) s) (hexp); clear eq
  end
  |  (funcomp) (ren_val ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_val ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_val sigma0) sigma = (funcomp) (subst_val ((funcomp) var_val sigma0)) sigma) as eq by (substify; reflexivity); rewrite   (eq); unify   ((funcomp) (subst_val ((funcomp) var_val sigma0)) sigma) (hexp); clear eq
  end
  |  ren_val ?sigma0 ?s  =>  match   hexp  with
  |  subst_val ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (ren_val sigma0 s = subst_val ((funcomp) var_val sigma0) s) as eq by (substify; reflexivity); rewrite   (eq); unify   (subst_val ((funcomp) var_val sigma0) s) (hexp); clear eq
  end
  |  ?s  =>  musigma   (gexp) (hexp)
  |  subst_exp ((scons) ?sval0 ((funcomp) var_val ?sigmaval)) ?sexp  =>  match   hexp  with
  |  subst_exp ((scons) ?tval0 var_val) ?texp  =>  unify   (subst_exp ((scons) sval0 var_val) (ren_exp ((scons) (var_zero) ((funcomp) (shift) sigmaval)) sexp)) (hexp)
  end
  |  subst_exp ((scons) ?sval0 ?sigmaval) ?sexp  =>  match   hexp  with
  |  subst_exp ((scons) ?tval0 var_val) ?texp  =>  unify   (subst_exp ((scons) sval0 var_val) (subst_exp ((scons) (var_val (var_zero)) ((funcomp) (ren_val (shift)) sigmaval)) sexp)) (hexp)
  end
  |  subst_exp ((scons) ?sval0 ((funcomp) var_val ?sigmaval)) ?sexp  =>  match   hexp  with
  |  subst_exp ((scons) ?tval0 var_val) ?texp  =>  unify   (subst_exp ((scons) sval0 var_val) (ren_exp ((scons) (var_zero) ((funcomp) (shift) sigmaval)) sexp)) (hexp)
  end
  |  subst_exp ((scons) ?sval0 ?sigmaval) ?sexp  =>  match   hexp  with
  |  subst_exp ((scons) ?tval0 var_val) ?texp  =>  unify   (subst_exp ((scons) sval0 var_val) (subst_exp ((scons) (var_val (var_zero)) ((funcomp) (ren_val (shift)) sigmaval)) sexp)) (hexp)
  end
  |  ?s  =>  match   hexp  with
  |  subst_exp ?sigma0 ?t  =>  unify   (subst_exp var_val s) (hexp)
  |  ren_exp ?sigma0 ?t  =>  unify   (ren_exp (id) s) (hexp)
  |  subst_val ?sigma0 ?t  =>  unify   (subst_val var_val s) (hexp)
  |  ren_val ?sigma0 ?t  =>  unify   (ren_val (id) s) (hexp)
  end
  |  value ?s0  =>  match   hexp  with
  |  value ?t0  =>  heuristics   (s0) (t0)
  end
  |  app ?s0 ?s1  =>  match   hexp  with
  |  app ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  mkpair ?s0 ?s1  =>  match   hexp  with
  |  mkpair ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  fst ?s0  =>  match   hexp  with
  |  fst ?t0  =>  heuristics   (s0) (t0)
  end
  |  snd ?s0  =>  match   hexp  with
  |  snd ?t0  =>  heuristics   (s0) (t0)
  end
  |  letC ?s0 ?s1  =>  match   hexp  with
  |  letC ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  subst_exp ?sigma0 ?s  =>  match   hexp  with
  |  subst_exp ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  ren_exp ?sigma0 ?s  =>  match   hexp  with
  |  ren_exp ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (subst_exp ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_exp ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (ren_exp ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_exp ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  |  lam ?s0  =>  match   hexp  with
  |  lam ?t0  =>  heuristics   (s0) (t0)
  end
  |  pair ?s0 ?s1  =>  match   hexp  with
  |  pair ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  subst_val ?sigma0 ?s  =>  match   hexp  with
  |  subst_val ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  ren_val ?sigma0 ?s  =>  match   hexp  with
  |  ren_val ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (subst_val ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_val ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (ren_val ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_val ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
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
