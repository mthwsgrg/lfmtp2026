Require Export fintype.



Section tmstackcmd.
Inductive tm (ntm nstack : nat) : Type :=
  | var_tm : (fin) (ntm) -> tm (ntm) (nstack)
  | lam : tm  ((S) ntm) (nstack) -> tm (ntm) (nstack)
  | mu : cmd  (ntm) ((S) nstack) -> tm (ntm) (nstack)
 with stack (ntm nstack : nat) : Type :=
  | var_stack : (fin) (nstack) -> stack (ntm) (nstack)
  | cons : tm  (ntm) (nstack) -> stack  (ntm) (nstack) -> stack (ntm) (nstack)
 with cmd (ntm nstack : nat) : Type :=
  | cut : tm  (ntm) (nstack) -> stack  (ntm) (nstack) -> cmd (ntm) (nstack).

Lemma congr_lam { mtm mstack : nat } { s0 : tm  ((S) mtm) (mstack) } { t0 : tm  ((S) mtm) (mstack) } (H1 : s0 = t0) : lam (mtm) (mstack) s0 = lam (mtm) (mstack) t0 .
Proof. congruence. Qed.

Lemma congr_mu { mtm mstack : nat } { s0 : cmd  (mtm) ((S) mstack) } { t0 : cmd  (mtm) ((S) mstack) } (H1 : s0 = t0) : mu (mtm) (mstack) s0 = mu (mtm) (mstack) t0 .
Proof. congruence. Qed.

Lemma congr_cons { mtm mstack : nat } { s0 : tm  (mtm) (mstack) } { s1 : stack  (mtm) (mstack) } { t0 : tm  (mtm) (mstack) } { t1 : stack  (mtm) (mstack) } (H1 : s0 = t0) (H2 : s1 = t1) : cons (mtm) (mstack) s0 s1 = cons (mtm) (mstack) t0 t1 .
Proof. congruence. Qed.

Lemma congr_cut { mtm mstack : nat } { s0 : tm  (mtm) (mstack) } { s1 : stack  (mtm) (mstack) } { t0 : tm  (mtm) (mstack) } { t1 : stack  (mtm) (mstack) } (H1 : s0 = t0) (H2 : s1 = t1) : cut (mtm) (mstack) s0 s1 = cut (mtm) (mstack) t0 t1 .
Proof. congruence. Qed.

Definition upRen_tm_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Definition upRen_tm_stack { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (m) -> (fin) (n) :=
  xi.

Definition upRen_stack_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (m) -> (fin) (n) :=
  xi.

Definition upRen_stack_stack { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Fixpoint ren_tm { mtm mstack : nat } { ntm nstack : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xistack : (fin) (mstack) -> (fin) (nstack)) (s : tm (mtm) (mstack)) : tm (ntm) (nstack) :=
    match s return tm (ntm) (nstack) with
    | var_tm (_) (_) s => (var_tm (ntm) (nstack)) (xitm s)
    | lam (_) (_) s0 => lam (ntm) (nstack) ((ren_tm (upRen_tm_tm xitm) (upRen_tm_stack xistack)) s0)
    | mu (_) (_) s0 => mu (ntm) (nstack) ((ren_cmd (upRen_stack_tm xitm) (upRen_stack_stack xistack)) s0)
    end
 with ren_stack { mtm mstack : nat } { ntm nstack : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xistack : (fin) (mstack) -> (fin) (nstack)) (s : stack (mtm) (mstack)) : stack (ntm) (nstack) :=
    match s return stack (ntm) (nstack) with
    | var_stack (_) (_) s => (var_stack (ntm) (nstack)) (xistack s)
    | cons (_) (_) s0 s1 => cons (ntm) (nstack) ((ren_tm xitm xistack) s0) ((ren_stack xitm xistack) s1)
    end
 with ren_cmd { mtm mstack : nat } { ntm nstack : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xistack : (fin) (mstack) -> (fin) (nstack)) (s : cmd (mtm) (mstack)) : cmd (ntm) (nstack) :=
    match s return cmd (ntm) (nstack) with
    | cut (_) (_) s0 s1 => cut (ntm) (nstack) ((ren_tm xitm xistack) s0) ((ren_stack xitm xistack) s1)
    end.

Definition up_tm_tm { m : nat } { ntm nstack : nat } (sigma : (fin) (m) -> tm (ntm) (nstack)) : (fin) ((S) (m)) -> tm ((S) ntm) (nstack) :=
  (scons) ((var_tm ((S) ntm) (nstack)) (var_zero)) ((funcomp) (ren_tm (shift) (id)) sigma).

Definition up_tm_stack { m : nat } { ntm nstack : nat } (sigma : (fin) (m) -> stack (ntm) (nstack)) : (fin) (m) -> stack ((S) ntm) (nstack) :=
  (funcomp) (ren_stack (shift) (id)) sigma.

Definition up_stack_tm { m : nat } { ntm nstack : nat } (sigma : (fin) (m) -> tm (ntm) (nstack)) : (fin) (m) -> tm (ntm) ((S) nstack) :=
  (funcomp) (ren_tm (id) (shift)) sigma.

Definition up_stack_stack { m : nat } { ntm nstack : nat } (sigma : (fin) (m) -> stack (ntm) (nstack)) : (fin) ((S) (m)) -> stack (ntm) ((S) nstack) :=
  (scons) ((var_stack (ntm) ((S) nstack)) (var_zero)) ((funcomp) (ren_stack (id) (shift)) sigma).

Fixpoint subst_tm { mtm mstack : nat } { ntm nstack : nat } (sigmatm : (fin) (mtm) -> tm (ntm) (nstack)) (sigmastack : (fin) (mstack) -> stack (ntm) (nstack)) (s : tm (mtm) (mstack)) : tm (ntm) (nstack) :=
    match s return tm (ntm) (nstack) with
    | var_tm (_) (_) s => sigmatm s
    | lam (_) (_) s0 => lam (ntm) (nstack) ((subst_tm (up_tm_tm sigmatm) (up_tm_stack sigmastack)) s0)
    | mu (_) (_) s0 => mu (ntm) (nstack) ((subst_cmd (up_stack_tm sigmatm) (up_stack_stack sigmastack)) s0)
    end
 with subst_stack { mtm mstack : nat } { ntm nstack : nat } (sigmatm : (fin) (mtm) -> tm (ntm) (nstack)) (sigmastack : (fin) (mstack) -> stack (ntm) (nstack)) (s : stack (mtm) (mstack)) : stack (ntm) (nstack) :=
    match s return stack (ntm) (nstack) with
    | var_stack (_) (_) s => sigmastack s
    | cons (_) (_) s0 s1 => cons (ntm) (nstack) ((subst_tm sigmatm sigmastack) s0) ((subst_stack sigmatm sigmastack) s1)
    end
 with subst_cmd { mtm mstack : nat } { ntm nstack : nat } (sigmatm : (fin) (mtm) -> tm (ntm) (nstack)) (sigmastack : (fin) (mstack) -> stack (ntm) (nstack)) (s : cmd (mtm) (mstack)) : cmd (ntm) (nstack) :=
    match s return cmd (ntm) (nstack) with
    | cut (_) (_) s0 s1 => cut (ntm) (nstack) ((subst_tm sigmatm sigmastack) s0) ((subst_stack sigmatm sigmastack) s1)
    end.

Definition upId_tm_tm { mtm mstack : nat } (sigma : (fin) (mtm) -> tm (mtm) (mstack)) (Eq : forall x, sigma x = (var_tm (mtm) (mstack)) x) : forall x, (up_tm_tm sigma) x = (var_tm ((S) mtm) (mstack)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (shift) (id)) (Eq fin_n)
  | None  => eq_refl
  end.

Definition upId_tm_stack { mtm mstack : nat } (sigma : (fin) (mstack) -> stack (mtm) (mstack)) (Eq : forall x, sigma x = (var_stack (mtm) (mstack)) x) : forall x, (up_tm_stack sigma) x = (var_stack ((S) mtm) (mstack)) x :=
  fun n => (ap) (ren_stack (shift) (id)) (Eq n).

Definition upId_stack_tm { mtm mstack : nat } (sigma : (fin) (mtm) -> tm (mtm) (mstack)) (Eq : forall x, sigma x = (var_tm (mtm) (mstack)) x) : forall x, (up_stack_tm sigma) x = (var_tm (mtm) ((S) mstack)) x :=
  fun n => (ap) (ren_tm (id) (shift)) (Eq n).

Definition upId_stack_stack { mtm mstack : nat } (sigma : (fin) (mstack) -> stack (mtm) (mstack)) (Eq : forall x, sigma x = (var_stack (mtm) (mstack)) x) : forall x, (up_stack_stack sigma) x = (var_stack (mtm) ((S) mstack)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_stack (id) (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint idSubst_tm { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (mtm) (mstack)) (sigmastack : (fin) (mstack) -> stack (mtm) (mstack)) (Eqtm : forall x, sigmatm x = (var_tm (mtm) (mstack)) x) (Eqstack : forall x, sigmastack x = (var_stack (mtm) (mstack)) x) (s : tm (mtm) (mstack)) : subst_tm sigmatm sigmastack s = s :=
    match s return subst_tm sigmatm sigmastack s = s with
    | var_tm (_) (_) s => Eqtm s
    | lam (_) (_) s0 => congr_lam ((idSubst_tm (up_tm_tm sigmatm) (up_tm_stack sigmastack) (upId_tm_tm (_) Eqtm) (upId_tm_stack (_) Eqstack)) s0)
    | mu (_) (_) s0 => congr_mu ((idSubst_cmd (up_stack_tm sigmatm) (up_stack_stack sigmastack) (upId_stack_tm (_) Eqtm) (upId_stack_stack (_) Eqstack)) s0)
    end
 with idSubst_stack { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (mtm) (mstack)) (sigmastack : (fin) (mstack) -> stack (mtm) (mstack)) (Eqtm : forall x, sigmatm x = (var_tm (mtm) (mstack)) x) (Eqstack : forall x, sigmastack x = (var_stack (mtm) (mstack)) x) (s : stack (mtm) (mstack)) : subst_stack sigmatm sigmastack s = s :=
    match s return subst_stack sigmatm sigmastack s = s with
    | var_stack (_) (_) s => Eqstack s
    | cons (_) (_) s0 s1 => congr_cons ((idSubst_tm sigmatm sigmastack Eqtm Eqstack) s0) ((idSubst_stack sigmatm sigmastack Eqtm Eqstack) s1)
    end
 with idSubst_cmd { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (mtm) (mstack)) (sigmastack : (fin) (mstack) -> stack (mtm) (mstack)) (Eqtm : forall x, sigmatm x = (var_tm (mtm) (mstack)) x) (Eqstack : forall x, sigmastack x = (var_stack (mtm) (mstack)) x) (s : cmd (mtm) (mstack)) : subst_cmd sigmatm sigmastack s = s :=
    match s return subst_cmd sigmatm sigmastack s = s with
    | cut (_) (_) s0 s1 => congr_cut ((idSubst_tm sigmatm sigmastack Eqtm Eqstack) s0) ((idSubst_stack sigmatm sigmastack Eqtm Eqstack) s1)
    end.

Definition upExtRen_tm_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_tm_tm xi) x = (upRen_tm_tm zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Definition upExtRen_tm_stack { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_tm_stack xi) x = (upRen_tm_stack zeta) x :=
  fun n => Eq n.

Definition upExtRen_stack_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_stack_tm xi) x = (upRen_stack_tm zeta) x :=
  fun n => Eq n.

Definition upExtRen_stack_stack { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_stack_stack xi) x = (upRen_stack_stack zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint extRen_tm { mtm mstack : nat } { ntm nstack : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xistack : (fin) (mstack) -> (fin) (nstack)) (zetatm : (fin) (mtm) -> (fin) (ntm)) (zetastack : (fin) (mstack) -> (fin) (nstack)) (Eqtm : forall x, xitm x = zetatm x) (Eqstack : forall x, xistack x = zetastack x) (s : tm (mtm) (mstack)) : ren_tm xitm xistack s = ren_tm zetatm zetastack s :=
    match s return ren_tm xitm xistack s = ren_tm zetatm zetastack s with
    | var_tm (_) (_) s => (ap) (var_tm (ntm) (nstack)) (Eqtm s)
    | lam (_) (_) s0 => congr_lam ((extRen_tm (upRen_tm_tm xitm) (upRen_tm_stack xistack) (upRen_tm_tm zetatm) (upRen_tm_stack zetastack) (upExtRen_tm_tm (_) (_) Eqtm) (upExtRen_tm_stack (_) (_) Eqstack)) s0)
    | mu (_) (_) s0 => congr_mu ((extRen_cmd (upRen_stack_tm xitm) (upRen_stack_stack xistack) (upRen_stack_tm zetatm) (upRen_stack_stack zetastack) (upExtRen_stack_tm (_) (_) Eqtm) (upExtRen_stack_stack (_) (_) Eqstack)) s0)
    end
 with extRen_stack { mtm mstack : nat } { ntm nstack : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xistack : (fin) (mstack) -> (fin) (nstack)) (zetatm : (fin) (mtm) -> (fin) (ntm)) (zetastack : (fin) (mstack) -> (fin) (nstack)) (Eqtm : forall x, xitm x = zetatm x) (Eqstack : forall x, xistack x = zetastack x) (s : stack (mtm) (mstack)) : ren_stack xitm xistack s = ren_stack zetatm zetastack s :=
    match s return ren_stack xitm xistack s = ren_stack zetatm zetastack s with
    | var_stack (_) (_) s => (ap) (var_stack (ntm) (nstack)) (Eqstack s)
    | cons (_) (_) s0 s1 => congr_cons ((extRen_tm xitm xistack zetatm zetastack Eqtm Eqstack) s0) ((extRen_stack xitm xistack zetatm zetastack Eqtm Eqstack) s1)
    end
 with extRen_cmd { mtm mstack : nat } { ntm nstack : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xistack : (fin) (mstack) -> (fin) (nstack)) (zetatm : (fin) (mtm) -> (fin) (ntm)) (zetastack : (fin) (mstack) -> (fin) (nstack)) (Eqtm : forall x, xitm x = zetatm x) (Eqstack : forall x, xistack x = zetastack x) (s : cmd (mtm) (mstack)) : ren_cmd xitm xistack s = ren_cmd zetatm zetastack s :=
    match s return ren_cmd xitm xistack s = ren_cmd zetatm zetastack s with
    | cut (_) (_) s0 s1 => congr_cut ((extRen_tm xitm xistack zetatm zetastack Eqtm Eqstack) s0) ((extRen_stack xitm xistack zetatm zetastack Eqtm Eqstack) s1)
    end.

Definition upExt_tm_tm { m : nat } { ntm nstack : nat } (sigma : (fin) (m) -> tm (ntm) (nstack)) (tau : (fin) (m) -> tm (ntm) (nstack)) (Eq : forall x, sigma x = tau x) : forall x, (up_tm_tm sigma) x = (up_tm_tm tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (shift) (id)) (Eq fin_n)
  | None  => eq_refl
  end.

Definition upExt_tm_stack { m : nat } { ntm nstack : nat } (sigma : (fin) (m) -> stack (ntm) (nstack)) (tau : (fin) (m) -> stack (ntm) (nstack)) (Eq : forall x, sigma x = tau x) : forall x, (up_tm_stack sigma) x = (up_tm_stack tau) x :=
  fun n => (ap) (ren_stack (shift) (id)) (Eq n).

Definition upExt_stack_tm { m : nat } { ntm nstack : nat } (sigma : (fin) (m) -> tm (ntm) (nstack)) (tau : (fin) (m) -> tm (ntm) (nstack)) (Eq : forall x, sigma x = tau x) : forall x, (up_stack_tm sigma) x = (up_stack_tm tau) x :=
  fun n => (ap) (ren_tm (id) (shift)) (Eq n).

Definition upExt_stack_stack { m : nat } { ntm nstack : nat } (sigma : (fin) (m) -> stack (ntm) (nstack)) (tau : (fin) (m) -> stack (ntm) (nstack)) (Eq : forall x, sigma x = tau x) : forall x, (up_stack_stack sigma) x = (up_stack_stack tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_stack (id) (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint ext_tm { mtm mstack : nat } { ntm nstack : nat } (sigmatm : (fin) (mtm) -> tm (ntm) (nstack)) (sigmastack : (fin) (mstack) -> stack (ntm) (nstack)) (tautm : (fin) (mtm) -> tm (ntm) (nstack)) (taustack : (fin) (mstack) -> stack (ntm) (nstack)) (Eqtm : forall x, sigmatm x = tautm x) (Eqstack : forall x, sigmastack x = taustack x) (s : tm (mtm) (mstack)) : subst_tm sigmatm sigmastack s = subst_tm tautm taustack s :=
    match s return subst_tm sigmatm sigmastack s = subst_tm tautm taustack s with
    | var_tm (_) (_) s => Eqtm s
    | lam (_) (_) s0 => congr_lam ((ext_tm (up_tm_tm sigmatm) (up_tm_stack sigmastack) (up_tm_tm tautm) (up_tm_stack taustack) (upExt_tm_tm (_) (_) Eqtm) (upExt_tm_stack (_) (_) Eqstack)) s0)
    | mu (_) (_) s0 => congr_mu ((ext_cmd (up_stack_tm sigmatm) (up_stack_stack sigmastack) (up_stack_tm tautm) (up_stack_stack taustack) (upExt_stack_tm (_) (_) Eqtm) (upExt_stack_stack (_) (_) Eqstack)) s0)
    end
 with ext_stack { mtm mstack : nat } { ntm nstack : nat } (sigmatm : (fin) (mtm) -> tm (ntm) (nstack)) (sigmastack : (fin) (mstack) -> stack (ntm) (nstack)) (tautm : (fin) (mtm) -> tm (ntm) (nstack)) (taustack : (fin) (mstack) -> stack (ntm) (nstack)) (Eqtm : forall x, sigmatm x = tautm x) (Eqstack : forall x, sigmastack x = taustack x) (s : stack (mtm) (mstack)) : subst_stack sigmatm sigmastack s = subst_stack tautm taustack s :=
    match s return subst_stack sigmatm sigmastack s = subst_stack tautm taustack s with
    | var_stack (_) (_) s => Eqstack s
    | cons (_) (_) s0 s1 => congr_cons ((ext_tm sigmatm sigmastack tautm taustack Eqtm Eqstack) s0) ((ext_stack sigmatm sigmastack tautm taustack Eqtm Eqstack) s1)
    end
 with ext_cmd { mtm mstack : nat } { ntm nstack : nat } (sigmatm : (fin) (mtm) -> tm (ntm) (nstack)) (sigmastack : (fin) (mstack) -> stack (ntm) (nstack)) (tautm : (fin) (mtm) -> tm (ntm) (nstack)) (taustack : (fin) (mstack) -> stack (ntm) (nstack)) (Eqtm : forall x, sigmatm x = tautm x) (Eqstack : forall x, sigmastack x = taustack x) (s : cmd (mtm) (mstack)) : subst_cmd sigmatm sigmastack s = subst_cmd tautm taustack s :=
    match s return subst_cmd sigmatm sigmastack s = subst_cmd tautm taustack s with
    | cut (_) (_) s0 s1 => congr_cut ((ext_tm sigmatm sigmastack tautm taustack Eqtm Eqstack) s0) ((ext_stack sigmatm sigmastack tautm taustack Eqtm Eqstack) s1)
    end.

Definition up_ren_ren_tm_tm { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_tm_tm tau) (upRen_tm_tm xi)) x = (upRen_tm_tm theta) x :=
  up_ren_ren xi tau theta Eq.

Definition up_ren_ren_tm_stack { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_tm_stack tau) (upRen_tm_stack xi)) x = (upRen_tm_stack theta) x :=
  Eq.

Definition up_ren_ren_stack_tm { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_stack_tm tau) (upRen_stack_tm xi)) x = (upRen_stack_tm theta) x :=
  Eq.

Definition up_ren_ren_stack_stack { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_stack_stack tau) (upRen_stack_stack xi)) x = (upRen_stack_stack theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_tm { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xistack : (fin) (mstack) -> (fin) (kstack)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetastack : (fin) (kstack) -> (fin) (lstack)) (rhotm : (fin) (mtm) -> (fin) (ltm)) (rhostack : (fin) (mstack) -> (fin) (lstack)) (Eqtm : forall x, ((funcomp) zetatm xitm) x = rhotm x) (Eqstack : forall x, ((funcomp) zetastack xistack) x = rhostack x) (s : tm (mtm) (mstack)) : ren_tm zetatm zetastack (ren_tm xitm xistack s) = ren_tm rhotm rhostack s :=
    match s return ren_tm zetatm zetastack (ren_tm xitm xistack s) = ren_tm rhotm rhostack s with
    | var_tm (_) (_) s => (ap) (var_tm (ltm) (lstack)) (Eqtm s)
    | lam (_) (_) s0 => congr_lam ((compRenRen_tm (upRen_tm_tm xitm) (upRen_tm_stack xistack) (upRen_tm_tm zetatm) (upRen_tm_stack zetastack) (upRen_tm_tm rhotm) (upRen_tm_stack rhostack) (up_ren_ren (_) (_) (_) Eqtm) Eqstack) s0)
    | mu (_) (_) s0 => congr_mu ((compRenRen_cmd (upRen_stack_tm xitm) (upRen_stack_stack xistack) (upRen_stack_tm zetatm) (upRen_stack_stack zetastack) (upRen_stack_tm rhotm) (upRen_stack_stack rhostack) Eqtm (up_ren_ren (_) (_) (_) Eqstack)) s0)
    end
 with compRenRen_stack { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xistack : (fin) (mstack) -> (fin) (kstack)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetastack : (fin) (kstack) -> (fin) (lstack)) (rhotm : (fin) (mtm) -> (fin) (ltm)) (rhostack : (fin) (mstack) -> (fin) (lstack)) (Eqtm : forall x, ((funcomp) zetatm xitm) x = rhotm x) (Eqstack : forall x, ((funcomp) zetastack xistack) x = rhostack x) (s : stack (mtm) (mstack)) : ren_stack zetatm zetastack (ren_stack xitm xistack s) = ren_stack rhotm rhostack s :=
    match s return ren_stack zetatm zetastack (ren_stack xitm xistack s) = ren_stack rhotm rhostack s with
    | var_stack (_) (_) s => (ap) (var_stack (ltm) (lstack)) (Eqstack s)
    | cons (_) (_) s0 s1 => congr_cons ((compRenRen_tm xitm xistack zetatm zetastack rhotm rhostack Eqtm Eqstack) s0) ((compRenRen_stack xitm xistack zetatm zetastack rhotm rhostack Eqtm Eqstack) s1)
    end
 with compRenRen_cmd { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xistack : (fin) (mstack) -> (fin) (kstack)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetastack : (fin) (kstack) -> (fin) (lstack)) (rhotm : (fin) (mtm) -> (fin) (ltm)) (rhostack : (fin) (mstack) -> (fin) (lstack)) (Eqtm : forall x, ((funcomp) zetatm xitm) x = rhotm x) (Eqstack : forall x, ((funcomp) zetastack xistack) x = rhostack x) (s : cmd (mtm) (mstack)) : ren_cmd zetatm zetastack (ren_cmd xitm xistack s) = ren_cmd rhotm rhostack s :=
    match s return ren_cmd zetatm zetastack (ren_cmd xitm xistack s) = ren_cmd rhotm rhostack s with
    | cut (_) (_) s0 s1 => congr_cut ((compRenRen_tm xitm xistack zetatm zetastack rhotm rhostack Eqtm Eqstack) s0) ((compRenRen_stack xitm xistack zetatm zetastack rhotm rhostack Eqtm Eqstack) s1)
    end.

Definition up_ren_subst_tm_tm { k : nat } { l : nat } { mtm mstack : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> tm (mtm) (mstack)) (theta : (fin) (k) -> tm (mtm) (mstack)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_tm_tm tau) (upRen_tm_tm xi)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (shift) (id)) (Eq fin_n)
  | None  => eq_refl
  end.

Definition up_ren_subst_tm_stack { k : nat } { l : nat } { mtm mstack : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> stack (mtm) (mstack)) (theta : (fin) (k) -> stack (mtm) (mstack)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_tm_stack tau) (upRen_tm_stack xi)) x = (up_tm_stack theta) x :=
  fun n => (ap) (ren_stack (shift) (id)) (Eq n).

Definition up_ren_subst_stack_tm { k : nat } { l : nat } { mtm mstack : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> tm (mtm) (mstack)) (theta : (fin) (k) -> tm (mtm) (mstack)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_stack_tm tau) (upRen_stack_tm xi)) x = (up_stack_tm theta) x :=
  fun n => (ap) (ren_tm (id) (shift)) (Eq n).

Definition up_ren_subst_stack_stack { k : nat } { l : nat } { mtm mstack : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> stack (mtm) (mstack)) (theta : (fin) (k) -> stack (mtm) (mstack)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_stack_stack tau) (upRen_stack_stack xi)) x = (up_stack_stack theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_stack (id) (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint compRenSubst_tm { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xistack : (fin) (mstack) -> (fin) (kstack)) (tautm : (fin) (ktm) -> tm (ltm) (lstack)) (taustack : (fin) (kstack) -> stack (ltm) (lstack)) (thetatm : (fin) (mtm) -> tm (ltm) (lstack)) (thetastack : (fin) (mstack) -> stack (ltm) (lstack)) (Eqtm : forall x, ((funcomp) tautm xitm) x = thetatm x) (Eqstack : forall x, ((funcomp) taustack xistack) x = thetastack x) (s : tm (mtm) (mstack)) : subst_tm tautm taustack (ren_tm xitm xistack s) = subst_tm thetatm thetastack s :=
    match s return subst_tm tautm taustack (ren_tm xitm xistack s) = subst_tm thetatm thetastack s with
    | var_tm (_) (_) s => Eqtm s
    | lam (_) (_) s0 => congr_lam ((compRenSubst_tm (upRen_tm_tm xitm) (upRen_tm_stack xistack) (up_tm_tm tautm) (up_tm_stack taustack) (up_tm_tm thetatm) (up_tm_stack thetastack) (up_ren_subst_tm_tm (_) (_) (_) Eqtm) (up_ren_subst_tm_stack (_) (_) (_) Eqstack)) s0)
    | mu (_) (_) s0 => congr_mu ((compRenSubst_cmd (upRen_stack_tm xitm) (upRen_stack_stack xistack) (up_stack_tm tautm) (up_stack_stack taustack) (up_stack_tm thetatm) (up_stack_stack thetastack) (up_ren_subst_stack_tm (_) (_) (_) Eqtm) (up_ren_subst_stack_stack (_) (_) (_) Eqstack)) s0)
    end
 with compRenSubst_stack { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xistack : (fin) (mstack) -> (fin) (kstack)) (tautm : (fin) (ktm) -> tm (ltm) (lstack)) (taustack : (fin) (kstack) -> stack (ltm) (lstack)) (thetatm : (fin) (mtm) -> tm (ltm) (lstack)) (thetastack : (fin) (mstack) -> stack (ltm) (lstack)) (Eqtm : forall x, ((funcomp) tautm xitm) x = thetatm x) (Eqstack : forall x, ((funcomp) taustack xistack) x = thetastack x) (s : stack (mtm) (mstack)) : subst_stack tautm taustack (ren_stack xitm xistack s) = subst_stack thetatm thetastack s :=
    match s return subst_stack tautm taustack (ren_stack xitm xistack s) = subst_stack thetatm thetastack s with
    | var_stack (_) (_) s => Eqstack s
    | cons (_) (_) s0 s1 => congr_cons ((compRenSubst_tm xitm xistack tautm taustack thetatm thetastack Eqtm Eqstack) s0) ((compRenSubst_stack xitm xistack tautm taustack thetatm thetastack Eqtm Eqstack) s1)
    end
 with compRenSubst_cmd { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xistack : (fin) (mstack) -> (fin) (kstack)) (tautm : (fin) (ktm) -> tm (ltm) (lstack)) (taustack : (fin) (kstack) -> stack (ltm) (lstack)) (thetatm : (fin) (mtm) -> tm (ltm) (lstack)) (thetastack : (fin) (mstack) -> stack (ltm) (lstack)) (Eqtm : forall x, ((funcomp) tautm xitm) x = thetatm x) (Eqstack : forall x, ((funcomp) taustack xistack) x = thetastack x) (s : cmd (mtm) (mstack)) : subst_cmd tautm taustack (ren_cmd xitm xistack s) = subst_cmd thetatm thetastack s :=
    match s return subst_cmd tautm taustack (ren_cmd xitm xistack s) = subst_cmd thetatm thetastack s with
    | cut (_) (_) s0 s1 => congr_cut ((compRenSubst_tm xitm xistack tautm taustack thetatm thetastack Eqtm Eqstack) s0) ((compRenSubst_stack xitm xistack tautm taustack thetatm thetastack Eqtm Eqstack) s1)
    end.

Definition up_subst_ren_tm_tm { k : nat } { ltm lstack : nat } { mtm mstack : nat } (sigma : (fin) (k) -> tm (ltm) (lstack)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (zetastack : (fin) (lstack) -> (fin) (mstack)) (theta : (fin) (k) -> tm (mtm) (mstack)) (Eq : forall x, ((funcomp) (ren_tm zetatm zetastack) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRen_tm_tm zetatm) (upRen_tm_stack zetastack)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_tm (shift) (id) (upRen_tm_tm zetatm) (upRen_tm_stack zetastack) ((funcomp) (shift) zetatm) ((funcomp) (id) zetastack) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetatm zetastack (shift) (id) ((funcomp) (shift) zetatm) ((funcomp) (id) zetastack) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_tm (shift) (id)) (Eq fin_n)))
  | None  => eq_refl
  end.

Definition up_subst_ren_tm_stack { k : nat } { ltm lstack : nat } { mtm mstack : nat } (sigma : (fin) (k) -> stack (ltm) (lstack)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (zetastack : (fin) (lstack) -> (fin) (mstack)) (theta : (fin) (k) -> stack (mtm) (mstack)) (Eq : forall x, ((funcomp) (ren_stack zetatm zetastack) sigma) x = theta x) : forall x, ((funcomp) (ren_stack (upRen_tm_tm zetatm) (upRen_tm_stack zetastack)) (up_tm_stack sigma)) x = (up_tm_stack theta) x :=
  fun n => (eq_trans) (compRenRen_stack (shift) (id) (upRen_tm_tm zetatm) (upRen_tm_stack zetastack) ((funcomp) (shift) zetatm) ((funcomp) (id) zetastack) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_stack zetatm zetastack (shift) (id) ((funcomp) (shift) zetatm) ((funcomp) (id) zetastack) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_stack (shift) (id)) (Eq n))).

Definition up_subst_ren_stack_tm { k : nat } { ltm lstack : nat } { mtm mstack : nat } (sigma : (fin) (k) -> tm (ltm) (lstack)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (zetastack : (fin) (lstack) -> (fin) (mstack)) (theta : (fin) (k) -> tm (mtm) (mstack)) (Eq : forall x, ((funcomp) (ren_tm zetatm zetastack) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRen_stack_tm zetatm) (upRen_stack_stack zetastack)) (up_stack_tm sigma)) x = (up_stack_tm theta) x :=
  fun n => (eq_trans) (compRenRen_tm (id) (shift) (upRen_stack_tm zetatm) (upRen_stack_stack zetastack) ((funcomp) (id) zetatm) ((funcomp) (shift) zetastack) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetatm zetastack (id) (shift) ((funcomp) (id) zetatm) ((funcomp) (shift) zetastack) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_tm (id) (shift)) (Eq n))).

Definition up_subst_ren_stack_stack { k : nat } { ltm lstack : nat } { mtm mstack : nat } (sigma : (fin) (k) -> stack (ltm) (lstack)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (zetastack : (fin) (lstack) -> (fin) (mstack)) (theta : (fin) (k) -> stack (mtm) (mstack)) (Eq : forall x, ((funcomp) (ren_stack zetatm zetastack) sigma) x = theta x) : forall x, ((funcomp) (ren_stack (upRen_stack_tm zetatm) (upRen_stack_stack zetastack)) (up_stack_stack sigma)) x = (up_stack_stack theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_stack (id) (shift) (upRen_stack_tm zetatm) (upRen_stack_stack zetastack) ((funcomp) (id) zetatm) ((funcomp) (shift) zetastack) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_stack zetatm zetastack (id) (shift) ((funcomp) (id) zetatm) ((funcomp) (shift) zetastack) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_stack (id) (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstRen_tm { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kstack)) (sigmastack : (fin) (mstack) -> stack (ktm) (kstack)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetastack : (fin) (kstack) -> (fin) (lstack)) (thetatm : (fin) (mtm) -> tm (ltm) (lstack)) (thetastack : (fin) (mstack) -> stack (ltm) (lstack)) (Eqtm : forall x, ((funcomp) (ren_tm zetatm zetastack) sigmatm) x = thetatm x) (Eqstack : forall x, ((funcomp) (ren_stack zetatm zetastack) sigmastack) x = thetastack x) (s : tm (mtm) (mstack)) : ren_tm zetatm zetastack (subst_tm sigmatm sigmastack s) = subst_tm thetatm thetastack s :=
    match s return ren_tm zetatm zetastack (subst_tm sigmatm sigmastack s) = subst_tm thetatm thetastack s with
    | var_tm (_) (_) s => Eqtm s
    | lam (_) (_) s0 => congr_lam ((compSubstRen_tm (up_tm_tm sigmatm) (up_tm_stack sigmastack) (upRen_tm_tm zetatm) (upRen_tm_stack zetastack) (up_tm_tm thetatm) (up_tm_stack thetastack) (up_subst_ren_tm_tm (_) (_) (_) (_) Eqtm) (up_subst_ren_tm_stack (_) (_) (_) (_) Eqstack)) s0)
    | mu (_) (_) s0 => congr_mu ((compSubstRen_cmd (up_stack_tm sigmatm) (up_stack_stack sigmastack) (upRen_stack_tm zetatm) (upRen_stack_stack zetastack) (up_stack_tm thetatm) (up_stack_stack thetastack) (up_subst_ren_stack_tm (_) (_) (_) (_) Eqtm) (up_subst_ren_stack_stack (_) (_) (_) (_) Eqstack)) s0)
    end
 with compSubstRen_stack { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kstack)) (sigmastack : (fin) (mstack) -> stack (ktm) (kstack)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetastack : (fin) (kstack) -> (fin) (lstack)) (thetatm : (fin) (mtm) -> tm (ltm) (lstack)) (thetastack : (fin) (mstack) -> stack (ltm) (lstack)) (Eqtm : forall x, ((funcomp) (ren_tm zetatm zetastack) sigmatm) x = thetatm x) (Eqstack : forall x, ((funcomp) (ren_stack zetatm zetastack) sigmastack) x = thetastack x) (s : stack (mtm) (mstack)) : ren_stack zetatm zetastack (subst_stack sigmatm sigmastack s) = subst_stack thetatm thetastack s :=
    match s return ren_stack zetatm zetastack (subst_stack sigmatm sigmastack s) = subst_stack thetatm thetastack s with
    | var_stack (_) (_) s => Eqstack s
    | cons (_) (_) s0 s1 => congr_cons ((compSubstRen_tm sigmatm sigmastack zetatm zetastack thetatm thetastack Eqtm Eqstack) s0) ((compSubstRen_stack sigmatm sigmastack zetatm zetastack thetatm thetastack Eqtm Eqstack) s1)
    end
 with compSubstRen_cmd { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kstack)) (sigmastack : (fin) (mstack) -> stack (ktm) (kstack)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetastack : (fin) (kstack) -> (fin) (lstack)) (thetatm : (fin) (mtm) -> tm (ltm) (lstack)) (thetastack : (fin) (mstack) -> stack (ltm) (lstack)) (Eqtm : forall x, ((funcomp) (ren_tm zetatm zetastack) sigmatm) x = thetatm x) (Eqstack : forall x, ((funcomp) (ren_stack zetatm zetastack) sigmastack) x = thetastack x) (s : cmd (mtm) (mstack)) : ren_cmd zetatm zetastack (subst_cmd sigmatm sigmastack s) = subst_cmd thetatm thetastack s :=
    match s return ren_cmd zetatm zetastack (subst_cmd sigmatm sigmastack s) = subst_cmd thetatm thetastack s with
    | cut (_) (_) s0 s1 => congr_cut ((compSubstRen_tm sigmatm sigmastack zetatm zetastack thetatm thetastack Eqtm Eqstack) s0) ((compSubstRen_stack sigmatm sigmastack zetatm zetastack thetatm thetastack Eqtm Eqstack) s1)
    end.

Definition up_subst_subst_tm_tm { k : nat } { ltm lstack : nat } { mtm mstack : nat } (sigma : (fin) (k) -> tm (ltm) (lstack)) (tautm : (fin) (ltm) -> tm (mtm) (mstack)) (taustack : (fin) (lstack) -> stack (mtm) (mstack)) (theta : (fin) (k) -> tm (mtm) (mstack)) (Eq : forall x, ((funcomp) (subst_tm tautm taustack) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (up_tm_tm tautm) (up_tm_stack taustack)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_tm (shift) (id) (up_tm_tm tautm) (up_tm_stack taustack) ((funcomp) (up_tm_tm tautm) (shift)) ((funcomp) (up_tm_stack taustack) (id)) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tautm taustack (shift) (id) ((funcomp) (ren_tm (shift) (id)) tautm) ((funcomp) (ren_stack (shift) (id)) taustack) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_tm (shift) (id)) (Eq fin_n)))
  | None  => eq_refl
  end.

Definition up_subst_subst_tm_stack { k : nat } { ltm lstack : nat } { mtm mstack : nat } (sigma : (fin) (k) -> stack (ltm) (lstack)) (tautm : (fin) (ltm) -> tm (mtm) (mstack)) (taustack : (fin) (lstack) -> stack (mtm) (mstack)) (theta : (fin) (k) -> stack (mtm) (mstack)) (Eq : forall x, ((funcomp) (subst_stack tautm taustack) sigma) x = theta x) : forall x, ((funcomp) (subst_stack (up_tm_tm tautm) (up_tm_stack taustack)) (up_tm_stack sigma)) x = (up_tm_stack theta) x :=
  fun n => (eq_trans) (compRenSubst_stack (shift) (id) (up_tm_tm tautm) (up_tm_stack taustack) ((funcomp) (up_tm_tm tautm) (shift)) ((funcomp) (up_tm_stack taustack) (id)) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_stack tautm taustack (shift) (id) ((funcomp) (ren_tm (shift) (id)) tautm) ((funcomp) (ren_stack (shift) (id)) taustack) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_stack (shift) (id)) (Eq n))).

Definition up_subst_subst_stack_tm { k : nat } { ltm lstack : nat } { mtm mstack : nat } (sigma : (fin) (k) -> tm (ltm) (lstack)) (tautm : (fin) (ltm) -> tm (mtm) (mstack)) (taustack : (fin) (lstack) -> stack (mtm) (mstack)) (theta : (fin) (k) -> tm (mtm) (mstack)) (Eq : forall x, ((funcomp) (subst_tm tautm taustack) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (up_stack_tm tautm) (up_stack_stack taustack)) (up_stack_tm sigma)) x = (up_stack_tm theta) x :=
  fun n => (eq_trans) (compRenSubst_tm (id) (shift) (up_stack_tm tautm) (up_stack_stack taustack) ((funcomp) (up_stack_tm tautm) (id)) ((funcomp) (up_stack_stack taustack) (shift)) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tautm taustack (id) (shift) ((funcomp) (ren_tm (id) (shift)) tautm) ((funcomp) (ren_stack (id) (shift)) taustack) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_tm (id) (shift)) (Eq n))).

Definition up_subst_subst_stack_stack { k : nat } { ltm lstack : nat } { mtm mstack : nat } (sigma : (fin) (k) -> stack (ltm) (lstack)) (tautm : (fin) (ltm) -> tm (mtm) (mstack)) (taustack : (fin) (lstack) -> stack (mtm) (mstack)) (theta : (fin) (k) -> stack (mtm) (mstack)) (Eq : forall x, ((funcomp) (subst_stack tautm taustack) sigma) x = theta x) : forall x, ((funcomp) (subst_stack (up_stack_tm tautm) (up_stack_stack taustack)) (up_stack_stack sigma)) x = (up_stack_stack theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_stack (id) (shift) (up_stack_tm tautm) (up_stack_stack taustack) ((funcomp) (up_stack_tm tautm) (id)) ((funcomp) (up_stack_stack taustack) (shift)) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_stack tautm taustack (id) (shift) ((funcomp) (ren_tm (id) (shift)) tautm) ((funcomp) (ren_stack (id) (shift)) taustack) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_stack (id) (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstSubst_tm { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kstack)) (sigmastack : (fin) (mstack) -> stack (ktm) (kstack)) (tautm : (fin) (ktm) -> tm (ltm) (lstack)) (taustack : (fin) (kstack) -> stack (ltm) (lstack)) (thetatm : (fin) (mtm) -> tm (ltm) (lstack)) (thetastack : (fin) (mstack) -> stack (ltm) (lstack)) (Eqtm : forall x, ((funcomp) (subst_tm tautm taustack) sigmatm) x = thetatm x) (Eqstack : forall x, ((funcomp) (subst_stack tautm taustack) sigmastack) x = thetastack x) (s : tm (mtm) (mstack)) : subst_tm tautm taustack (subst_tm sigmatm sigmastack s) = subst_tm thetatm thetastack s :=
    match s return subst_tm tautm taustack (subst_tm sigmatm sigmastack s) = subst_tm thetatm thetastack s with
    | var_tm (_) (_) s => Eqtm s
    | lam (_) (_) s0 => congr_lam ((compSubstSubst_tm (up_tm_tm sigmatm) (up_tm_stack sigmastack) (up_tm_tm tautm) (up_tm_stack taustack) (up_tm_tm thetatm) (up_tm_stack thetastack) (up_subst_subst_tm_tm (_) (_) (_) (_) Eqtm) (up_subst_subst_tm_stack (_) (_) (_) (_) Eqstack)) s0)
    | mu (_) (_) s0 => congr_mu ((compSubstSubst_cmd (up_stack_tm sigmatm) (up_stack_stack sigmastack) (up_stack_tm tautm) (up_stack_stack taustack) (up_stack_tm thetatm) (up_stack_stack thetastack) (up_subst_subst_stack_tm (_) (_) (_) (_) Eqtm) (up_subst_subst_stack_stack (_) (_) (_) (_) Eqstack)) s0)
    end
 with compSubstSubst_stack { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kstack)) (sigmastack : (fin) (mstack) -> stack (ktm) (kstack)) (tautm : (fin) (ktm) -> tm (ltm) (lstack)) (taustack : (fin) (kstack) -> stack (ltm) (lstack)) (thetatm : (fin) (mtm) -> tm (ltm) (lstack)) (thetastack : (fin) (mstack) -> stack (ltm) (lstack)) (Eqtm : forall x, ((funcomp) (subst_tm tautm taustack) sigmatm) x = thetatm x) (Eqstack : forall x, ((funcomp) (subst_stack tautm taustack) sigmastack) x = thetastack x) (s : stack (mtm) (mstack)) : subst_stack tautm taustack (subst_stack sigmatm sigmastack s) = subst_stack thetatm thetastack s :=
    match s return subst_stack tautm taustack (subst_stack sigmatm sigmastack s) = subst_stack thetatm thetastack s with
    | var_stack (_) (_) s => Eqstack s
    | cons (_) (_) s0 s1 => congr_cons ((compSubstSubst_tm sigmatm sigmastack tautm taustack thetatm thetastack Eqtm Eqstack) s0) ((compSubstSubst_stack sigmatm sigmastack tautm taustack thetatm thetastack Eqtm Eqstack) s1)
    end
 with compSubstSubst_cmd { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kstack)) (sigmastack : (fin) (mstack) -> stack (ktm) (kstack)) (tautm : (fin) (ktm) -> tm (ltm) (lstack)) (taustack : (fin) (kstack) -> stack (ltm) (lstack)) (thetatm : (fin) (mtm) -> tm (ltm) (lstack)) (thetastack : (fin) (mstack) -> stack (ltm) (lstack)) (Eqtm : forall x, ((funcomp) (subst_tm tautm taustack) sigmatm) x = thetatm x) (Eqstack : forall x, ((funcomp) (subst_stack tautm taustack) sigmastack) x = thetastack x) (s : cmd (mtm) (mstack)) : subst_cmd tautm taustack (subst_cmd sigmatm sigmastack s) = subst_cmd thetatm thetastack s :=
    match s return subst_cmd tautm taustack (subst_cmd sigmatm sigmastack s) = subst_cmd thetatm thetastack s with
    | cut (_) (_) s0 s1 => congr_cut ((compSubstSubst_tm sigmatm sigmastack tautm taustack thetatm thetastack Eqtm Eqstack) s0) ((compSubstSubst_stack sigmatm sigmastack tautm taustack thetatm thetastack Eqtm Eqstack) s1)
    end.

Definition rinstInst_up_tm_tm { m : nat } { ntm nstack : nat } (xi : (fin) (m) -> (fin) (ntm)) (sigma : (fin) (m) -> tm (ntm) (nstack)) (Eq : forall x, ((funcomp) (var_tm (ntm) (nstack)) xi) x = sigma x) : forall x, ((funcomp) (var_tm ((S) ntm) (nstack)) (upRen_tm_tm xi)) x = (up_tm_tm sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (shift) (id)) (Eq fin_n)
  | None  => eq_refl
  end.

Definition rinstInst_up_tm_stack { m : nat } { ntm nstack : nat } (xi : (fin) (m) -> (fin) (nstack)) (sigma : (fin) (m) -> stack (ntm) (nstack)) (Eq : forall x, ((funcomp) (var_stack (ntm) (nstack)) xi) x = sigma x) : forall x, ((funcomp) (var_stack ((S) ntm) (nstack)) (upRen_tm_stack xi)) x = (up_tm_stack sigma) x :=
  fun n => (ap) (ren_stack (shift) (id)) (Eq n).

Definition rinstInst_up_stack_tm { m : nat } { ntm nstack : nat } (xi : (fin) (m) -> (fin) (ntm)) (sigma : (fin) (m) -> tm (ntm) (nstack)) (Eq : forall x, ((funcomp) (var_tm (ntm) (nstack)) xi) x = sigma x) : forall x, ((funcomp) (var_tm (ntm) ((S) nstack)) (upRen_stack_tm xi)) x = (up_stack_tm sigma) x :=
  fun n => (ap) (ren_tm (id) (shift)) (Eq n).

Definition rinstInst_up_stack_stack { m : nat } { ntm nstack : nat } (xi : (fin) (m) -> (fin) (nstack)) (sigma : (fin) (m) -> stack (ntm) (nstack)) (Eq : forall x, ((funcomp) (var_stack (ntm) (nstack)) xi) x = sigma x) : forall x, ((funcomp) (var_stack (ntm) ((S) nstack)) (upRen_stack_stack xi)) x = (up_stack_stack sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_stack (id) (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint rinst_inst_tm { mtm mstack : nat } { ntm nstack : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xistack : (fin) (mstack) -> (fin) (nstack)) (sigmatm : (fin) (mtm) -> tm (ntm) (nstack)) (sigmastack : (fin) (mstack) -> stack (ntm) (nstack)) (Eqtm : forall x, ((funcomp) (var_tm (ntm) (nstack)) xitm) x = sigmatm x) (Eqstack : forall x, ((funcomp) (var_stack (ntm) (nstack)) xistack) x = sigmastack x) (s : tm (mtm) (mstack)) : ren_tm xitm xistack s = subst_tm sigmatm sigmastack s :=
    match s return ren_tm xitm xistack s = subst_tm sigmatm sigmastack s with
    | var_tm (_) (_) s => Eqtm s
    | lam (_) (_) s0 => congr_lam ((rinst_inst_tm (upRen_tm_tm xitm) (upRen_tm_stack xistack) (up_tm_tm sigmatm) (up_tm_stack sigmastack) (rinstInst_up_tm_tm (_) (_) Eqtm) (rinstInst_up_tm_stack (_) (_) Eqstack)) s0)
    | mu (_) (_) s0 => congr_mu ((rinst_inst_cmd (upRen_stack_tm xitm) (upRen_stack_stack xistack) (up_stack_tm sigmatm) (up_stack_stack sigmastack) (rinstInst_up_stack_tm (_) (_) Eqtm) (rinstInst_up_stack_stack (_) (_) Eqstack)) s0)
    end
 with rinst_inst_stack { mtm mstack : nat } { ntm nstack : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xistack : (fin) (mstack) -> (fin) (nstack)) (sigmatm : (fin) (mtm) -> tm (ntm) (nstack)) (sigmastack : (fin) (mstack) -> stack (ntm) (nstack)) (Eqtm : forall x, ((funcomp) (var_tm (ntm) (nstack)) xitm) x = sigmatm x) (Eqstack : forall x, ((funcomp) (var_stack (ntm) (nstack)) xistack) x = sigmastack x) (s : stack (mtm) (mstack)) : ren_stack xitm xistack s = subst_stack sigmatm sigmastack s :=
    match s return ren_stack xitm xistack s = subst_stack sigmatm sigmastack s with
    | var_stack (_) (_) s => Eqstack s
    | cons (_) (_) s0 s1 => congr_cons ((rinst_inst_tm xitm xistack sigmatm sigmastack Eqtm Eqstack) s0) ((rinst_inst_stack xitm xistack sigmatm sigmastack Eqtm Eqstack) s1)
    end
 with rinst_inst_cmd { mtm mstack : nat } { ntm nstack : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xistack : (fin) (mstack) -> (fin) (nstack)) (sigmatm : (fin) (mtm) -> tm (ntm) (nstack)) (sigmastack : (fin) (mstack) -> stack (ntm) (nstack)) (Eqtm : forall x, ((funcomp) (var_tm (ntm) (nstack)) xitm) x = sigmatm x) (Eqstack : forall x, ((funcomp) (var_stack (ntm) (nstack)) xistack) x = sigmastack x) (s : cmd (mtm) (mstack)) : ren_cmd xitm xistack s = subst_cmd sigmatm sigmastack s :=
    match s return ren_cmd xitm xistack s = subst_cmd sigmatm sigmastack s with
    | cut (_) (_) s0 s1 => congr_cut ((rinst_inst_tm xitm xistack sigmatm sigmastack Eqtm Eqstack) s0) ((rinst_inst_stack xitm xistack sigmatm sigmastack Eqtm Eqstack) s1)
    end.

Lemma rinstInst_tm { mtm mstack : nat } { ntm nstack : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xistack : (fin) (mstack) -> (fin) (nstack)) : ren_tm xitm xistack = subst_tm ((funcomp) (var_tm (ntm) (nstack)) xitm) ((funcomp) (var_stack (ntm) (nstack)) xistack) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_tm xitm xistack (_) (_) (fun n => eq_refl) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_stack { mtm mstack : nat } { ntm nstack : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xistack : (fin) (mstack) -> (fin) (nstack)) : ren_stack xitm xistack = subst_stack ((funcomp) (var_tm (ntm) (nstack)) xitm) ((funcomp) (var_stack (ntm) (nstack)) xistack) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_stack xitm xistack (_) (_) (fun n => eq_refl) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_cmd { mtm mstack : nat } { ntm nstack : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xistack : (fin) (mstack) -> (fin) (nstack)) : ren_cmd xitm xistack = subst_cmd ((funcomp) (var_tm (ntm) (nstack)) xitm) ((funcomp) (var_stack (ntm) (nstack)) xistack) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_cmd xitm xistack (_) (_) (fun n => eq_refl) (fun n => eq_refl) x)). Qed.

Lemma instId_tm { mtm mstack : nat } : subst_tm (var_tm (mtm) (mstack)) (var_stack (mtm) (mstack)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_tm (var_tm (mtm) (mstack)) (var_stack (mtm) (mstack)) (fun n => eq_refl) (fun n => eq_refl) ((id) x))). Qed.

Lemma instId_stack { mtm mstack : nat } : subst_stack (var_tm (mtm) (mstack)) (var_stack (mtm) (mstack)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_stack (var_tm (mtm) (mstack)) (var_stack (mtm) (mstack)) (fun n => eq_refl) (fun n => eq_refl) ((id) x))). Qed.

Lemma instId_cmd { mtm mstack : nat } : subst_cmd (var_tm (mtm) (mstack)) (var_stack (mtm) (mstack)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_cmd (var_tm (mtm) (mstack)) (var_stack (mtm) (mstack)) (fun n => eq_refl) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_tm { mtm mstack : nat } : @ren_tm (mtm) (mstack) (mtm) (mstack) (id) (id) = id .
Proof. exact ((eq_trans) (rinstInst_tm ((id) (_)) ((id) (_))) instId_tm). Qed.

Lemma rinstId_stack { mtm mstack : nat } : @ren_stack (mtm) (mstack) (mtm) (mstack) (id) (id) = id .
Proof. exact ((eq_trans) (rinstInst_stack ((id) (_)) ((id) (_))) instId_stack). Qed.

Lemma rinstId_cmd { mtm mstack : nat } : @ren_cmd (mtm) (mstack) (mtm) (mstack) (id) (id) = id .
Proof. exact ((eq_trans) (rinstInst_cmd ((id) (_)) ((id) (_))) instId_cmd). Qed.

Lemma varL_tm { mtm mstack : nat } { ntm nstack : nat } (sigmatm : (fin) (mtm) -> tm (ntm) (nstack)) (sigmastack : (fin) (mstack) -> stack (ntm) (nstack)) : (funcomp) (subst_tm sigmatm sigmastack) (var_tm (mtm) (mstack)) = sigmatm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varL_stack { mtm mstack : nat } { ntm nstack : nat } (sigmatm : (fin) (mtm) -> tm (ntm) (nstack)) (sigmastack : (fin) (mstack) -> stack (ntm) (nstack)) : (funcomp) (subst_stack sigmatm sigmastack) (var_stack (mtm) (mstack)) = sigmastack .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_tm { mtm mstack : nat } { ntm nstack : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xistack : (fin) (mstack) -> (fin) (nstack)) : (funcomp) (ren_tm xitm xistack) (var_tm (mtm) (mstack)) = (funcomp) (var_tm (ntm) (nstack)) xitm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_stack { mtm mstack : nat } { ntm nstack : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (xistack : (fin) (mstack) -> (fin) (nstack)) : (funcomp) (ren_stack xitm xistack) (var_stack (mtm) (mstack)) = (funcomp) (var_stack (ntm) (nstack)) xistack .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_tm { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kstack)) (sigmastack : (fin) (mstack) -> stack (ktm) (kstack)) (tautm : (fin) (ktm) -> tm (ltm) (lstack)) (taustack : (fin) (kstack) -> stack (ltm) (lstack)) (s : tm (mtm) (mstack)) : subst_tm tautm taustack (subst_tm sigmatm sigmastack s) = subst_tm ((funcomp) (subst_tm tautm taustack) sigmatm) ((funcomp) (subst_stack tautm taustack) sigmastack) s .
Proof. exact (compSubstSubst_tm sigmatm sigmastack tautm taustack (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compComp_stack { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kstack)) (sigmastack : (fin) (mstack) -> stack (ktm) (kstack)) (tautm : (fin) (ktm) -> tm (ltm) (lstack)) (taustack : (fin) (kstack) -> stack (ltm) (lstack)) (s : stack (mtm) (mstack)) : subst_stack tautm taustack (subst_stack sigmatm sigmastack s) = subst_stack ((funcomp) (subst_tm tautm taustack) sigmatm) ((funcomp) (subst_stack tautm taustack) sigmastack) s .
Proof. exact (compSubstSubst_stack sigmatm sigmastack tautm taustack (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compComp_cmd { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kstack)) (sigmastack : (fin) (mstack) -> stack (ktm) (kstack)) (tautm : (fin) (ktm) -> tm (ltm) (lstack)) (taustack : (fin) (kstack) -> stack (ltm) (lstack)) (s : cmd (mtm) (mstack)) : subst_cmd tautm taustack (subst_cmd sigmatm sigmastack s) = subst_cmd ((funcomp) (subst_tm tautm taustack) sigmatm) ((funcomp) (subst_stack tautm taustack) sigmastack) s .
Proof. exact (compSubstSubst_cmd sigmatm sigmastack tautm taustack (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compComp'_tm { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kstack)) (sigmastack : (fin) (mstack) -> stack (ktm) (kstack)) (tautm : (fin) (ktm) -> tm (ltm) (lstack)) (taustack : (fin) (kstack) -> stack (ltm) (lstack)) : (funcomp) (subst_tm tautm taustack) (subst_tm sigmatm sigmastack) = subst_tm ((funcomp) (subst_tm tautm taustack) sigmatm) ((funcomp) (subst_stack tautm taustack) sigmastack) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_tm sigmatm sigmastack tautm taustack n)). Qed.

Lemma compComp'_stack { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kstack)) (sigmastack : (fin) (mstack) -> stack (ktm) (kstack)) (tautm : (fin) (ktm) -> tm (ltm) (lstack)) (taustack : (fin) (kstack) -> stack (ltm) (lstack)) : (funcomp) (subst_stack tautm taustack) (subst_stack sigmatm sigmastack) = subst_stack ((funcomp) (subst_tm tautm taustack) sigmatm) ((funcomp) (subst_stack tautm taustack) sigmastack) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_stack sigmatm sigmastack tautm taustack n)). Qed.

Lemma compComp'_cmd { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kstack)) (sigmastack : (fin) (mstack) -> stack (ktm) (kstack)) (tautm : (fin) (ktm) -> tm (ltm) (lstack)) (taustack : (fin) (kstack) -> stack (ltm) (lstack)) : (funcomp) (subst_cmd tautm taustack) (subst_cmd sigmatm sigmastack) = subst_cmd ((funcomp) (subst_tm tautm taustack) sigmatm) ((funcomp) (subst_stack tautm taustack) sigmastack) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_cmd sigmatm sigmastack tautm taustack n)). Qed.

Lemma compRen_tm { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kstack)) (sigmastack : (fin) (mstack) -> stack (ktm) (kstack)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetastack : (fin) (kstack) -> (fin) (lstack)) (s : tm (mtm) (mstack)) : ren_tm zetatm zetastack (subst_tm sigmatm sigmastack s) = subst_tm ((funcomp) (ren_tm zetatm zetastack) sigmatm) ((funcomp) (ren_stack zetatm zetastack) sigmastack) s .
Proof. exact (compSubstRen_tm sigmatm sigmastack zetatm zetastack (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compRen_stack { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kstack)) (sigmastack : (fin) (mstack) -> stack (ktm) (kstack)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetastack : (fin) (kstack) -> (fin) (lstack)) (s : stack (mtm) (mstack)) : ren_stack zetatm zetastack (subst_stack sigmatm sigmastack s) = subst_stack ((funcomp) (ren_tm zetatm zetastack) sigmatm) ((funcomp) (ren_stack zetatm zetastack) sigmastack) s .
Proof. exact (compSubstRen_stack sigmatm sigmastack zetatm zetastack (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compRen_cmd { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kstack)) (sigmastack : (fin) (mstack) -> stack (ktm) (kstack)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetastack : (fin) (kstack) -> (fin) (lstack)) (s : cmd (mtm) (mstack)) : ren_cmd zetatm zetastack (subst_cmd sigmatm sigmastack s) = subst_cmd ((funcomp) (ren_tm zetatm zetastack) sigmatm) ((funcomp) (ren_stack zetatm zetastack) sigmastack) s .
Proof. exact (compSubstRen_cmd sigmatm sigmastack zetatm zetastack (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compRen'_tm { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kstack)) (sigmastack : (fin) (mstack) -> stack (ktm) (kstack)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetastack : (fin) (kstack) -> (fin) (lstack)) : (funcomp) (ren_tm zetatm zetastack) (subst_tm sigmatm sigmastack) = subst_tm ((funcomp) (ren_tm zetatm zetastack) sigmatm) ((funcomp) (ren_stack zetatm zetastack) sigmastack) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_tm sigmatm sigmastack zetatm zetastack n)). Qed.

Lemma compRen'_stack { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kstack)) (sigmastack : (fin) (mstack) -> stack (ktm) (kstack)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetastack : (fin) (kstack) -> (fin) (lstack)) : (funcomp) (ren_stack zetatm zetastack) (subst_stack sigmatm sigmastack) = subst_stack ((funcomp) (ren_tm zetatm zetastack) sigmatm) ((funcomp) (ren_stack zetatm zetastack) sigmastack) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_stack sigmatm sigmastack zetatm zetastack n)). Qed.

Lemma compRen'_cmd { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (sigmatm : (fin) (mtm) -> tm (ktm) (kstack)) (sigmastack : (fin) (mstack) -> stack (ktm) (kstack)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetastack : (fin) (kstack) -> (fin) (lstack)) : (funcomp) (ren_cmd zetatm zetastack) (subst_cmd sigmatm sigmastack) = subst_cmd ((funcomp) (ren_tm zetatm zetastack) sigmatm) ((funcomp) (ren_stack zetatm zetastack) sigmastack) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_cmd sigmatm sigmastack zetatm zetastack n)). Qed.

Lemma renComp_tm { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xistack : (fin) (mstack) -> (fin) (kstack)) (tautm : (fin) (ktm) -> tm (ltm) (lstack)) (taustack : (fin) (kstack) -> stack (ltm) (lstack)) (s : tm (mtm) (mstack)) : subst_tm tautm taustack (ren_tm xitm xistack s) = subst_tm ((funcomp) tautm xitm) ((funcomp) taustack xistack) s .
Proof. exact (compRenSubst_tm xitm xistack tautm taustack (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renComp_stack { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xistack : (fin) (mstack) -> (fin) (kstack)) (tautm : (fin) (ktm) -> tm (ltm) (lstack)) (taustack : (fin) (kstack) -> stack (ltm) (lstack)) (s : stack (mtm) (mstack)) : subst_stack tautm taustack (ren_stack xitm xistack s) = subst_stack ((funcomp) tautm xitm) ((funcomp) taustack xistack) s .
Proof. exact (compRenSubst_stack xitm xistack tautm taustack (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renComp_cmd { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xistack : (fin) (mstack) -> (fin) (kstack)) (tautm : (fin) (ktm) -> tm (ltm) (lstack)) (taustack : (fin) (kstack) -> stack (ltm) (lstack)) (s : cmd (mtm) (mstack)) : subst_cmd tautm taustack (ren_cmd xitm xistack s) = subst_cmd ((funcomp) tautm xitm) ((funcomp) taustack xistack) s .
Proof. exact (compRenSubst_cmd xitm xistack tautm taustack (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renComp'_tm { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xistack : (fin) (mstack) -> (fin) (kstack)) (tautm : (fin) (ktm) -> tm (ltm) (lstack)) (taustack : (fin) (kstack) -> stack (ltm) (lstack)) : (funcomp) (subst_tm tautm taustack) (ren_tm xitm xistack) = subst_tm ((funcomp) tautm xitm) ((funcomp) taustack xistack) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_tm xitm xistack tautm taustack n)). Qed.

Lemma renComp'_stack { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xistack : (fin) (mstack) -> (fin) (kstack)) (tautm : (fin) (ktm) -> tm (ltm) (lstack)) (taustack : (fin) (kstack) -> stack (ltm) (lstack)) : (funcomp) (subst_stack tautm taustack) (ren_stack xitm xistack) = subst_stack ((funcomp) tautm xitm) ((funcomp) taustack xistack) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_stack xitm xistack tautm taustack n)). Qed.

Lemma renComp'_cmd { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xistack : (fin) (mstack) -> (fin) (kstack)) (tautm : (fin) (ktm) -> tm (ltm) (lstack)) (taustack : (fin) (kstack) -> stack (ltm) (lstack)) : (funcomp) (subst_cmd tautm taustack) (ren_cmd xitm xistack) = subst_cmd ((funcomp) tautm xitm) ((funcomp) taustack xistack) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_cmd xitm xistack tautm taustack n)). Qed.

Lemma renRen_tm { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xistack : (fin) (mstack) -> (fin) (kstack)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetastack : (fin) (kstack) -> (fin) (lstack)) (s : tm (mtm) (mstack)) : ren_tm zetatm zetastack (ren_tm xitm xistack s) = ren_tm ((funcomp) zetatm xitm) ((funcomp) zetastack xistack) s .
Proof. exact (compRenRen_tm xitm xistack zetatm zetastack (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renRen_stack { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xistack : (fin) (mstack) -> (fin) (kstack)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetastack : (fin) (kstack) -> (fin) (lstack)) (s : stack (mtm) (mstack)) : ren_stack zetatm zetastack (ren_stack xitm xistack s) = ren_stack ((funcomp) zetatm xitm) ((funcomp) zetastack xistack) s .
Proof. exact (compRenRen_stack xitm xistack zetatm zetastack (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renRen_cmd { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xistack : (fin) (mstack) -> (fin) (kstack)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetastack : (fin) (kstack) -> (fin) (lstack)) (s : cmd (mtm) (mstack)) : ren_cmd zetatm zetastack (ren_cmd xitm xistack s) = ren_cmd ((funcomp) zetatm xitm) ((funcomp) zetastack xistack) s .
Proof. exact (compRenRen_cmd xitm xistack zetatm zetastack (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renRen'_tm { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xistack : (fin) (mstack) -> (fin) (kstack)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetastack : (fin) (kstack) -> (fin) (lstack)) : (funcomp) (ren_tm zetatm zetastack) (ren_tm xitm xistack) = ren_tm ((funcomp) zetatm xitm) ((funcomp) zetastack xistack) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_tm xitm xistack zetatm zetastack n)). Qed.

Lemma renRen'_stack { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xistack : (fin) (mstack) -> (fin) (kstack)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetastack : (fin) (kstack) -> (fin) (lstack)) : (funcomp) (ren_stack zetatm zetastack) (ren_stack xitm xistack) = ren_stack ((funcomp) zetatm xitm) ((funcomp) zetastack xistack) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_stack xitm xistack zetatm zetastack n)). Qed.

Lemma renRen'_cmd { ktm kstack : nat } { ltm lstack : nat } { mtm mstack : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (xistack : (fin) (mstack) -> (fin) (kstack)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (zetastack : (fin) (kstack) -> (fin) (lstack)) : (funcomp) (ren_cmd zetatm zetastack) (ren_cmd xitm xistack) = ren_cmd ((funcomp) zetatm xitm) ((funcomp) zetastack xistack) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_cmd xitm xistack zetatm zetastack n)). Qed.

End tmstackcmd.

Arguments var_tm {ntm} {nstack}.

Arguments lam {ntm} {nstack}.

Arguments mu {ntm} {nstack}.

Arguments var_stack {ntm} {nstack}.

Arguments cons {ntm} {nstack}.

Arguments cut {ntm} {nstack}.

Global Instance Subst_tm { mtm mstack : nat } { ntm nstack : nat } : Subst2 ((fin) (mtm) -> tm (ntm) (nstack)) ((fin) (mstack) -> stack (ntm) (nstack)) (tm (mtm) (mstack)) (tm (ntm) (nstack)) := @subst_tm (mtm) (mstack) (ntm) (nstack) .

Global Instance Subst_stack { mtm mstack : nat } { ntm nstack : nat } : Subst2 ((fin) (mtm) -> tm (ntm) (nstack)) ((fin) (mstack) -> stack (ntm) (nstack)) (stack (mtm) (mstack)) (stack (ntm) (nstack)) := @subst_stack (mtm) (mstack) (ntm) (nstack) .

Global Instance Subst_cmd { mtm mstack : nat } { ntm nstack : nat } : Subst2 ((fin) (mtm) -> tm (ntm) (nstack)) ((fin) (mstack) -> stack (ntm) (nstack)) (cmd (mtm) (mstack)) (cmd (ntm) (nstack)) := @subst_cmd (mtm) (mstack) (ntm) (nstack) .

Global Instance Ren_tm { mtm mstack : nat } { ntm nstack : nat } : Ren2 ((fin) (mtm) -> (fin) (ntm)) ((fin) (mstack) -> (fin) (nstack)) (tm (mtm) (mstack)) (tm (ntm) (nstack)) := @ren_tm (mtm) (mstack) (ntm) (nstack) .

Global Instance Ren_stack { mtm mstack : nat } { ntm nstack : nat } : Ren2 ((fin) (mtm) -> (fin) (ntm)) ((fin) (mstack) -> (fin) (nstack)) (stack (mtm) (mstack)) (stack (ntm) (nstack)) := @ren_stack (mtm) (mstack) (ntm) (nstack) .

Global Instance Ren_cmd { mtm mstack : nat } { ntm nstack : nat } : Ren2 ((fin) (mtm) -> (fin) (ntm)) ((fin) (mstack) -> (fin) (nstack)) (cmd (mtm) (mstack)) (cmd (ntm) (nstack)) := @ren_cmd (mtm) (mstack) (ntm) (nstack) .

Global Instance VarInstance_tm { mtm mstack : nat } : Var ((fin) (mtm)) (tm (mtm) (mstack)) := @var_tm (mtm) (mstack) .

Notation "x '__tm'" := (var_tm x) (at level 5, format "x __tm") : subst_scope.

Notation "x '__tm'" := (@ids (_) (_) VarInstance_tm x) (at level 5, only printing, format "x __tm") : subst_scope.

Notation "'var'" := (var_tm) (only printing, at level 1) : subst_scope.

Global Instance VarInstance_stack { mtm mstack : nat } : Var ((fin) (mstack)) (stack (mtm) (mstack)) := @var_stack (mtm) (mstack) .

Notation "x '__stack'" := (var_stack x) (at level 5, format "x __stack") : subst_scope.

Notation "x '__stack'" := (@ids (_) (_) VarInstance_stack x) (at level 5, only printing, format "x __stack") : subst_scope.

Notation "'var'" := (var_stack) (only printing, at level 1) : subst_scope.

Class Up_tm X Y := up_tm : X -> Y.

Notation "↑__tm" := (up_tm) (only printing) : subst_scope.

Class Up_stack X Y := up_stack : X -> Y.

Notation "↑__stack" := (up_stack) (only printing) : subst_scope.

Notation "↑__tm" := (up_tm_tm) (only printing) : subst_scope.

Global Instance Up_tm_tm { m : nat } { ntm nstack : nat } : Up_tm (_) (_) := @up_tm_tm (m) (ntm) (nstack) .

Notation "↑__tm" := (up_tm_stack) (only printing) : subst_scope.

Global Instance Up_tm_stack { m : nat } { ntm nstack : nat } : Up_stack (_) (_) := @up_tm_stack (m) (ntm) (nstack) .

Notation "↑__stack" := (up_stack_tm) (only printing) : subst_scope.

Global Instance Up_stack_tm { m : nat } { ntm nstack : nat } : Up_tm (_) (_) := @up_stack_tm (m) (ntm) (nstack) .

Notation "↑__stack" := (up_stack_stack) (only printing) : subst_scope.

Global Instance Up_stack_stack { m : nat } { ntm nstack : nat } : Up_stack (_) (_) := @up_stack_stack (m) (ntm) (nstack) .

Notation "s [ sigmatm ; sigmastack ]" := (subst_tm sigmatm sigmastack s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmatm ; sigmastack ]" := (subst_tm sigmatm sigmastack) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xitm ; xistack ⟩" := (ren_tm xitm xistack s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xitm ; xistack ⟩" := (ren_tm xitm xistack) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmatm ; sigmastack ]" := (subst_stack sigmatm sigmastack s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmatm ; sigmastack ]" := (subst_stack sigmatm sigmastack) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xitm ; xistack ⟩" := (ren_stack xitm xistack s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xitm ; xistack ⟩" := (ren_stack xitm xistack) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmatm ; sigmastack ]" := (subst_cmd sigmatm sigmastack s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmatm ; sigmastack ]" := (subst_cmd sigmatm sigmastack) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xitm ; xistack ⟩" := (ren_cmd xitm xistack s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xitm ; xistack ⟩" := (ren_cmd xitm xistack) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_tm,  Subst_stack,  Subst_cmd,  Ren_tm,  Ren_stack,  Ren_cmd,  VarInstance_tm,  VarInstance_stack.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_tm,  Subst_stack,  Subst_cmd,  Ren_tm,  Ren_stack,  Ren_cmd,  VarInstance_tm,  VarInstance_stack in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_tm| progress rewrite ?compComp_tm| progress rewrite ?compComp'_tm| progress rewrite ?instId_stack| progress rewrite ?compComp_stack| progress rewrite ?compComp'_stack| progress rewrite ?instId_cmd| progress rewrite ?compComp_cmd| progress rewrite ?compComp'_cmd| progress rewrite ?rinstId_tm| progress rewrite ?compRen_tm| progress rewrite ?compRen'_tm| progress rewrite ?renComp_tm| progress rewrite ?renComp'_tm| progress rewrite ?renRen_tm| progress rewrite ?renRen'_tm| progress rewrite ?rinstId_stack| progress rewrite ?compRen_stack| progress rewrite ?compRen'_stack| progress rewrite ?renComp_stack| progress rewrite ?renComp'_stack| progress rewrite ?renRen_stack| progress rewrite ?renRen'_stack| progress rewrite ?rinstId_cmd| progress rewrite ?compRen_cmd| progress rewrite ?compRen'_cmd| progress rewrite ?renComp_cmd| progress rewrite ?renComp'_cmd| progress rewrite ?renRen_cmd| progress rewrite ?renRen'_cmd| progress rewrite ?varL_tm| progress rewrite ?varL_stack| progress rewrite ?varLRen_tm| progress rewrite ?varLRen_stack| progress (unfold up_ren, upRen_tm_tm, upRen_tm_stack, upRen_stack_tm, upRen_stack_stack, up_tm_tm, up_tm_stack, up_stack_tm, up_stack_stack)| progress (cbn [subst_tm subst_stack subst_cmd ren_tm ren_stack ren_cmd])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_tm in *| progress rewrite ?compComp_tm in *| progress rewrite ?compComp'_tm in *| progress rewrite ?instId_stack in *| progress rewrite ?compComp_stack in *| progress rewrite ?compComp'_stack in *| progress rewrite ?instId_cmd in *| progress rewrite ?compComp_cmd in *| progress rewrite ?compComp'_cmd in *| progress rewrite ?rinstId_tm in *| progress rewrite ?compRen_tm in *| progress rewrite ?compRen'_tm in *| progress rewrite ?renComp_tm in *| progress rewrite ?renComp'_tm in *| progress rewrite ?renRen_tm in *| progress rewrite ?renRen'_tm in *| progress rewrite ?rinstId_stack in *| progress rewrite ?compRen_stack in *| progress rewrite ?compRen'_stack in *| progress rewrite ?renComp_stack in *| progress rewrite ?renComp'_stack in *| progress rewrite ?renRen_stack in *| progress rewrite ?renRen'_stack in *| progress rewrite ?rinstId_cmd in *| progress rewrite ?compRen_cmd in *| progress rewrite ?compRen'_cmd in *| progress rewrite ?renComp_cmd in *| progress rewrite ?renComp'_cmd in *| progress rewrite ?renRen_cmd in *| progress rewrite ?renRen'_cmd in *| progress rewrite ?varL_tm in *| progress rewrite ?varL_stack in *| progress rewrite ?varLRen_tm in *| progress rewrite ?varLRen_stack in *| progress (unfold up_ren, upRen_tm_tm, upRen_tm_stack, upRen_stack_tm, upRen_stack_stack, up_tm_tm, up_tm_stack, up_stack_tm, up_stack_stack in *)| progress (cbn [subst_tm subst_stack subst_cmd ren_tm ren_stack ren_cmd] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_tm); try repeat (erewrite rinstInst_stack); try repeat (erewrite rinstInst_cmd).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_tm); try repeat (erewrite <- rinstInst_stack); try repeat (erewrite <- rinstInst_cmd).

(** as_apply follows **)

Ltac  musigma gexp hexp :=
  match   gexp  with
  |  ?s  =>  unify   (gexp) (hexp)
  |  lam (subst_tm ((funcomp) (ren_stack (shift) (id)) ?sigma1) ((scons) (var_tm (var_zero)) ((funcomp) (ren_tm (shift) (id)) ?sigma0)) ?s0)  =>  first [ unify   (subst_tm sigma0 sigma1 (lam s0)) (hexp)|  musigma   (subst_tm sigma0 sigma1 (lam s0)) (hexp) ]
  |  mu (subst_cmd ((scons) (var_stack (var_zero)) ((funcomp) (ren_stack (id) (shift)) ?sigma1)) ((funcomp) (ren_tm (id) (shift)) ?sigma0) ?s0)  =>  first [ unify   (subst_tm sigma0 sigma1 (mu s0)) (hexp)|  musigma   (subst_tm sigma0 sigma1 (mu s0)) (hexp) ]
  |  lam (ren_tm ?sigma1 ((scons) (var_zero) ((funcomp) (shift) ?sigma0)) ?s0)  =>  first [ unify   (ren_tm sigma0 sigma1 (lam s0)) (hexp)|  musigma   (ren_tm sigma0 sigma1 (lam s0)) (hexp) ]
  |  mu (ren_cmd ((scons) (var_zero) ((funcomp) (shift) ?sigma1)) ?sigma0 ?s0)  =>  first [ unify   (ren_tm sigma0 sigma1 (mu s0)) (hexp)|  musigma   (ren_tm sigma0 sigma1 (mu s0)) (hexp) ]
  |  cons (subst_tm ?sigma1 ?sigma0 ?s0) (subst_stack ?sigma1 ?sigma0 ?s1)  =>  first [ unify   (subst_stack sigma0 sigma1 (cons s0 s1)) (hexp)|  musigma   (subst_stack sigma0 sigma1 (cons s0 s1)) (hexp) ]
  |  cons (ren_tm ?sigma1 ?sigma0 ?s0) (ren_stack ?sigma1 ?sigma0 ?s1)  =>  first [ unify   (ren_stack sigma0 sigma1 (cons s0 s1)) (hexp)|  musigma   (ren_stack sigma0 sigma1 (cons s0 s1)) (hexp) ]
  |  cut (subst_tm ?sigma1 ?sigma0 ?s0) (subst_stack ?sigma1 ?sigma0 ?s1)  =>  first [ unify   (subst_cmd sigma0 sigma1 (cut s0 s1)) (hexp)|  musigma   (subst_cmd sigma0 sigma1 (cut s0 s1)) (hexp) ]
  |  cut (ren_tm ?sigma1 ?sigma0 ?s0) (ren_stack ?sigma1 ?sigma0 ?s1)  =>  first [ unify   (ren_cmd sigma0 sigma1 (cut s0 s1)) (hexp)|  musigma   (ren_cmd sigma0 sigma1 (cut s0 s1)) (hexp) ]
  |  ren_tm ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1) ?s  =>  match   hexp  with
  |  ren_tm ?theta0 ?theta1 ?t  =>  first [ unify   (ren_tm tau0 tau1 (ren_tm sigma0 sigma1 s)) (hexp)|  musigma   (ren_tm tau0 tau1 (ren_tm sigma0 sigma1 s)) (hexp) ]
  end
  |  subst_tm ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1) ?s  =>  match   hexp  with
  |  subst_tm ?theta0 ?theta1 ?t  =>  first [ unify   (subst_tm tau0 tau1 (ren_tm sigma0 sigma1 s)) (hexp)|  musigma   (subst_tm tau0 tau1 (ren_tm sigma0 sigma1 s)) (hexp) ]
  end
  |  subst_tm ((funcomp) (ren_tm ?tau0 ?tau1) ?sigma0) ((funcomp) (ren_stack ?tau0 ?tau1) ?sigma1) ?s  =>  match   hexp  with
  |  ren_tm ?theta0 ?theta1 ?t  =>  first [ unify   (ren_tm tau0 tau1 (subst_tm sigma0 sigma1 s)) (hexp)|  musigma   (ren_tm tau0 tau1 (subst_tm sigma0 sigma1 s)) (hexp) ]
  end
  |  subst_tm ((funcomp) (subst_tm ?tau0 ?tau1) ?sigma0) ((funcomp) (subst_stack ?tau0 ?tau1) ?sigma1) ?s  =>  match   hexp  with
  |  subst_tm ?theta0 ?theta1 ?t  =>  first [ unify   (subst_tm tau0 tau1 (subst_tm sigma0 sigma1 s)) (hexp)|  musigma   (subst_tm tau0 tau1 (subst_tm sigma0 sigma1 s)) (hexp) ]
  end
  |  ren_stack ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1) ?s  =>  match   hexp  with
  |  ren_stack ?theta0 ?theta1 ?t  =>  first [ unify   (ren_stack tau0 tau1 (ren_stack sigma0 sigma1 s)) (hexp)|  musigma   (ren_stack tau0 tau1 (ren_stack sigma0 sigma1 s)) (hexp) ]
  end
  |  subst_stack ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1) ?s  =>  match   hexp  with
  |  subst_stack ?theta0 ?theta1 ?t  =>  first [ unify   (subst_stack tau0 tau1 (ren_stack sigma0 sigma1 s)) (hexp)|  musigma   (subst_stack tau0 tau1 (ren_stack sigma0 sigma1 s)) (hexp) ]
  end
  |  subst_stack ((funcomp) (ren_tm ?tau0 ?tau1) ?sigma0) ((funcomp) (ren_stack ?tau0 ?tau1) ?sigma1) ?s  =>  match   hexp  with
  |  ren_stack ?theta0 ?theta1 ?t  =>  first [ unify   (ren_stack tau0 tau1 (subst_stack sigma0 sigma1 s)) (hexp)|  musigma   (ren_stack tau0 tau1 (subst_stack sigma0 sigma1 s)) (hexp) ]
  end
  |  subst_stack ((funcomp) (subst_tm ?tau0 ?tau1) ?sigma0) ((funcomp) (subst_stack ?tau0 ?tau1) ?sigma1) ?s  =>  match   hexp  with
  |  subst_stack ?theta0 ?theta1 ?t  =>  first [ unify   (subst_stack tau0 tau1 (subst_stack sigma0 sigma1 s)) (hexp)|  musigma   (subst_stack tau0 tau1 (subst_stack sigma0 sigma1 s)) (hexp) ]
  end
  |  ren_cmd ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1) ?s  =>  match   hexp  with
  |  ren_cmd ?theta0 ?theta1 ?t  =>  first [ unify   (ren_cmd tau0 tau1 (ren_cmd sigma0 sigma1 s)) (hexp)|  musigma   (ren_cmd tau0 tau1 (ren_cmd sigma0 sigma1 s)) (hexp) ]
  end
  |  subst_cmd ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1) ?s  =>  match   hexp  with
  |  subst_cmd ?theta0 ?theta1 ?t  =>  first [ unify   (subst_cmd tau0 tau1 (ren_cmd sigma0 sigma1 s)) (hexp)|  musigma   (subst_cmd tau0 tau1 (ren_cmd sigma0 sigma1 s)) (hexp) ]
  end
  |  subst_cmd ((funcomp) (ren_tm ?tau0 ?tau1) ?sigma0) ((funcomp) (ren_stack ?tau0 ?tau1) ?sigma1) ?s  =>  match   hexp  with
  |  ren_cmd ?theta0 ?theta1 ?t  =>  first [ unify   (ren_cmd tau0 tau1 (subst_cmd sigma0 sigma1 s)) (hexp)|  musigma   (ren_cmd tau0 tau1 (subst_cmd sigma0 sigma1 s)) (hexp) ]
  end
  |  subst_cmd ((funcomp) (subst_tm ?tau0 ?tau1) ?sigma0) ((funcomp) (subst_stack ?tau0 ?tau1) ?sigma1) ?s  =>  match   hexp  with
  |  subst_cmd ?theta0 ?theta1 ?t  =>  first [ unify   (subst_cmd tau0 tau1 (subst_cmd sigma0 sigma1 s)) (hexp)|  musigma   (subst_cmd tau0 tau1 (subst_cmd sigma0 sigma1 s)) (hexp) ]
  end
  |  (funcomp) (ren_tm ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_tm ?theta0 ?theta1) ?sigmat  =>  first [ unify   ((funcomp) (ren_tm tau0 tau1) ((funcomp) (ren_tm sigma0 sigma1) sigmas)) (hexp)|  musigma   ((funcomp) (ren_tm tau0 tau1) ((funcomp) (ren_tm sigma0 sigma1) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_tm ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_tm ?theta0 ?theta1) ?sigmat  =>  first [ unify   ((funcomp) (subst_tm tau0 tau1) ((funcomp) (ren_tm sigma0 sigma1) sigmas)) (hexp)|  musigma   ((funcomp) (subst_tm tau0 tau1) ((funcomp) (ren_tm sigma0 sigma1) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_tm ((funcomp) (ren_tm ?tau0 ?tau1) ?sigma0) ((funcomp) (ren_stack ?tau0 ?tau1) ?sigma1)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_tm ?theta0 ?theta1) ?sigmat  =>  first [ unify   ((funcomp) (ren_tm tau0 tau1) ((funcomp) (subst_tm sigma0 sigma1) sigmas)) (hexp)|  musigma   ((funcomp) (ren_tm tau0 tau1) ((funcomp) (subst_tm sigma0 sigma1) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_tm ((funcomp) (subst_tm ?tau0 ?tau1) ?sigma0) ((funcomp) (subst_stack ?tau0 ?tau1) ?sigma1)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_tm ?theta0 ?theta1) ?sigmat  =>  first [ unify   ((funcomp) (subst_tm tau0 tau1) ((funcomp) (subst_tm sigma0 sigma1) sigmas)) (hexp)|  musigma   ((funcomp) (subst_tm tau0 tau1) ((funcomp) (subst_tm sigma0 sigma1) sigmas)) (hexp) ]
  end
  |  (funcomp) (ren_stack ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_stack ?theta0 ?theta1) ?sigmat  =>  first [ unify   ((funcomp) (ren_stack tau0 tau1) ((funcomp) (ren_stack sigma0 sigma1) sigmas)) (hexp)|  musigma   ((funcomp) (ren_stack tau0 tau1) ((funcomp) (ren_stack sigma0 sigma1) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_stack ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_stack ?theta0 ?theta1) ?sigmat  =>  first [ unify   ((funcomp) (subst_stack tau0 tau1) ((funcomp) (ren_stack sigma0 sigma1) sigmas)) (hexp)|  musigma   ((funcomp) (subst_stack tau0 tau1) ((funcomp) (ren_stack sigma0 sigma1) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_stack ((funcomp) (ren_tm ?tau0 ?tau1) ?sigma0) ((funcomp) (ren_stack ?tau0 ?tau1) ?sigma1)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_stack ?theta0 ?theta1) ?sigmat  =>  first [ unify   ((funcomp) (ren_stack tau0 tau1) ((funcomp) (subst_stack sigma0 sigma1) sigmas)) (hexp)|  musigma   ((funcomp) (ren_stack tau0 tau1) ((funcomp) (subst_stack sigma0 sigma1) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_stack ((funcomp) (subst_tm ?tau0 ?tau1) ?sigma0) ((funcomp) (subst_stack ?tau0 ?tau1) ?sigma1)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_stack ?theta0 ?theta1) ?sigmat  =>  first [ unify   ((funcomp) (subst_stack tau0 tau1) ((funcomp) (subst_stack sigma0 sigma1) sigmas)) (hexp)|  musigma   ((funcomp) (subst_stack tau0 tau1) ((funcomp) (subst_stack sigma0 sigma1) sigmas)) (hexp) ]
  end
  |  (funcomp) (ren_cmd ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_cmd ?theta0 ?theta1) ?sigmat  =>  first [ unify   ((funcomp) (ren_cmd tau0 tau1) ((funcomp) (ren_cmd sigma0 sigma1) sigmas)) (hexp)|  musigma   ((funcomp) (ren_cmd tau0 tau1) ((funcomp) (ren_cmd sigma0 sigma1) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_cmd ((funcomp) ?tau0 ?sigma0) ((funcomp) ?tau1 ?sigma1)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_cmd ?theta0 ?theta1) ?sigmat  =>  first [ unify   ((funcomp) (subst_cmd tau0 tau1) ((funcomp) (ren_cmd sigma0 sigma1) sigmas)) (hexp)|  musigma   ((funcomp) (subst_cmd tau0 tau1) ((funcomp) (ren_cmd sigma0 sigma1) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_cmd ((funcomp) (ren_tm ?tau0 ?tau1) ?sigma0) ((funcomp) (ren_stack ?tau0 ?tau1) ?sigma1)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_cmd ?theta0 ?theta1) ?sigmat  =>  first [ unify   ((funcomp) (ren_cmd tau0 tau1) ((funcomp) (subst_cmd sigma0 sigma1) sigmas)) (hexp)|  musigma   ((funcomp) (ren_cmd tau0 tau1) ((funcomp) (subst_cmd sigma0 sigma1) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_cmd ((funcomp) (subst_tm ?tau0 ?tau1) ?sigma0) ((funcomp) (subst_stack ?tau0 ?tau1) ?sigma1)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_cmd ?theta0 ?theta1) ?sigmat  =>  first [ unify   ((funcomp) (subst_cmd tau0 tau1) ((funcomp) (subst_cmd sigma0 sigma1) sigmas)) (hexp)|  musigma   ((funcomp) (subst_cmd tau0 tau1) ((funcomp) (subst_cmd sigma0 sigma1) sigmas)) (hexp) ]
  end
  |  (scons) (ren_tm ?sigma0 ?sigma1 ?s) ((funcomp) (ren_tm ?sigma0 ?sigma1) ?thetag)  =>  match   hexp  with
  |  (funcomp) (ren_tm ?tau0 ?tau1) ?thetah  =>  first [ unify   ((funcomp) (ren_tm sigma0 sigma1) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (ren_tm sigma0 sigma1) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (subst_tm ?sigma0 ?sigma1 ?s) ((funcomp) (subst_tm ?sigma0 ?sigma1) ?thetag)  =>  match   hexp  with
  |  (funcomp) (subst_tm ?tau0 ?tau1) ?thetah  =>  first [ unify   ((funcomp) (subst_tm sigma0 sigma1) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (subst_tm sigma0 sigma1) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (ren_stack ?sigma0 ?sigma1 ?s) ((funcomp) (ren_stack ?sigma0 ?sigma1) ?thetag)  =>  match   hexp  with
  |  (funcomp) (ren_stack ?tau0 ?tau1) ?thetah  =>  first [ unify   ((funcomp) (ren_stack sigma0 sigma1) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (ren_stack sigma0 sigma1) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (subst_stack ?sigma0 ?sigma1 ?s) ((funcomp) (subst_stack ?sigma0 ?sigma1) ?thetag)  =>  match   hexp  with
  |  (funcomp) (subst_stack ?tau0 ?tau1) ?thetah  =>  first [ unify   ((funcomp) (subst_stack sigma0 sigma1) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (subst_stack sigma0 sigma1) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (ren_cmd ?sigma0 ?sigma1 ?s) ((funcomp) (ren_cmd ?sigma0 ?sigma1) ?thetag)  =>  match   hexp  with
  |  (funcomp) (ren_cmd ?tau0 ?tau1) ?thetah  =>  first [ unify   ((funcomp) (ren_cmd sigma0 sigma1) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (ren_cmd sigma0 sigma1) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (subst_cmd ?sigma0 ?sigma1 ?s) ((funcomp) (subst_cmd ?sigma0 ?sigma1) ?thetag)  =>  match   hexp  with
  |  (funcomp) (subst_cmd ?tau0 ?tau1) ?thetah  =>  first [ unify   ((funcomp) (subst_cmd sigma0 sigma1) ((scons) s thetag)) (hexp)|  musigma   ((funcomp) (subst_cmd sigma0 sigma1) ((scons) s thetag)) (hexp) ]
  end
  |  lam ?s0  =>  match   hexp  with
  |  lam ?t0  =>  musigma   (s0) (t0)
  end
  |  mu ?s0  =>  match   hexp  with
  |  mu ?t0  =>  musigma   (s0) (t0)
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
  |  cons ?s0 ?s1  =>  match   hexp  with
  |  cons ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  subst_stack ?sigma0 ?sigma1 ?s  =>  match   hexp  with
  |  subst_stack ?tau0 ?tau1 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1)
  end
  |  ren_stack ?sigma0 ?sigma1 ?s  =>  match   hexp  with
  |  ren_stack ?tau0 ?tau1 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1)
  end
  |  (funcomp) (subst_stack ?sigma0 ?sigma1) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_stack ?tau0 ?tau1) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1)
  end
  |  (funcomp) (ren_stack ?sigma0 ?sigma1) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_stack ?tau0 ?tau1) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1)
  end
  |  cut ?s0 ?s1  =>  match   hexp  with
  |  cut ?t0 ?t1  =>  musigma   (s0) (t0); musigma   (s1) (t1)
  end
  |  subst_cmd ?sigma0 ?sigma1 ?s  =>  match   hexp  with
  |  subst_cmd ?tau0 ?tau1 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1)
  end
  |  ren_cmd ?sigma0 ?sigma1 ?s  =>  match   hexp  with
  |  ren_cmd ?tau0 ?tau1 ?t  =>  musigma   (s) (t); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1)
  end
  |  (funcomp) (subst_cmd ?sigma0 ?sigma1) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_cmd ?tau0 ?tau1) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1)
  end
  |  (funcomp) (ren_cmd ?sigma0 ?sigma1) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_cmd ?tau0 ?tau1) ?tau  =>  musigma   (sigma) (tau); musigma   (sigma0) (tau0); musigma   (sigma1) (tau1)
  end
  end.

Ltac  heuristics gexp hexp :=
  match   gexp  with
  |  ?s  =>  unify   (gexp) (hexp)
  |  (funcomp) (subst_tm ((funcomp) var_tm ?sigma0) ((funcomp) var_stack ?sigma1)) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_tm ?tau0 ?tau1) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (subst_tm ((funcomp) var_tm sigma0) ((funcomp) var_stack sigma1)) sigma = (funcomp) (ren_tm sigma0 sigma1) sigma) as eq by (renamify; reflexivity); rewrite   (eq); unify   ((funcomp) (ren_tm sigma0 sigma1) sigma) (hexp); clear eq
  end
  |  subst_tm ((funcomp) var_tm ?sigma0) ((funcomp) var_stack ?sigma1) ?s  =>  match   hexp  with
  |  ren_tm ?tau0 ?tau1 ?t  =>  let eq := fresh "eq" in
  assert (subst_tm ((funcomp) var_tm sigma0) ((funcomp) var_stack sigma1) s = ren_tm sigma0 sigma1 s) as eq by (renamify; reflexivity); rewrite   (eq); unify   (ren_tm sigma0 sigma1 s) (hexp); clear eq
  end
  |  (funcomp) (subst_stack ((funcomp) var_tm ?sigma0) ((funcomp) var_stack ?sigma1)) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_stack ?tau0 ?tau1) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (subst_stack ((funcomp) var_tm sigma0) ((funcomp) var_stack sigma1)) sigma = (funcomp) (ren_stack sigma0 sigma1) sigma) as eq by (renamify; reflexivity); rewrite   (eq); unify   ((funcomp) (ren_stack sigma0 sigma1) sigma) (hexp); clear eq
  end
  |  subst_stack ((funcomp) var_tm ?sigma0) ((funcomp) var_stack ?sigma1) ?s  =>  match   hexp  with
  |  ren_stack ?tau0 ?tau1 ?t  =>  let eq := fresh "eq" in
  assert (subst_stack ((funcomp) var_tm sigma0) ((funcomp) var_stack sigma1) s = ren_stack sigma0 sigma1 s) as eq by (renamify; reflexivity); rewrite   (eq); unify   (ren_stack sigma0 sigma1 s) (hexp); clear eq
  end
  |  (funcomp) (subst_cmd ((funcomp) var_tm ?sigma0) ((funcomp) var_stack ?sigma1)) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_cmd ?tau0 ?tau1) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (subst_cmd ((funcomp) var_tm sigma0) ((funcomp) var_stack sigma1)) sigma = (funcomp) (ren_cmd sigma0 sigma1) sigma) as eq by (renamify; reflexivity); rewrite   (eq); unify   ((funcomp) (ren_cmd sigma0 sigma1) sigma) (hexp); clear eq
  end
  |  subst_cmd ((funcomp) var_tm ?sigma0) ((funcomp) var_stack ?sigma1) ?s  =>  match   hexp  with
  |  ren_cmd ?tau0 ?tau1 ?t  =>  let eq := fresh "eq" in
  assert (subst_cmd ((funcomp) var_tm sigma0) ((funcomp) var_stack sigma1) s = ren_cmd sigma0 sigma1 s) as eq by (renamify; reflexivity); rewrite   (eq); unify   (ren_cmd sigma0 sigma1 s) (hexp); clear eq
  end
  |  (funcomp) (ren_tm ?sigma0 ?sigma1) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_tm ?tau0 ?tau1) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_tm sigma0 sigma1) sigma = (funcomp) (subst_tm ((funcomp) var_tm sigma0) ((funcomp) var_stack sigma1)) sigma) as eq by (substify; reflexivity); rewrite   (eq); unify   ((funcomp) (subst_tm ((funcomp) var_tm sigma0) ((funcomp) var_stack sigma1)) sigma) (hexp); clear eq
  end
  |  ren_tm ?sigma0 ?sigma1 ?s  =>  match   hexp  with
  |  subst_tm ?tau0 ?tau1 ?t  =>  let eq := fresh "eq" in
  assert (ren_tm sigma0 sigma1 s = subst_tm ((funcomp) var_tm sigma0) ((funcomp) var_stack sigma1) s) as eq by (substify; reflexivity); rewrite   (eq); unify   (subst_tm ((funcomp) var_tm sigma0) ((funcomp) var_stack sigma1) s) (hexp); clear eq
  end
  |  (funcomp) (ren_stack ?sigma0 ?sigma1) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_stack ?tau0 ?tau1) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_stack sigma0 sigma1) sigma = (funcomp) (subst_stack ((funcomp) var_tm sigma0) ((funcomp) var_stack sigma1)) sigma) as eq by (substify; reflexivity); rewrite   (eq); unify   ((funcomp) (subst_stack ((funcomp) var_tm sigma0) ((funcomp) var_stack sigma1)) sigma) (hexp); clear eq
  end
  |  ren_stack ?sigma0 ?sigma1 ?s  =>  match   hexp  with
  |  subst_stack ?tau0 ?tau1 ?t  =>  let eq := fresh "eq" in
  assert (ren_stack sigma0 sigma1 s = subst_stack ((funcomp) var_tm sigma0) ((funcomp) var_stack sigma1) s) as eq by (substify; reflexivity); rewrite   (eq); unify   (subst_stack ((funcomp) var_tm sigma0) ((funcomp) var_stack sigma1) s) (hexp); clear eq
  end
  |  (funcomp) (ren_cmd ?sigma0 ?sigma1) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_cmd ?tau0 ?tau1) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_cmd sigma0 sigma1) sigma = (funcomp) (subst_cmd ((funcomp) var_tm sigma0) ((funcomp) var_stack sigma1)) sigma) as eq by (substify; reflexivity); rewrite   (eq); unify   ((funcomp) (subst_cmd ((funcomp) var_tm sigma0) ((funcomp) var_stack sigma1)) sigma) (hexp); clear eq
  end
  |  ren_cmd ?sigma0 ?sigma1 ?s  =>  match   hexp  with
  |  subst_cmd ?tau0 ?tau1 ?t  =>  let eq := fresh "eq" in
  assert (ren_cmd sigma0 sigma1 s = subst_cmd ((funcomp) var_tm sigma0) ((funcomp) var_stack sigma1) s) as eq by (substify; reflexivity); rewrite   (eq); unify   (subst_cmd ((funcomp) var_tm sigma0) ((funcomp) var_stack sigma1) s) (hexp); clear eq
  end
  |  ?s  =>  musigma   (gexp) (hexp)
  |  subst_tm ((scons) ?stm0 ((funcomp) var_tm ?sigmatm)) ((funcomp) var_stack ?sigmastack) ?stm  =>  match   hexp  with
  |  subst_tm ((scons) ?ttm0 var_tm) var_stack ?ttm  =>  unify   (subst_tm ((scons) stm0 var_tm) var_stack (ren_tm ((scons) (var_zero) ((funcomp) (shift) sigmatm)) sigmastack stm)) (hexp)
  end
  |  subst_cmd ((funcomp) var_tm ?sigmatm) ((scons) ?sstack0 ((funcomp) var_stack ?sigmastack)) ?scmd  =>  match   hexp  with
  |  subst_cmd var_tm ((scons) ?tstack0 var_stack) ?tcmd  =>  unify   (subst_cmd var_tm ((scons) sstack0 var_stack) (ren_cmd sigmatm ((scons) (var_zero) ((funcomp) (shift) sigmastack)) scmd)) (hexp)
  end
  |  subst_tm ((scons) ?stm0 ?sigmatm) ?sigmastack ?stm  =>  match   hexp  with
  |  subst_tm ((scons) ?ttm0 var_tm) var_stack ?ttm  =>  unify   (subst_tm ((scons) stm0 var_tm) var_stack (subst_tm ((scons) (var_tm (var_zero)) ((funcomp) (ren_tm (shift) (id)) sigmatm)) ((funcomp) (ren_stack (shift) (id)) sigmastack) stm)) (hexp)
  end
  |  subst_cmd ?sigmatm ((scons) ?sstack0 ?sigmastack) ?scmd  =>  match   hexp  with
  |  subst_cmd var_tm ((scons) ?tstack0 var_stack) ?tcmd  =>  unify   (subst_cmd var_tm ((scons) sstack0 var_stack) (subst_cmd ((funcomp) (ren_tm (id) (shift)) sigmatm) ((scons) (var_stack (var_zero)) ((funcomp) (ren_stack (id) (shift)) sigmastack)) scmd)) (hexp)
  end
  |  ?s  =>  match   hexp  with
  |  subst_tm ?sigma0 ?sigma1 ?t  =>  unify   (subst_tm var_tm var_stack s) (hexp)
  |  ren_tm ?sigma0 ?sigma1 ?t  =>  unify   (ren_tm (id) (id) s) (hexp)
  |  subst_stack ?sigma0 ?sigma1 ?t  =>  unify   (subst_stack var_tm var_stack s) (hexp)
  |  ren_stack ?sigma0 ?sigma1 ?t  =>  unify   (ren_stack (id) (id) s) (hexp)
  |  subst_cmd ?sigma0 ?sigma1 ?t  =>  unify   (subst_cmd var_tm var_stack s) (hexp)
  |  ren_cmd ?sigma0 ?sigma1 ?t  =>  unify   (ren_cmd (id) (id) s) (hexp)
  end
  |  lam ?s0  =>  match   hexp  with
  |  lam ?t0  =>  heuristics   (s0) (t0)
  end
  |  mu ?s0  =>  match   hexp  with
  |  mu ?t0  =>  heuristics   (s0) (t0)
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
  |  cons ?s0 ?s1  =>  match   hexp  with
  |  cons ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  subst_stack ?sigma0 ?sigma1 ?s  =>  match   hexp  with
  |  subst_stack ?tau0 ?tau1 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1)
  end
  |  ren_stack ?sigma0 ?sigma1 ?s  =>  match   hexp  with
  |  ren_stack ?tau0 ?tau1 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1)
  end
  |  (funcomp) (subst_stack ?sigma0 ?sigma1) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_stack ?tau0 ?tau1) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1)
  end
  |  (funcomp) (ren_stack ?sigma0 ?sigma1) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_stack ?tau0 ?tau1) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1)
  end
  |  cut ?s0 ?s1  =>  match   hexp  with
  |  cut ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  subst_cmd ?sigma0 ?sigma1 ?s  =>  match   hexp  with
  |  subst_cmd ?tau0 ?tau1 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1)
  end
  |  ren_cmd ?sigma0 ?sigma1 ?s  =>  match   hexp  with
  |  ren_cmd ?tau0 ?tau1 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1)
  end
  |  (funcomp) (subst_cmd ?sigma0 ?sigma1) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_cmd ?tau0 ?tau1) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1)
  end
  |  (funcomp) (ren_cmd ?sigma0 ?sigma1) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_cmd ?tau0 ?tau1) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0); heuristics   (sigma1) (tau1)
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
