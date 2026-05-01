Require Import Syntax.

Ltac  sigma_min gexp hexp :=
  match   gexp  with
  |  pair ?s0 ?s1  =>  match   hexp  with
  |  pair ?t0 ?t1  =>  sigma_min   (s0) (t0); sigma_min   (s1) (t1)
  end
  |  inj ?s0 ?s1  =>  match   hexp  with
  |  inj ?t0 ?t1  =>  sigma_min   (s0) (t0); sigma_min   (s1) (t1)
  end
  |  thunk ?s0  =>  match   hexp  with
  |  thunk ?t0  =>  sigma_min   (s0) (t0)
  end
  |  subst_value ?sigma0 ?s  =>  match   hexp  with
  |  subst_value ?tau0 ?t  =>  sigma_min   (s) (t); sigma_min   (sigma0) (tau0)
  end
  |  ren_value ?sigma0 ?s  =>  match   hexp  with
  |  ren_value ?tau0 ?t  =>  sigma_min   (s) (t); sigma_min   (sigma0) (tau0)
  end
  |  (funcomp) (subst_value ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_value ?tau0) ?tau  =>  sigma_min   (sigma) (tau); sigma_min   (sigma0) (tau0)
  end
  |  (funcomp) (ren_value ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_value ?tau0) ?tau  =>  sigma_min   (sigma) (tau); sigma_min   (sigma0) (tau0)
  end
  |  force ?s0  =>  match   hexp  with
  |  force ?t0  =>  sigma_min   (s0) (t0)
  end
  |  lambda ?s0  =>  match   hexp  with
  |  lambda ?t0  =>  sigma_min   (s0) (t0)
  end
  |  app ?s0 ?s1  =>  match   hexp  with
  |  app ?t0 ?t1  =>  sigma_min   (s0) (t0); sigma_min   (s1) (t1)
  end
  |  tuple ?s0 ?s1  =>  match   hexp  with
  |  tuple ?t0 ?t1  =>  sigma_min   (s0) (t0); sigma_min   (s1) (t1)
  end
  |  ret ?s0  =>  match   hexp  with
  |  ret ?t0  =>  sigma_min   (s0) (t0)
  end
  |  letin ?s0 ?s1  =>  match   hexp  with
  |  letin ?t0 ?t1  =>  sigma_min   (s0) (t0); sigma_min   (s1) (t1)
  end
  |  proj ?s0 ?s1  =>  match   hexp  with
  |  proj ?t0 ?t1  =>  sigma_min   (s0) (t0); sigma_min   (s1) (t1)
  end
  |  caseZ ?s0  =>  match   hexp  with
  |  caseZ ?t0  =>  sigma_min   (s0) (t0)
  end
  |  caseS ?s0 ?s1 ?s2  =>  match   hexp  with
  |  caseS ?t0 ?t1 ?t2  =>  sigma_min   (s0) (t0); sigma_min   (s1) (t1); sigma_min   (s2) (t2)
  end
  |  caseP ?s0 ?s1  =>  match   hexp  with
  |  caseP ?t0 ?t1  =>  sigma_min   (s0) (t0); sigma_min   (s1) (t1)
  end
  |  subst_comp ?sigma0 ?s  =>  match   hexp  with
  |  subst_comp ?tau0 ?t  =>  sigma_min   (s) (t); sigma_min   (sigma0) (tau0)
  end
  |  ren_comp ?sigma0 ?s  =>  match   hexp  with
  |  ren_comp ?tau0 ?t  =>  sigma_min   (s) (t); sigma_min   (sigma0) (tau0)
  end
  |  (funcomp) (subst_comp ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_comp ?tau0) ?tau  =>  sigma_min   (sigma) (tau); sigma_min   (sigma0) (tau0)
  end
  |  (funcomp) (ren_comp ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_comp ?tau0) ?tau  =>  sigma_min   (sigma) (tau); sigma_min   (sigma0) (tau0)
  end
  |  ?s  =>  unify   (gexp) (hexp)
  |  pair (subst_value ?sigma0 ?s0) (subst_value ?sigma0 ?s1)  =>  first [ unify   (subst_value sigma0 (pair s0 s1)) (hexp)|  sigma_min   (subst_value sigma0 (pair s0 s1)) (hexp) ]
  |  inj ((fun x => x) ?s0) (subst_value ?sigma0 ?s1)  =>  first [ unify   (subst_value sigma0 (inj s0 s1)) (hexp)|  sigma_min   (subst_value sigma0 (inj s0 s1)) (hexp) ]
  |  thunk (subst_comp ?sigma0 ?s0)  =>  first [ unify   (subst_value sigma0 (thunk s0)) (hexp)|  sigma_min   (subst_value sigma0 (thunk s0)) (hexp) ]
  |  pair (ren_value ?sigma0 ?s0) (ren_value ?sigma0 ?s1)  =>  first [ unify   (ren_value sigma0 (pair s0 s1)) (hexp)|  sigma_min   (ren_value sigma0 (pair s0 s1)) (hexp) ]
  |  inj ((fun x => x) ?s0) (ren_value ?sigma0 ?s1)  =>  first [ unify   (ren_value sigma0 (inj s0 s1)) (hexp)|  sigma_min   (ren_value sigma0 (inj s0 s1)) (hexp) ]
  |  thunk (ren_comp ?sigma0 ?s0)  =>  first [ unify   (ren_value sigma0 (thunk s0)) (hexp)|  sigma_min   (ren_value sigma0 (thunk s0)) (hexp) ]
  |  force (subst_value ?sigma0 ?s0)  =>  first [ unify   (subst_comp sigma0 (force s0)) (hexp)|  sigma_min   (subst_comp sigma0 (force s0)) (hexp) ]
  |  lambda (subst_comp ((scons) (var_value (var_zero)) ((funcomp) (ren_value (shift)) ?sigma0)) ?s0)  =>  first [ unify   (subst_comp sigma0 (lambda s0)) (hexp)|  sigma_min   (subst_comp sigma0 (lambda s0)) (hexp) ]
  |  app (subst_comp ?sigma0 ?s0) (subst_value ?sigma0 ?s1)  =>  first [ unify   (subst_comp sigma0 (app s0 s1)) (hexp)|  sigma_min   (subst_comp sigma0 (app s0 s1)) (hexp) ]
  |  tuple (subst_comp ?sigma0 ?s0) (subst_comp ?sigma0 ?s1)  =>  first [ unify   (subst_comp sigma0 (tuple s0 s1)) (hexp)|  sigma_min   (subst_comp sigma0 (tuple s0 s1)) (hexp) ]
  |  ret (subst_value ?sigma0 ?s0)  =>  first [ unify   (subst_comp sigma0 (ret s0)) (hexp)|  sigma_min   (subst_comp sigma0 (ret s0)) (hexp) ]
  |  letin (subst_comp ?sigma0 ?s0) (subst_comp ((scons) (var_value (var_zero)) ((funcomp) (ren_value (shift)) ?sigma0)) ?s1)  =>  first [ unify   (subst_comp sigma0 (letin s0 s1)) (hexp)|  sigma_min   (subst_comp sigma0 (letin s0 s1)) (hexp) ]
  |  proj ((fun x => x) ?s0) (subst_comp ?sigma0 ?s1)  =>  first [ unify   (subst_comp sigma0 (proj s0 s1)) (hexp)|  sigma_min   (subst_comp sigma0 (proj s0 s1)) (hexp) ]
  |  caseZ (subst_value ?sigma0 ?s0)  =>  first [ unify   (subst_comp sigma0 (caseZ s0)) (hexp)|  sigma_min   (subst_comp sigma0 (caseZ s0)) (hexp) ]
  |  caseS (subst_value ?sigma0 ?s0) (subst_comp ((scons) (var_value (var_zero)) ((funcomp) (ren_value (shift)) ?sigma0)) ?s1) (subst_comp ((scons) (var_value (var_zero)) ((funcomp) (ren_value (shift)) ?sigma0)) ?s2)  =>  first [ unify   (subst_comp sigma0 (caseS s0 s1 s2)) (hexp)|  sigma_min   (subst_comp sigma0 (caseS s0 s1 s2)) (hexp) ]
  |  caseP (subst_value ?sigma0 ?s0) (subst_comp ((scons) (var_value (var_zero)) ((scons) (var_value ((shift) (var_zero))) ((funcomp) (ren_value ((funcomp) (shift) (shift))) ?sigma0))) ?s1)  =>  first [ unify   (subst_comp sigma0 (caseP s0 s1)) (hexp)|  sigma_min   (subst_comp sigma0 (caseP s0 s1)) (hexp) ]
  |  force (ren_value ?sigma0 ?s0)  =>  first [ unify   (ren_comp sigma0 (force s0)) (hexp)|  sigma_min   (ren_comp sigma0 (force s0)) (hexp) ]
  |  lambda (ren_comp ((scons) (var_zero) ((funcomp) (shift) ?sigma0)) ?s0)  =>  first [ unify   (ren_comp sigma0 (lambda s0)) (hexp)|  sigma_min   (ren_comp sigma0 (lambda s0)) (hexp) ]
  |  app (ren_comp ?sigma0 ?s0) (ren_value ?sigma0 ?s1)  =>  first [ unify   (ren_comp sigma0 (app s0 s1)) (hexp)|  sigma_min   (ren_comp sigma0 (app s0 s1)) (hexp) ]
  |  tuple (ren_comp ?sigma0 ?s0) (ren_comp ?sigma0 ?s1)  =>  first [ unify   (ren_comp sigma0 (tuple s0 s1)) (hexp)|  sigma_min   (ren_comp sigma0 (tuple s0 s1)) (hexp) ]
  |  ret (ren_value ?sigma0 ?s0)  =>  first [ unify   (ren_comp sigma0 (ret s0)) (hexp)|  sigma_min   (ren_comp sigma0 (ret s0)) (hexp) ]
  |  letin (ren_comp ?sigma0 ?s0) (ren_comp ((scons) (var_zero) ((funcomp) (shift) ?sigma0)) ?s1)  =>  first [ unify   (ren_comp sigma0 (letin s0 s1)) (hexp)|  sigma_min   (ren_comp sigma0 (letin s0 s1)) (hexp) ]
  |  proj ((fun x => x) ?s0) (ren_comp ?sigma0 ?s1)  =>  first [ unify   (ren_comp sigma0 (proj s0 s1)) (hexp)|  sigma_min   (ren_comp sigma0 (proj s0 s1)) (hexp) ]
  |  caseZ (ren_value ?sigma0 ?s0)  =>  first [ unify   (ren_comp sigma0 (caseZ s0)) (hexp)|  sigma_min   (ren_comp sigma0 (caseZ s0)) (hexp) ]
  |  caseS (ren_value ?sigma0 ?s0) (ren_comp ((scons) (var_zero) ((funcomp) (shift) ?sigma0)) ?s1) (ren_comp ((scons) (var_zero) ((funcomp) (shift) ?sigma0)) ?s2)  =>  first [ unify   (ren_comp sigma0 (caseS s0 s1 s2)) (hexp)|  sigma_min   (ren_comp sigma0 (caseS s0 s1 s2)) (hexp) ]
  |  caseP (ren_value ?sigma0 ?s0) (ren_comp ((scons) (var_zero) ((scons) ((shift) (var_zero)) ((funcomp) ((funcomp) (shift) (shift)) ?sigma0))) ?s1)  =>  first [ unify   (ren_comp sigma0 (caseP s0 s1)) (hexp)|  sigma_min   (ren_comp sigma0 (caseP s0 s1)) (hexp) ]
  |  ren_value ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  ren_value ?theta0 ?t  =>  first [ unify   (ren_value tau0 (ren_value sigma0 s)) (hexp)|  sigma_min   (ren_value tau0 (ren_value sigma0 s)) (hexp) ]
  end
  |  subst_value ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  subst_value ?theta0 ?t  =>  first [ unify   (subst_value tau0 (ren_value sigma0 s)) (hexp)|  sigma_min   (subst_value tau0 (ren_value sigma0 s)) (hexp) ]
  end
  |  subst_value ((funcomp) (ren_value ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  ren_value ?theta0 ?t  =>  first [ unify   (ren_value tau0 (subst_value sigma0 s)) (hexp)|  sigma_min   (ren_value tau0 (subst_value sigma0 s)) (hexp) ]
  end
  |  subst_value ((funcomp) (subst_value ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  subst_value ?theta0 ?t  =>  first [ unify   (subst_value tau0 (subst_value sigma0 s)) (hexp)|  sigma_min   (subst_value tau0 (subst_value sigma0 s)) (hexp) ]
  end
  |  ren_comp ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  ren_comp ?theta0 ?t  =>  first [ unify   (ren_comp tau0 (ren_comp sigma0 s)) (hexp)|  sigma_min   (ren_comp tau0 (ren_comp sigma0 s)) (hexp) ]
  end
  |  subst_comp ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  subst_comp ?theta0 ?t  =>  first [ unify   (subst_comp tau0 (ren_comp sigma0 s)) (hexp)|  sigma_min   (subst_comp tau0 (ren_comp sigma0 s)) (hexp) ]
  end
  |  subst_comp ((funcomp) (ren_value ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  ren_comp ?theta0 ?t  =>  first [ unify   (ren_comp tau0 (subst_comp sigma0 s)) (hexp)|  sigma_min   (ren_comp tau0 (subst_comp sigma0 s)) (hexp) ]
  end
  |  subst_comp ((funcomp) (subst_value ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  subst_comp ?theta0 ?t  =>  first [ unify   (subst_comp tau0 (subst_comp sigma0 s)) (hexp)|  sigma_min   (subst_comp tau0 (subst_comp sigma0 s)) (hexp) ]
  end
  |  (funcomp) (ren_value ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_value ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_value tau0) ((funcomp) (ren_value sigma0) sigmas)) (hexp)|  sigma_min   ((funcomp) (ren_value tau0) ((funcomp) (ren_value sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_value ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_value ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_value tau0) ((funcomp) (ren_value sigma0) sigmas)) (hexp)|  sigma_min   ((funcomp) (subst_value tau0) ((funcomp) (ren_value sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_value ((funcomp) (ren_value ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_value ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_value tau0) ((funcomp) (subst_value sigma0) sigmas)) (hexp)|  sigma_min   ((funcomp) (ren_value tau0) ((funcomp) (subst_value sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_value ((funcomp) (subst_value ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_value ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_value tau0) ((funcomp) (subst_value sigma0) sigmas)) (hexp)|  sigma_min   ((funcomp) (subst_value tau0) ((funcomp) (subst_value sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (ren_comp ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_comp ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_comp tau0) ((funcomp) (ren_comp sigma0) sigmas)) (hexp)|  sigma_min   ((funcomp) (ren_comp tau0) ((funcomp) (ren_comp sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_comp ((funcomp) ?tau0 ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_comp ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_comp tau0) ((funcomp) (ren_comp sigma0) sigmas)) (hexp)|  sigma_min   ((funcomp) (subst_comp tau0) ((funcomp) (ren_comp sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_comp ((funcomp) (ren_value ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (ren_comp ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (ren_comp tau0) ((funcomp) (subst_comp sigma0) sigmas)) (hexp)|  sigma_min   ((funcomp) (ren_comp tau0) ((funcomp) (subst_comp sigma0) sigmas)) (hexp) ]
  end
  |  (funcomp) (subst_comp ((funcomp) (subst_value ?tau0) ?sigma0)) ?sigmas  =>  match   hexp  with
  |  (funcomp) (subst_comp ?theta0) ?sigmat  =>  first [ unify   ((funcomp) (subst_comp tau0) ((funcomp) (subst_comp sigma0) sigmas)) (hexp)|  sigma_min   ((funcomp) (subst_comp tau0) ((funcomp) (subst_comp sigma0) sigmas)) (hexp) ]
  end
  |  (scons) (ren_value ?sigma0 ?s) ((funcomp) (ren_value ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (ren_value ?tau0) ?thetah  =>  first [ unify   ((funcomp) (ren_value sigma0) ((scons) s thetag)) (hexp)|  sigma_min   ((funcomp) (ren_value sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (subst_value ?sigma0 ?s) ((funcomp) (subst_value ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (subst_value ?tau0) ?thetah  =>  first [ unify   ((funcomp) (subst_value sigma0) ((scons) s thetag)) (hexp)|  sigma_min   ((funcomp) (subst_value sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (ren_comp ?sigma0 ?s) ((funcomp) (ren_comp ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (ren_comp ?tau0) ?thetah  =>  first [ unify   ((funcomp) (ren_comp sigma0) ((scons) s thetag)) (hexp)|  sigma_min   ((funcomp) (ren_comp sigma0) ((scons) s thetag)) (hexp) ]
  end
  |  (scons) (subst_comp ?sigma0 ?s) ((funcomp) (subst_comp ?sigma0) ?thetag)  =>  match   hexp  with
  |  (funcomp) (subst_comp ?tau0) ?thetah  =>  first [ unify   ((funcomp) (subst_comp sigma0) ((scons) s thetag)) (hexp)|  sigma_min   ((funcomp) (subst_comp sigma0) ((scons) s thetag)) (hexp) ]
  end
  end.

Ltac  heuristics gexp hexp :=
  match   gexp  with
  |  (funcomp) (subst_value ((funcomp) var_value ?sigma0)) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_value ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (subst_value ((funcomp) var_value sigma0)) sigma = (funcomp) (ren_value sigma0) sigma) as eq by (renamify; reflexivity); rewrite   (eq); clear eq; heuristics   ((funcomp) (ren_value sigma0) sigma) (hexp)
  end
  |  subst_value ((funcomp) var_value ?sigma0) ?s  =>  match   hexp  with
  |  ren_value ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (subst_value ((funcomp) var_value sigma0) s = ren_value sigma0 s) as eq by (renamify; reflexivity); rewrite   (eq); clear eq; heuristics   (ren_value sigma0 s) (hexp)
  end
  |  (funcomp) (subst_comp ((funcomp) var_value ?sigma0)) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_comp ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (subst_comp ((funcomp) var_value sigma0)) sigma = (funcomp) (ren_comp sigma0) sigma) as eq by (renamify; reflexivity); rewrite   (eq); clear eq; heuristics   ((funcomp) (ren_comp sigma0) sigma) (hexp)
  end
  |  subst_comp ((funcomp) var_value ?sigma0) ?s  =>  match   hexp  with
  |  ren_comp ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (subst_comp ((funcomp) var_value sigma0) s = ren_comp sigma0 s) as eq by (renamify; reflexivity); rewrite   (eq); clear eq; heuristics   (ren_comp sigma0 s) (hexp)
  end
  |  (funcomp) (ren_value ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_value ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_value sigma0) sigma = (funcomp) (subst_value ((funcomp) var_value sigma0)) sigma) as eq by (substify; reflexivity); rewrite   (eq); clear eq; heuristics   ((funcomp) (subst_value ((funcomp) var_value sigma0)) sigma) (hexp)
  end
  |  ren_value ?sigma0 ?s  =>  match   hexp  with
  |  subst_value ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (ren_value sigma0 s = subst_value ((funcomp) var_value sigma0) s) as eq by (substify; reflexivity); rewrite   (eq); clear eq; heuristics   (subst_value ((funcomp) var_value sigma0) s) (hexp)
  end
  |  (funcomp) (ren_comp ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_comp ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_comp sigma0) sigma = (funcomp) (subst_comp ((funcomp) var_value sigma0)) sigma) as eq by (substify; reflexivity); rewrite   (eq); clear eq; heuristics   ((funcomp) (subst_comp ((funcomp) var_value sigma0)) sigma) (hexp)
  end
  |  ren_comp ?sigma0 ?s  =>  match   hexp  with
  |  subst_comp ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (ren_comp sigma0 s = subst_comp ((funcomp) var_value sigma0) s) as eq by (substify; reflexivity); rewrite   (eq); clear eq; heuristics   (subst_comp ((funcomp) var_value sigma0) s) (hexp)
  end
  |  ?s  =>  sigma_min   (gexp) (hexp)
  |  subst_comp ((scons) ?svalue0 ((funcomp) var_value ?sigmavalue)) ?scomp  =>  match   hexp  with
  |  subst_comp ((scons) ?tvalue0 var_value) ?tcomp  =>  unify   (subst_comp ((scons) svalue0 var_value) (ren_comp ((scons) (var_zero) ((funcomp) (shift) sigmavalue)) scomp)) (hexp)
  end
  |  subst_comp ((scons) ?svalue0 ((funcomp) var_value ?sigmavalue)) ?scomp  =>  match   hexp  with
  |  subst_comp ((scons) ?tvalue0 var_value) ?tcomp  =>  unify   (subst_comp ((scons) svalue0 var_value) (ren_comp ((scons) (var_zero) ((funcomp) (shift) sigmavalue)) scomp)) (hexp)
  end
  |  subst_comp ((scons) ?svalue0 ((funcomp) var_value ?sigmavalue)) ?scomp  =>  match   hexp  with
  |  subst_comp ((scons) ?tvalue0 var_value) ?tcomp  =>  unify   (subst_comp ((scons) svalue0 var_value) (ren_comp ((scons) (var_zero) ((funcomp) (shift) sigmavalue)) scomp)) (hexp)
  end
  |  subst_comp ((scons) ?svalue0 ((funcomp) var_value ?sigmavalue)) ?scomp  =>  match   hexp  with
  |  subst_comp ((scons) ?tvalue0 var_value) ?tcomp  =>  unify   (subst_comp ((scons) svalue0 var_value) (ren_comp ((scons) (var_zero) ((funcomp) (shift) sigmavalue)) scomp)) (hexp)
  end
  |  subst_comp ((scons) ?svalue1 ((scons) ?svalue0 ((funcomp) var_value ?sigmavalue))) ?scomp  =>  match   hexp  with
  |  subst_comp ((scons) ?tvalue1 ((scons) ?tvalue0 var_value)) ?tcomp  =>  unify   (subst_comp ((scons) svalue1 ((scons) svalue0 var_value)) (ren_comp ((scons) (var_zero) ((scons) ((shift) (var_zero)) ((funcomp) ((funcomp) (shift) (shift)) sigmavalue))) scomp)) (hexp)
  end
  |  subst_comp ((scons) ?svalue0 ?sigmavalue) ?scomp  =>  match   hexp  with
  |  subst_comp ((scons) ?tvalue0 var_value) ?tcomp  =>  unify   (subst_comp ((scons) svalue0 var_value) (subst_comp ((scons) (var_value (var_zero)) ((funcomp) (ren_value (shift)) sigmavalue)) scomp)) (hexp)
  end
  |  subst_comp ((scons) ?svalue0 ?sigmavalue) ?scomp  =>  match   hexp  with
  |  subst_comp ((scons) ?tvalue0 var_value) ?tcomp  =>  unify   (subst_comp ((scons) svalue0 var_value) (subst_comp ((scons) (var_value (var_zero)) ((funcomp) (ren_value (shift)) sigmavalue)) scomp)) (hexp)
  end
  |  subst_comp ((scons) ?svalue0 ?sigmavalue) ?scomp  =>  match   hexp  with
  |  subst_comp ((scons) ?tvalue0 var_value) ?tcomp  =>  unify   (subst_comp ((scons) svalue0 var_value) (subst_comp ((scons) (var_value (var_zero)) ((funcomp) (ren_value (shift)) sigmavalue)) scomp)) (hexp)
  end
  |  subst_comp ((scons) ?svalue0 ?sigmavalue) ?scomp  =>  match   hexp  with
  |  subst_comp ((scons) ?tvalue0 var_value) ?tcomp  =>  unify   (subst_comp ((scons) svalue0 var_value) (subst_comp ((scons) (var_value (var_zero)) ((funcomp) (ren_value (shift)) sigmavalue)) scomp)) (hexp)
  end
  |  subst_comp ((scons) ?svalue1 ((scons) ?svalue0 ?sigmavalue)) ?scomp  =>  match   hexp  with
  |  subst_comp ((scons) ?tvalue1 ((scons) ?tvalue0 var_value)) ?tcomp  =>  unify   (subst_comp ((scons) svalue1 ((scons) svalue0 var_value)) (subst_comp ((scons) (var_value (var_zero)) ((scons) (var_value ((shift) (var_zero))) ((funcomp) (ren_value ((funcomp) (shift) (shift))) sigmavalue))) scomp)) (hexp)
  end
  |  ?s  =>  match   hexp  with
  |  subst_value ?sigma0 ?t  =>  unify   (subst_value var_value s) (hexp)
  |  ren_value ?sigma0 ?t  =>  unify   (ren_value (id) s) (hexp)
  |  subst_comp ?sigma0 ?t  =>  unify   (subst_comp var_value s) (hexp)
  |  ren_comp ?sigma0 ?t  =>  unify   (ren_comp (id) s) (hexp)
  end
  |  pair ?s0 ?s1  =>  match   hexp  with
  |  pair ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  inj ?s0 ?s1  =>  match   hexp  with
  |  inj ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  thunk ?s0  =>  match   hexp  with
  |  thunk ?t0  =>  heuristics   (s0) (t0)
  end
  |  subst_value ?sigma0 ?s  =>  match   hexp  with
  |  subst_value ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  ren_value ?sigma0 ?s  =>  match   hexp  with
  |  ren_value ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (subst_value ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_value ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (ren_value ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_value ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  |  force ?s0  =>  match   hexp  with
  |  force ?t0  =>  heuristics   (s0) (t0)
  end
  |  lambda ?s0  =>  match   hexp  with
  |  lambda ?t0  =>  heuristics   (s0) (t0)
  end
  |  app ?s0 ?s1  =>  match   hexp  with
  |  app ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  tuple ?s0 ?s1  =>  match   hexp  with
  |  tuple ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  ret ?s0  =>  match   hexp  with
  |  ret ?t0  =>  heuristics   (s0) (t0)
  end
  |  letin ?s0 ?s1  =>  match   hexp  with
  |  letin ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  proj ?s0 ?s1  =>  match   hexp  with
  |  proj ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  caseZ ?s0  =>  match   hexp  with
  |  caseZ ?t0  =>  heuristics   (s0) (t0)
  end
  |  caseS ?s0 ?s1 ?s2  =>  match   hexp  with
  |  caseS ?t0 ?t1 ?t2  =>  heuristics   (s0) (t0); heuristics   (s1) (t1); heuristics   (s2) (t2)
  end
  |  caseP ?s0 ?s1  =>  match   hexp  with
  |  caseP ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  subst_comp ?sigma0 ?s  =>  match   hexp  with
  |  subst_comp ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  ren_comp ?sigma0 ?s  =>  match   hexp  with
  |  ren_comp ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (subst_comp ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_comp ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (ren_comp ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_comp ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  end.


(** asimpl in this development folds back everything to typeclass form. My assumption was that it wouldn't but I could have such a unfolder function generically*)
Ltac unfolder :=  unfold ids in *; unfold VarInstance_value in *;     
  unfold subst1 in *; unfold Subst_comp in *;  unfold Subst_value in *;  unfold ren1 in *;   unfold Ren_value in *.



Ltac match_concl_goal  H := unfolder;
  let ty_hyp  := type of H in
  match goal with
  | [ |- ?Pr ?garg1 ?garg2 ?garg3 ?garg4 ?garg5 ?garg6] => match ty_hyp with
                                                  | Pr ?harg1 ?harg2 ?harg3 ?harg4 ?harg5 ?harg6 => heuristics garg1 harg1;
                                                                                                   heuristics garg2 harg2;
                                                                                                   heuristics garg3 harg3;
                                                                                                   heuristics garg4 harg4;
                                                                                                   heuristics garg5 harg5;
                                                                                                   heuristics garg6 harg6
                                                                                      
                                                  end   
  | [ |- ?Pr ?garg1 ?garg2 ?garg3 ?garg4 ?garg5] =>  match ty_hyp with
                                                  | Pr ?harg1 ?harg2 ?harg3 ?harg4 ?harg5 => heuristics garg1 harg1;
                                                                                            heuristics garg2 harg2;
                                                                                            heuristics garg3 harg3;
                                                                                            heuristics garg4 harg4;
                                                                                            heuristics garg5 harg5
                                                                                      
                                                  end    
    
  | [ |- ?Pr ?garg1 ?garg2 ?garg3 ?garg4 ] => match ty_hyp with
                                            | Pr ?harg1 ?harg2 ?harg3 ?harg4 => heuristics garg1 harg1;
                                                                               heuristics garg2 harg2;
                                                                               heuristics garg3 harg3;
                                                                               heuristics garg4 harg4 
                                            end    
  
  | [ |- ?Pr ?garg1 ?garg2 ?garg3 ] => match ty_hyp with
                                     | Pr ?harg1 ?harg2 ?harg3 => heuristics garg1 harg1;
                                                                 heuristics garg2 harg2;
                                                                 heuristics garg3 harg3
                                     end    

  | [ |- ?Pr ?garg1 ?garg2 ] => match ty_hyp with
                              | Pr ?harg1 ?harg2 => heuristics garg1 harg1;
                                                   heuristics garg2 harg2
                              end
                                     
  | [ |- ?Pr ?garg1 ] => match ty_hyp with
                       | Pr ?harg1 =>  heuristics garg1 harg1
                       end
  end.




Ltac premises_to_subgoals H n :=    
  match (eval compute in n) with
  | 0 => match_concl_goal H;
        asimpl in H;
        exact H
  | _ => let ty_hyp := type of H in
        match ty_hyp with
        | ?ant -> ?concl => let z := fresh "z" in
                           evar (z: ant);
                           specialize (H ?z);
                           premises_to_subgoals H (n-1);
                           clear z
        end                         
  end.
  

(** qvar_to_evar is not working as expected in the Rocq version 8.8.2 *)
Ltac qvar_to_evar H n :=
  match (eval compute in n) with
  | 0 => let H' := fresh "H" in
        pose proof H as H';
        first [ premises_to_subgoals H' 0
              | premises_to_subgoals H' 1
              | premises_to_subgoals H' 2
              | premises_to_subgoals H' 3
              | premises_to_subgoals H' 4
              | premises_to_subgoals H' 5
              | premises_to_subgoals H' 6
              | premises_to_subgoals H' 7
              | premises_to_subgoals H' 8
              | premises_to_subgoals H' 9
              | premises_to_subgoals H' 10];
        clear H'
  | _ => let ty_hyp := type of H in
        match ty_hyp with
        | forall (x: ?T), ?rest => let y := fresh "y" in
                             evar (y: T);
                             specialize (H ?y);
                             qvar_to_evar H (n-1);
                             clear y
                                          
        end
  end.
  
    



Ltac as_apply H' :=  unshelve (intros; asimpl;
  let H := fresh "H" in
  pose proof H' as H;
  asimpl in H;
  first [ qvar_to_evar H 0
        | qvar_to_evar H 1
        | qvar_to_evar H 2
        | qvar_to_evar H 3
        | qvar_to_evar H 4
        | qvar_to_evar H 5
        | qvar_to_evar H 6
        | qvar_to_evar H 7
        | qvar_to_evar H 8
        | qvar_to_evar H 9
        | qvar_to_evar H 10
        | qvar_to_evar H 11
        | qvar_to_evar H 12
        | qvar_to_evar H 13
        | qvar_to_evar H 14
        | qvar_to_evar H 15]).


