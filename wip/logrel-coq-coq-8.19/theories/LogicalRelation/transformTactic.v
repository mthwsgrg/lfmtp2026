From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms UntypedReduction Weakening GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Induction Reflexivity Irrelevance Escape.


 
Ltac  heuristics gexp hexp :=
  match   gexp  with
  |  ?s  =>  unify   (gexp) (hexp)
  |  subst_term ((scons) ?sterm0 ((funcomp) tRel ?sigmaterm)) ?sterm  =>  match   hexp  with
  |  subst_term ((scons) ?tterm0 tRel) ?tterm  =>  unify   (subst_term ((scons) sterm0 tRel) (ren_term ((scons) (0) ((funcomp) (shift) sigmaterm)) sterm)) (hexp)
  end
  |  subst_term ((scons) ?sterm0 ((funcomp) tRel ?sigmaterm)) ?sterm  =>  match   hexp  with
  |  subst_term ((scons) ?tterm0 tRel) ?tterm  =>  unify   (subst_term ((scons) sterm0 tRel) (ren_term ((scons) (0) ((funcomp) (shift) sigmaterm)) sterm)) (hexp)
  end
  |  subst_term ((scons) ?sterm0 ((funcomp) tRel ?sigmaterm)) ?sterm  =>  match   hexp  with
  |  subst_term ((scons) ?tterm0 tRel) ?tterm  =>  unify   (subst_term ((scons) sterm0 tRel) (ren_term ((scons) (0) ((funcomp) (shift) sigmaterm)) sterm)) (hexp)
  end
  |  subst_term ((scons) ?sterm0 ((funcomp) tRel ?sigmaterm)) ?sterm  =>  match   hexp  with
  |  subst_term ((scons) ?tterm0 tRel) ?tterm  =>  unify   (subst_term ((scons) sterm0 tRel) (ren_term ((scons) (0) ((funcomp) (shift) sigmaterm)) sterm)) (hexp)
  end
  |  subst_term ((scons) ?sterm0 ((funcomp) tRel ?sigmaterm)) ?sterm  =>  match   hexp  with
  |  subst_term ((scons) ?tterm0 tRel) ?tterm  =>  unify   (subst_term ((scons) sterm0 tRel) (ren_term ((scons) (0) ((funcomp) (shift) sigmaterm)) sterm)) (hexp)
  end
  |  subst_term ((scons) ?sterm0 ((funcomp) tRel ?sigmaterm)) ?sterm  =>  match   hexp  with
  |  subst_term ((scons) ?tterm0 tRel) ?tterm  =>  unify   (subst_term ((scons) sterm0 tRel) (ren_term ((scons) (0) ((funcomp) (shift) sigmaterm)) sterm)) (hexp)
  end
  |  subst_term ((scons) ?sterm1 ((scons) ?sterm0 ((funcomp) tRel ?sigmaterm))) ?sterm  =>  match   hexp  with
  |  subst_term ((scons) ?tterm1 ((scons) ?tterm0 tRel)) ?tterm  =>  unify   (subst_term ((scons) sterm1 ((scons) sterm0 tRel)) (ren_term ((scons) (0) ((scons) ((shift) (0)) ((funcomp) ((funcomp) (shift) (shift)) sigmaterm))) sterm)) (hexp)
  end
  |  subst_term ((scons) ?sterm0 ?sigmaterm) ?sterm  =>  match   hexp  with
  |  subst_term ((scons) ?tterm0 tRel) ?tterm  =>  unify   (subst_term ((scons) sterm0 tRel) (subst_term ((scons) (tRel (0)) ((funcomp) (ren_term (shift)) sigmaterm)) sterm)) (hexp)
  end
  |  subst_term ((scons) ?sterm0 ?sigmaterm) ?sterm  =>  match   hexp  with
  |  subst_term ((scons) ?tterm0 tRel) ?tterm  =>  unify   (subst_term ((scons) sterm0 tRel) (subst_term ((scons) (tRel (0)) ((funcomp) (ren_term (shift)) sigmaterm)) sterm)) (hexp)
  end
  |  subst_term ((scons) ?sterm0 ?sigmaterm) ?sterm  =>  match   hexp  with
  |  subst_term ((scons) ?tterm0 tRel) ?tterm  =>  unify   (subst_term ((scons) sterm0 tRel) (subst_term ((scons) (tRel (0)) ((funcomp) (ren_term (shift)) sigmaterm)) sterm)) (hexp)
  end
  |  subst_term ((scons) ?sterm0 ?sigmaterm) ?sterm  =>  match   hexp  with
  |  subst_term ((scons) ?tterm0 tRel) ?tterm  =>  unify   (subst_term ((scons) sterm0 tRel) (subst_term ((scons) (tRel (0)) ((funcomp) (ren_term (shift)) sigmaterm)) sterm)) (hexp)
  end
  |  subst_term ((scons) ?sterm0 ?sigmaterm) ?sterm  =>  match   hexp  with
  |  subst_term ((scons) ?tterm0 tRel) ?tterm  =>  unify   (subst_term ((scons) sterm0 tRel) (subst_term ((scons) (tRel (0)) ((funcomp) (ren_term (shift)) sigmaterm)) sterm)) (hexp)
  end
  |  subst_term ((scons) ?sterm0 ?sigmaterm) ?sterm  =>  match   hexp  with
  |  subst_term ((scons) ?tterm0 tRel) ?tterm  =>  unify   (subst_term ((scons) sterm0 tRel) (subst_term ((scons) (tRel (0)) ((funcomp) (ren_term (shift)) sigmaterm)) sterm)) (hexp)
  end
  |  subst_term ((scons) ?sterm1 ((scons) ?sterm0 ?sigmaterm)) ?sterm  =>  match   hexp  with
  |  subst_term ((scons) ?tterm1 ((scons) ?tterm0 tRel)) ?tterm  =>  unify   (subst_term ((scons) sterm1 ((scons) sterm0 tRel)) (subst_term ((scons) (tRel (0)) ((scons) (tRel ((shift) (0))) ((funcomp) (ren_term ((funcomp) (shift) (shift))) sigmaterm))) sterm)) (hexp)
  end
  |  (funcomp) (subst_term ((funcomp) tRel ?sigma0)) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_term ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (subst_term ((funcomp) tRel sigma0)) sigma = (funcomp) (ren_term sigma0) sigma) as eq by (renamify; reflexivity); rewrite   (eq); unify   ((funcomp) (ren_term sigma0) sigma) (hexp); clear eq
  end
  |  subst_term ((funcomp) tRel ?sigma0) ?s  =>  match   hexp  with
  |  ren_term ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (subst_term ((funcomp) tRel sigma0) s = ren_term sigma0 s) as eq by (renamify; reflexivity); rewrite   (eq); unify   (ren_term sigma0 s) (hexp); clear eq
  end
  |  (funcomp) (ren_term ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_term ?tau0) ?tau  =>  let eq := fresh "eq" in
  assert ((funcomp) (ren_term sigma0) sigma = (funcomp) (subst_term ((funcomp) tRel sigma0)) sigma) as eq by (substify; reflexivity); rewrite   (eq); unify   ((funcomp) (subst_term ((funcomp) tRel sigma0)) sigma) (hexp); clear eq
  end
  |  ren_term ?sigma0 ?s  =>  match   hexp  with
  |  subst_term ?tau0 ?t  =>  let eq := fresh "eq" in
  assert (ren_term sigma0 s = subst_term ((funcomp) tRel sigma0) s) as eq by (substify; reflexivity); rewrite   (eq); unify   (subst_term ((funcomp) tRel sigma0) s) (hexp); clear eq
  end
  |  tProd (subst_term ?sigma0 ?s0) (subst_term ((scons) (tRel (0)) ((funcomp) (ren_term (shift)) ?sigma0)) ?s1)  =>  unify   (subst_term sigma0 (tProd s0 s1)) (hexp)
  |  tLambda (subst_term ?sigma0 ?s0) (subst_term ((scons) (tRel (0)) ((funcomp) (ren_term (shift)) ?sigma0)) ?s1)  =>  unify   (subst_term sigma0 (tLambda s0 s1)) (hexp)
  |  tApp (subst_term ?sigma0 ?s0) (subst_term ?sigma0 ?s1)  =>  unify   (subst_term sigma0 (tApp s0 s1)) (hexp)
  |  tSucc (subst_term ?sigma0 ?s0)  =>  unify   (subst_term sigma0 (tSucc s0)) (hexp)
  |  tNatElim (subst_term ((scons) (tRel (0)) ((funcomp) (ren_term (shift)) ?sigma0)) ?s0) (subst_term ?sigma0 ?s1) (subst_term ?sigma0 ?s2) (subst_term ?sigma0 ?s3)  =>  unify   (subst_term sigma0 (tNatElim s0 s1 s2 s3)) (hexp)
  |  tEmptyElim (subst_term ((scons) (tRel (0)) ((funcomp) (ren_term (shift)) ?sigma0)) ?s0) (subst_term ?sigma0 ?s1)  =>  unify   (subst_term sigma0 (tEmptyElim s0 s1)) (hexp)
  |  tSig (subst_term ?sigma0 ?s0) (subst_term ((scons) (tRel (0)) ((funcomp) (ren_term (shift)) ?sigma0)) ?s1)  =>  unify   (subst_term sigma0 (tSig s0 s1)) (hexp)
  |  tPair (subst_term ?sigma0 ?s0) (subst_term ((scons) (tRel (0)) ((funcomp) (ren_term (shift)) ?sigma0)) ?s1) (subst_term ?sigma0 ?s2) (subst_term ?sigma0 ?s3)  =>  unify   (subst_term sigma0 (tPair s0 s1 s2 s3)) (hexp)
  |  tFst (subst_term ?sigma0 ?s0)  =>  unify   (subst_term sigma0 (tFst s0)) (hexp)
  |  tSnd (subst_term ?sigma0 ?s0)  =>  unify   (subst_term sigma0 (tSnd s0)) (hexp)
  |  tId (subst_term ?sigma0 ?s0) (subst_term ?sigma0 ?s1) (subst_term ?sigma0 ?s2)  =>  unify   (subst_term sigma0 (tId s0 s1 s2)) (hexp)
  |  tRefl (subst_term ?sigma0 ?s0) (subst_term ?sigma0 ?s1)  =>  unify   (subst_term sigma0 (tRefl s0 s1)) (hexp)
  |  tIdElim (subst_term ?sigma0 ?s0) (subst_term ?sigma0 ?s1) (subst_term ((scons) (tRel (0)) ((scons) (tRel ((shift) (0))) ((funcomp) (ren_term ((funcomp) (shift) (shift))) ?sigma0))) ?s2) (subst_term ?sigma0 ?s3) (subst_term ?sigma0 ?s4) (subst_term ?sigma0 ?s5)  =>  unify   (subst_term sigma0 (tIdElim s0 s1 s2 s3 s4 s5)) (hexp)
  |  tProd (ren_term ?sigma0 ?s0) (ren_term ((scons) (0) ((funcomp) (shift) ?sigma0)) ?s1)  =>  unify   (ren_term sigma0 (tProd s0 s1)) (hexp)
  |  tLambda (ren_term ?sigma0 ?s0) (ren_term ((scons) (0) ((funcomp) (shift) ?sigma0)) ?s1)  =>  unify   (ren_term sigma0 (tLambda s0 s1)) (hexp)
  |  tApp (ren_term ?sigma0 ?s0) (ren_term ?sigma0 ?s1)  =>  unify   (ren_term sigma0 (tApp s0 s1)) (hexp)
  |  tSucc (ren_term ?sigma0 ?s0)  =>  unify   (ren_term sigma0 (tSucc s0)) (hexp)
  |  tNatElim (ren_term ((scons) (0) ((funcomp) (shift) ?sigma0)) ?s0) (ren_term ?sigma0 ?s1) (ren_term ?sigma0 ?s2) (ren_term ?sigma0 ?s3)  =>  unify   (ren_term sigma0 (tNatElim s0 s1 s2 s3)) (hexp)
  |  tEmptyElim (ren_term ((scons) (0) ((funcomp) (shift) ?sigma0)) ?s0) (ren_term ?sigma0 ?s1)  =>  unify   (ren_term sigma0 (tEmptyElim s0 s1)) (hexp)
  |  tSig (ren_term ?sigma0 ?s0) (ren_term ((scons) (0) ((funcomp) (shift) ?sigma0)) ?s1)  =>  unify   (ren_term sigma0 (tSig s0 s1)) (hexp)
  |  tPair (ren_term ?sigma0 ?s0) (ren_term ((scons) (0) ((funcomp) (shift) ?sigma0)) ?s1) (ren_term ?sigma0 ?s2) (ren_term ?sigma0 ?s3)  =>  unify   (ren_term sigma0 (tPair s0 s1 s2 s3)) (hexp)
  |  tFst (ren_term ?sigma0 ?s0)  =>  unify   (ren_term sigma0 (tFst s0)) (hexp)
  |  tSnd (ren_term ?sigma0 ?s0)  =>  unify   (ren_term sigma0 (tSnd s0)) (hexp)
  |  tId (ren_term ?sigma0 ?s0) (ren_term ?sigma0 ?s1) (ren_term ?sigma0 ?s2)  =>  unify   (ren_term sigma0 (tId s0 s1 s2)) (hexp)
  |  tRefl (ren_term ?sigma0 ?s0) (ren_term ?sigma0 ?s1)  =>  unify   (ren_term sigma0 (tRefl s0 s1)) (hexp)
  |  tIdElim (ren_term ?sigma0 ?s0) (ren_term ?sigma0 ?s1) (ren_term ((scons) (0) ((scons) ((shift) (0)) ((funcomp) ((funcomp) (shift) (shift)) ?sigma0))) ?s2) (ren_term ?sigma0 ?s3) (ren_term ?sigma0 ?s4) (ren_term ?sigma0 ?s5)  =>  unify   (ren_term sigma0 (tIdElim s0 s1 s2 s3 s4 s5)) (hexp)
  |  ren_term ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  ren_term ?theta0 ?t  =>  unify   (ren_term tau0 (ren_term sigma0 s)) (hexp)
  end
  |  subst_term ((funcomp) ?tau0 ?sigma0) ?s  =>  match   hexp  with
  |  subst_term ?theta0 ?t  =>  unify   (subst_term tau0 (ren_term sigma0 s)) (hexp)
  end
  |  subst_term ((funcomp) (ren_term ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  ren_term ?theta0 ?t  =>  unify   (ren_term tau0 (subst_term sigma0 s)) (hexp)
  end
  |  subst_term ((funcomp) (subst_term ?tau0) ?sigma0) ?s  =>  match   hexp  with
  |  subst_term ?theta0 ?t  =>  unify   (subst_term tau0 (subst_term sigma0 s)) (hexp)
  end
  |  tSort ?s0  =>  match   hexp  with
  |  tSort ?t0  =>  heuristics   (s0) (t0)
  end
  |  tProd ?s0 ?s1  =>  match   hexp  with
  |  tProd ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  tLambda ?s0 ?s1  =>  match   hexp  with
  |  tLambda ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  tApp ?s0 ?s1  =>  match   hexp  with
  |  tApp ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  tSucc ?s0  =>  match   hexp  with
  |  tSucc ?t0  =>  heuristics   (s0) (t0)
  end
  |  tNatElim ?s0 ?s1 ?s2 ?s3  =>  match   hexp  with
  |  tNatElim ?t0 ?t1 ?t2 ?t3  =>  heuristics   (s0) (t0); heuristics   (s1) (t1); heuristics   (s2) (t2); heuristics   (s3) (t3)
  end
  |  tEmptyElim ?s0 ?s1  =>  match   hexp  with
  |  tEmptyElim ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  tSig ?s0 ?s1  =>  match   hexp  with
  |  tSig ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  tPair ?s0 ?s1 ?s2 ?s3  =>  match   hexp  with
  |  tPair ?t0 ?t1 ?t2 ?t3  =>  heuristics   (s0) (t0); heuristics   (s1) (t1); heuristics   (s2) (t2); heuristics   (s3) (t3)
  end
  |  tFst ?s0  =>  match   hexp  with
  |  tFst ?t0  =>  heuristics   (s0) (t0)
  end
  |  tSnd ?s0  =>  match   hexp  with
  |  tSnd ?t0  =>  heuristics   (s0) (t0)
  end
  |  tId ?s0 ?s1 ?s2  =>  match   hexp  with
  |  tId ?t0 ?t1 ?t2  =>  heuristics   (s0) (t0); heuristics   (s1) (t1); heuristics   (s2) (t2)
  end
  |  tRefl ?s0 ?s1  =>  match   hexp  with
  |  tRefl ?t0 ?t1  =>  heuristics   (s0) (t0); heuristics   (s1) (t1)
  end
  |  tIdElim ?s0 ?s1 ?s2 ?s3 ?s4 ?s5  =>  match   hexp  with
  |  tIdElim ?t0 ?t1 ?t2 ?t3 ?t4 ?t5  =>  heuristics   (s0) (t0); heuristics   (s1) (t1); heuristics   (s2) (t2); heuristics   (s3) (t3); heuristics   (s4) (t4); heuristics   (s5) (t5)
  end
  |  subst_term ?sigma0 ?s  =>  match   hexp  with
  |  subst_term ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  ren_term ?sigma0 ?s  =>  match   hexp  with
  |  ren_term ?tau0 ?t  =>  heuristics   (s) (t); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (subst_term ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (subst_term ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  |  (funcomp) (ren_term ?sigma0) ?sigma  =>  match   hexp  with
  |  (funcomp) (ren_term ?tau0) ?tau  =>  heuristics   (sigma) (tau); heuristics   (sigma0) (tau0)
  end
  |  ?s  =>  match   hexp  with
  |  subst_term ?sigma0 ?t  =>  unify   (subst_term tRel s) (hexp)
  |  ren_term ?sigma0 ?t  =>  unify   (ren_term (id) s) (hexp)
  end
  end.
