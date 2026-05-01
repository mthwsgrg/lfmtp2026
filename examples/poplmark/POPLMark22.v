Require Export Coq.Lists.List.
Require Import Coq.Program.Equality.
From poplmark Require Export sysf_pat.
Require Import Coq.Program.Tactics.
Require Import Coq.ZArith.Zcompare.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.




(** Some Notation definitions *)

Notation "s ⟨ xi1 ⟩" := (ren1  xi1 s) (at level 7, left associativity, format "s  ⟨ xi1 ⟩") : subst_scope.
Notation "s ⟨ xi1 ; xi2 ⟩" := (ren2 xi1 xi2 s) (at level 7, left associativity, format "s  ⟨ xi1 ; xi2 ⟩") : subst_scope.
Notation "⟨ xi ⟩" := (ren1 xi) (at level 1, left associativity, format "⟨ xi ⟩") : fscope.
Notation "⟨ xi1 ; xi2 ⟩" := (ren2 xi1 xi2) (at level 1, left associativity, format "⟨ xi1 ; xi2 ⟩") : fscope.
Notation "s [ sigma ]" := (subst1 sigma s) (at level 7, left associativity, format "s '/' [ sigma ]") : subst_scope.
Notation "[ sigma ]" := (subst1 sigma) (at level 1, left associativity, format "[ sigma ]") : fscope.
Notation "s [ sigma ; tau ]" := (subst2 sigma tau s) (at level 7, left associativity, format "s '/' [ sigma ; '/'  tau ]") : subst_scope.
Notation "[ sigma ; tau ]" := (subst2 sigma tau) (at level 1, left associativity, format "[ sigma ; tau ]") : fscope.



Definition ctx (q:nat) := fin q -> ty q.
Definition dctx (p q: nat) :=  fin p -> ty q.
Definition empty {X} : fin 0 -> X :=  fun x => match x with end.

Inductive unique {X} : list (nat * X) -> Prop :=
| unil : unique nil
| ucons l x xs : unique xs -> (forall x, ~ In (l, x) xs) ->  unique (cons (l,x) xs).

#[export] Hint Constructors unique.

Lemma unique_map {X Y: Type} {f : X -> Y} (xs : list (nat * X)) :
  unique xs -> unique (map (prod_map (fun x => x) f) xs).
Proof.
  intros.
  induction H; cbn; eauto.
  constructor; eauto.
  intros z A. rewrite in_map_iff in A. destruct A as ((?&?)&?&?).
  inv H1. eapply H0; eauto.
Qed.

Lemma unique_spec {X} (xs : list (nat * X)) :
  unique xs -> (forall l x y, In (l, x) xs -> In (l, y) xs -> x = y).
Proof.
  induction 1; intros; cbn in *.
  - contradiction.
  - destruct H1 as [|]; destruct H2 as [|]; try inversion H1; try inversion H2; subst; eauto; firstorder.
Qed.

Lemma in_map {X Y: Type} {f : X -> Y} (xs : list (nat * X)) l x:
  In (l, x) xs -> In (l, f x) (map (prod_map (fun x => x) f) xs).
Proof.
  unfold prod_map.
  induction xs;  cbn; eauto.
  - destruct a; eauto. intros [|]; eauto. inversion H; eauto.
Qed.

Definition label_equiv {X Y} (xs : list (nat * X)) (ys : list (nat * Y)) :=
   (forall i, (exists s, In (i, s) xs) <-> (exists A, In (i, A) ys)).

Lemma label_equiv_map {X X' Y Y': Type} {f : X -> X'} {g : Y -> Y'} (xs : list (nat * X)) (ys : list (nat * Y)) :
  label_equiv xs ys -> label_equiv (map (prod_map (fun x => x) f) xs) (map (prod_map (fun x => x) g) ys).
Proof.
  intros H. intros l.
  unfold prod_map. split; intros (?&?).
  - rewrite in_map_iff in H0. destruct H0 as ((?&?)&?&?). inv H0.
  unfold label_equiv in H. specialize (H l). assert (exists x0, In (l, x0) xs) by eauto.
  apply H in H0. destruct H0 as (?&?). exists (g x). rewrite in_map_iff. exists (l, x). eauto.
- rewrite in_map_iff in H0. destruct H0 as ((?&?)&?&?). inv H0.
  unfold label_equiv in H. specialize (H l). assert (exists x0, In (l, x0) ys) by eauto.
  apply H in H0. destruct H0 as (?&?). exists (f x). rewrite in_map_iff. exists (l, x). eauto.
Qed.

#[export] Hint Resolve unique_map label_equiv_map.

Definition update {X} (ts : list (nat * X)) l x : list (nat * X) :=
  map (fun p => if (Nat.eqb (fst p) l) then (l, x) else p) ts.

Lemma unique_update {X} (xs :list (nat * X)) l x :
  unique xs -> unique (update xs l x).
Proof.
  unfold update. intros H.
  induction xs; eauto. inv H. specialize (IHxs H2). cbn.
  destruct (Nat.eqb l0 l) eqn: H; cbn; eauto.
  - constructor; eauto. intros. apply PeanoNat.Nat.eqb_eq in H. subst. intros HH. apply in_map_iff in HH. destruct HH as (?&?&?). destruct x2. cbn in *.  destruct (Nat.eqb n l) eqn: HHH; eauto.
    apply PeanoNat.Nat.eqb_eq in HHH. subst. inv H. eapply H3. eauto. inv H. eapply H3. eauto.
  - constructor; eauto. intros z HH. apply in_map_iff in HH. destruct HH as ((?&?)&?&?). cbn in *.
    destruct (Nat.eqb n l) eqn:HHH; inversion H0; eauto. subst. apply PeanoNat.Nat.eqb_eq in HHH. subst. eapply H3. eauto. subst. eapply H3; eauto.
Qed.

Lemma natequiv_update {X Y} (xs :list (nat * X)) l x (ys: list (nat * Y)):
  label_equiv xs ys -> label_equiv (update xs l x) ys.
Proof.
  enough (label_equiv xs (update xs l x)).
  - intros A i. unfold label_equiv in H, A. now rewrite <- A, H.
  - clear ys. unfold label_equiv. induction xs; cbn; eauto.
    + intros _. split; eauto.
    + destruct a. intros i. cbn. split.
      * intros (?&?). destruct H; eauto.
        -- inv H. destruct (Nat.eqb i l) eqn:HH; eauto. apply PeanoNat.Nat.eqb_eq in HH. subst. eauto. -- assert (exists s, In (i, s) xs) by eauto. apply IHxs in H0. destruct H0 as (?&?). eauto.
      * intros (?&?). destruct H.
        -- destruct (Nat.eqb n l) eqn:HH; eauto. apply PeanoNat.Nat.eqb_eq in HH. subst. inv H. eauto.
        -- assert (exists A, In (i, A) (update xs l x)) by eauto. apply IHxs in H0.
           destruct H0. eauto.
Qed.

Lemma update_char {X} (xs : list (nat * X)) l x i s:
  In (i, s) (update xs l x) -> In (i, s) xs \/ (l = i /\ s = x).
Proof.
  induction xs; eauto. destruct a. cbn.
  destruct (Nat.eqb n l); intros [|]; try inversion H; eauto.
  all: destruct (IHxs H); eauto.
Qed.

Lemma list_dec {X} (P Q : X -> Prop) xs (IH : forall x, In x xs -> P x \/ Q x) :
  (forall x, In x xs -> P x) \/ (exists x, In x xs /\ Q x).
Proof.
  induction xs; cbn; eauto.
  - left. cbn. intros _ [].
  - cbn in IH. assert (forall x, In x xs -> P x \/ Q x) by firstorder.
    destruct (IHxs H) as [|(x&?&?)].
    + assert (P a \/ Q a) as[|] by eauto; cbn; eauto. left. intros z [->|]; cbn; eauto.
    + right. cbn. eauto.
Qed.

#[export] Hint Resolve unique_update natequiv_update.

(** POPLMark 1B. *)
Reserved Notation "'SUB' Delta |- A <: B" (at level 68, A at level 99, no associativity).
Inductive sub {q:nat} (Delta : ctx q) : ty q -> ty q -> Prop :=
| SA_top A :
    SUB Delta |- A <: top
| SA_Refl x :
    SUB Delta |- var_ty x <: var_ty x
| SA_Trans x  B :
     SUB Delta |- (Delta x) <: B ->  SUB Delta |- var_ty x <: B
| SA_arrow A1 A2 B1 B2 :
    SUB Delta |- B1 <: A1 -> SUB Delta |- A2 <: B2 ->
    SUB Delta |- arr A1 A2 <: arr B1 B2
| SA_all (A1: ty q) (A2: ty (S q)) B1 B2 :
    SUB Delta |- B1 <: A1 -> @sub (S q) ((B1 .:  Delta) >> (ren1 shift) ) A2 B2 ->
    SUB Delta |- all A1 A2 <: all B1 B2
| SA_rec (xs ys : list (nat * ty q)) : (forall l T', In (l, T') ys -> exists T, In (l, T) xs /\ SUB Delta |- T <: T') ->
                       unique xs -> unique ys -> SUB Delta |- recty xs <: recty ys
where "'SUB' Delta |- A <: B" := (sub Delta A B).

#[export] Hint Constructors sub.

Lemma sub_rec :  forall P : forall q : nat, ctx q -> ty q -> ty q -> Prop,
       (forall (p : nat) (Delta : ctx p) (A : ty p), P p Delta A top) ->
       (forall (p : nat) (Delta : ctx p) (x :  fin p), P p Delta (var_ty x) (var_ty x)) ->
       (forall (p : nat) (Delta : ctx p) (x :  fin p) (B : ty p),
        SUB Delta |- Delta x <: B -> P p Delta (Delta x) B -> P p Delta (var_ty x) B) ->
       (forall (p : nat) (Delta : ctx p) (A1 A2 B1 B2 : ty p),
        SUB Delta |- B1 <: A1 ->
        P p Delta B1 A1 ->
        SUB Delta |- A2 <: B2 -> P p Delta A2 B2 -> P p Delta (arr A1 A2) (arr B1 B2)) ->
       (forall (p : nat) (Delta : ctx p) (A1 : ty p) (A2 : ty (S p)) (B1 : ty p) (B2 : ty (S p)),
        SUB Delta |- B1 <: A1 ->
        P p Delta B1 A1 ->
        SUB (B1 .: Delta) >> (ren1 shift) |- A2 <: B2 ->
        P (S p) ((B1 .: Delta) >> (ren1 shift) ) A2 B2 -> P p Delta (all A1 A2) (all B1 B2)) ->
       (forall (p : nat) (Delta : ctx p) (xs ys : list (nat * ty p)),
        (forall (i : nat) (T' : ty p),
         In (i, T') ys -> exists  (T : ty p), In (i, T) xs /\ SUB Delta |- T <: T' /\ P _ Delta T T') ->
        unique xs -> unique ys -> P p Delta (recty xs) (recty ys)) ->
       forall (p : nat) (Delta : ctx p) (t t0 : ty p), SUB Delta |- t <: t0 -> P p Delta t t0.
Proof. intros P. fix IH 11.
  intros. induction H5; try now (clear IH; eauto).
  eapply H4. intros. destruct (H5 _ _ H8) as (T&?&?).
  exists T. repeat split; eauto. all: eauto.
Qed.

Lemma ty_rec
     : forall P : forall qty : nat, ty qty -> Prop,
       (forall (qty : nat) (f : fin qty), P qty (var_ty f)) ->
       (forall qty : nat, P qty top) ->
       (forall (qty : nat) (t : ty qty), P qty t -> forall t0 : ty qty, P qty t0 -> P qty (arr t t0)) ->
       (forall (qty : nat) (t : ty qty),
        P qty t -> forall t0 : ty (S qty), P (S qty) t0 -> P qty (all t t0)) ->
       (forall (qty : nat) (l : list (nat * ty qty)), (forall i t, In (i,t) l -> P _ t) -> P qty (recty l)) ->
       forall (qty : nat) (t : ty qty), P qty t.
Proof.
  intros P. fix IH 7. intros.
  induction t; try now (clear IH; eauto).
  eapply H3. intros. induction l.
  - contradiction.
  - destruct H4 as [|].
    + destruct a. specialize (IH H H0 H1 H2 H3 _ t0). intros. inv H4. apply IH.
    + now apply IHl.
Qed.


(** We assume that the subtyping relation is reflexive.
A proof requires a well-formedness condition.*)

Section Pattern.
  
Variable sub_refl : forall  q (Delta : ctx q) A, SUB Delta |- A <: A.


Lemma sub_weak {p q: nat} (Delta1: ctx p) (Delta2: ctx q) A1 A2  (xi:  fin p ->  fin q) :
  SUB Delta1 |- A1 <: A2 ->
 (forall x,  ren1 xi (Delta1 x) = Delta2 (xi x)) ->
 SUB Delta2 |- A1⟨xi⟩ <: A2⟨xi⟩ .

  intros H. autorevert H. induction H using @sub_rec; intros; subst; asimpl; cbn; econstructor; eauto.
  - rewrite <- H0.
    eapply IHsub; eauto.
  - eapply IHsub2; try reflexivity.
    destruct x; asimpl.
    + rewrite <- H1. asimpl. reflexivity.        
    + now asimpl.
  - intros l T' HH. rewrite in_map_iff in HH. destruct HH as ([]&HH&?).
    inv HH. destruct (H _ _ H3) as (?&?&?&?).
    exists (ren1 xi x). split; eauto. apply in_map; eauto.
Qed.


Definition transitivity_at {q:nat} (B: ty q) := forall p Gamma (A : ty p) C  (xi:  fin q ->  fin p),
  SUB Gamma |- A <: ren1 xi B -> SUB Gamma |- ren1 xi B <: C ->  SUB Gamma |- A <: C.

Lemma transitivity_proj {p:nat} (Gamma: ctx p) A B C :
  transitivity_at B ->
  SUB Gamma |- A <: B -> SUB Gamma |- B <: C -> SUB Gamma |- A <: C.
Proof. intros H. specialize (H p Gamma A C id).  now asimpl in H. Qed.

Hint Resolve transitivity_proj.

Lemma transitivity_ren {p q:nat} B (xi:  fin p ->  fin q) : transitivity_at B -> transitivity_at (ren1 xi B).
Proof. unfold transitivity_at. intros. eapply H; asimpl in H0; asimpl in H1; eauto. Qed.

Lemma sub_narrow {p:nat} (Delta Delta': ctx p) A C :
  (forall x, SUB Delta' |- Delta' x <: Delta x) ->
  (forall x, Delta x = Delta' x \/ transitivity_at (Delta x)) ->
  SUB Delta |- A <: C -> SUB Delta' |- A <: C.
Proof with asimpl;eauto.
  intros H H' HH. autorevert HH. induction HH using sub_rec; intros; eauto.
  - destruct (H' x); eauto. rewrite H0 in *. eauto.
  - constructor; eauto.
    eapply IHHH2.
    + destruct x; asimpl; cbn; eauto; try apply sub_refl.
      eapply sub_weak; try reflexivity. eapply H.
       
    + destruct x; asimpl; cbn; eauto.
      destruct (H' f);  eauto using transitivity_ren.
      rewrite H0. now left.
  - econstructor; eauto. intros l T' HH.
    destruct (H _ _ HH) as (T&?&?&?). exists  T.
    split; eauto.
Qed.

Corollary sub_trans' {p:nat} (B : ty p): transitivity_at B.
Proof with asimpl;eauto.
  unfold transitivity_at.
  autorevert B. induction B using ty_rec; intros...
  - depind H...
  - depind H... depind H0...
  - depind H... depind H1...
  - depind H... depind H1...
    econstructor... clear IHsub0 IHsub3 IHsub1 IHsub2.
    eapply IHB2; eauto.
    + asimpl in *. eapply sub_narrow; try eapply H0.
      * destruct x; asimpl; cbn; eauto.
        (** EXAMPLE 1 *)  as_apply sub_weak; eauto.
      * intro x; destruct x; eauto.
        ** try cbn.
           right. apply transitivity_ren. eauto.
    + asimpl in H1_0. auto.
  - depind H0... depind H3...
    econstructor; eauto. intros.
    destruct (H5 _ _ H6) as (T&?&?). rewrite in_map_iff in H7.
    destruct H7 as ((?&?)&?&?). inv H7.
    edestruct (H2 l0 (ren1 xi t) ) as (T&?&?).
    + apply in_map_iff. exists (l0, t). eauto.
    + eauto.
Qed.

Corollary sub_trans {p:nat} (Delta  : ctx p) A B C:
  SUB Delta |- A <: B -> SUB Delta |- B <: C -> SUB Delta |- A <: C.
Proof. eauto using sub_trans'. Qed.


Lemma sub_substitution {p q :nat} (sigma :  fin p -> ty q) Delta (Delta': ctx q) A B:
   (forall x ,  SUB Delta' |- sigma x <:   (Delta x)[sigma]  ) ->
   SUB Delta |- A <: B -> SUB Delta' |- A[sigma] <: subst_ty sigma B.
Proof.
    intros eq H. autorevert H. induction H using sub_rec; try now (econstructor; eauto).
  - intros. asimpl. eapply sub_refl.
  - intros. asimpl. eauto. cbn in *. eauto using sub_trans.
  - intros. asimpl. econstructor; eauto.
    asimpl. eapply IHsub2.
    intros [|];asimpl; cbn; eauto using sub_refl. asimpl.    
    (** EXAMPLE 2 *)   as_apply sub_weak; eauto.    
 - intros. asimpl. econstructor; eauto. intros. rewrite in_map_iff in H2. destruct H2 as ((?&?)&?&?).
    inv H2. destruct (H _ _ H3) as (T&?&?&?).
    exists (T[sigma]). split; eauto. apply in_map. eauto.

    
Qed.

(** POPLMARK CHALLENGE 2B *)

Parameter pat_ty : forall {m} (p: nat), pat m -> ty m ->  (fin p -> (ty m)) -> Prop.
Parameter pat_eval : forall {m n} p, pat m -> tm m n -> (fin p -> (tm m n)) -> Prop.
Parameter pat_ty_subst: forall {m n} (sigma: fin m -> ty n) p pt A Gamma, @pat_ty m p pt A Gamma -> @pat_ty n p (pt[sigma]) (A[sigma]) (Gamma >>  subst_ty sigma).

Inductive value  {q p}: tm q p -> Prop :=
| Value_abs A s : value(abs A s)
| Value_tabs A s : value(tabs A s)
| Value_rec xs : (forall i s, In (i, s) xs -> value s) -> value (rectm xs).


Reserved Notation "'TY' Delta ; Gamma |- A : B"
  (at level 68, A at level 99, no associativity,
   format "'TY'  Delta ; Gamma  |-  A  :  B").

Inductive has_ty {q p:nat} (Δ : ctx q) (Γ : dctx  p q) : tm q p -> ty q -> Prop :=
| T_Var  x :
  TY Δ;Γ |- var_tm x : Γ x
  | T_abs (A: ty q) B (s: tm q (S p)):
    @has_ty q (S p) Δ (A .: Γ) s B   ->
    TY Δ;Γ |- abs A s : arr A B
| T_app A B s t: TY Δ;Γ |- s : arr A B  -> TY Δ;Γ |- t : A -> TY Δ;Γ |- app s t : B
| T_tabs A B s : @has_ty (S q) p ((A .: Δ) >> (ren1 shift) ) (Γ >> (ren1 shift) ) s B -> TY Δ;Γ |- tabs A s : all A B
|  T_Tapp A B A' s : TY Δ;Γ |- s : all A B -> SUB Δ |- A' <: A ->  TY Δ;Γ |- tapp s A' : subst1 (A'..) B
| T_Rcd ts As : unique ts -> unique As -> label_equiv ts As
                -> (forall i A t, In (i, t) ts -> In (i, A) As -> TY Δ;Γ |- t : A) -> TY Δ;Γ |- rectm ts : recty As
| T_Proj ts j A As: TY Δ;Γ |- ts : recty As -> In (j, A) As -> TY Δ;Γ |- proj ts j : A
| letpat_ty n (P: pat q) (t : tm q p) (s: tm q (n + p)) A (B : ty q) (ABar: fin n -> (ty q)): has_ty Δ Γ t A -> pat_ty  n P A ABar -> @has_ty q (n + p) Δ (scons_p n ABar Γ) s B ->  has_ty Δ Γ (letpat  n P t s) B
| T_Sub A B s :
    TY Δ;Γ |- s : A  -> SUB Δ |- A <: B   ->
    TY Δ;Γ |- s : B
where "'TY' Delta ; Gamma |- s : A" := (has_ty Delta Gamma s A).

Lemma T_Var' {q p:nat} (Δ : ctx q) (Γ : dctx p q) x :
  forall A, A = Γ x -> TY Δ;Γ |- var_tm x : A.
Proof. intros A ->. now econstructor. Qed.

Reserved Notation "'EV' s => t"
  (at level 68, s at level 80, no associativity, format "'EV'  s  =>  t").

Inductive eval {q p:nat} : tm q p -> tm q p -> Prop :=
| E_appabs A s t : EV app (abs A s) t => subst2 ids (t..) s
| E_Tapptabs A s B : EV tapp (tabs A s) B => subst2 (B..) ids s
| E_RecProj  ts j s : In (j, s) ts -> EV (proj (rectm  ts) j) => s
| letpat_eval n (P : pat q) (t : tm q p) (s : tm q (n + p)) (tBar: fin n -> (tm q p)) :  pat_eval n P t tBar -> eval (letpat n P t s) (subst_tm (@var_ty q) (scons_p _ tBar (@var_tm _ _)) s)
| E_appFun s s' t :
     EV s => s' ->
     EV app s t => app s' t
| E_appArg s s' v:
     EV s => s' -> value v ->
     EV app v s => app v s'
| E_TyFun s s' A :
     EV s => s' ->
     EV tapp s A => tapp s' A
| E_Proj s s' j : EV s => s' -> EV (proj s j) => (proj s' j)
| E_Rec l ts t t' : EV t => t' -> In (l,t) ts -> EV (rectm ts) => rectm (update ts l t')  | E_LetL n P t t' s : EV t => t' -> EV (letpat n P t s) => (letpat n P t'  s)
where "'EV' s => t" := (eval s t).

(** Assumptions of progress and typing on patterns. *)
Parameter pat_progress : forall p pt s A Gamma, TY empty; empty |- s : A -> @pat_ty _ p pt A Gamma -> exists sigma, @pat_eval _ _ p pt s sigma.

(** PROGRESS *)

Lemma can_form_arr {s: tm 0 0} {A B}:
  TY empty;empty |- s : arr A B -> value s -> exists C t, s = abs C t.
Proof.
  intros H.
  depind H; intros; eauto.
  all: try now (try destruct x0;  try inversion H1).
 + inversion H0; subst; eauto. inversion x.
Qed.

Lemma can_form_all {s A B}:
  TY empty;empty |- s : all A B -> value s -> exists C t, s = tabs C t.
Proof.
  intros H.
  depind H; intros; eauto.
  all: try now (try destruct x0; try inversion H1).
  + inv H0; subst.  inversion x.  eauto.
Qed.

Lemma can_form_rectm {s A}:
  TY empty;empty |- s : recty A -> value s -> exists xs, s = rectm xs /\ forall l A', In (l, A') A -> exists s', In (l, s') xs.
Proof.
  intros H.
  depind H; intros; eauto.
   all: try now (try destruct x0; try inversion H1).
  + eexists. split; eauto.
    intros. apply H1; eauto.
  +  inv H0; subst; eauto.
     * inversion x.
     * edestruct IHhas_ty as (?&?&?); eauto.
       subst. exists x; split; eauto. intros.
       edestruct (H3 _ _ H0).
       eapply H2. apply H5.
Qed.

Lemma ty_inv_rec {q p:nat} {Δ Γ A As'} ts  :
  TY Δ;Γ |- rectm ts: A  ->  SUB Δ |- A <: recty As' ->
   (  (forall (i : nat) (s : tm q p) B',
          In (i, s) ts -> In (i, B') As' ->  exists (B : ty q),  TY Δ;Γ |- s : B /\ SUB Δ |- B <: B')).
Proof.
  intros H. depind H; intros.
  - inv H4. eauto.
    assert (exists A, In (i, A) As) as [A ?].
    + apply H1. eauto.
    + specialize (H2 _ _ _ H5 H4).
      destruct (H9 _ _ H6) as (?&?&?).
      assert (x = A) as -> by eauto using unique_spec.
      eauto.
  - eauto using sub_trans.
Qed.
  

Theorem ev_progress s A:
  TY empty;empty |- s : A -> value s \/ exists t,  EV s => t.
Proof.
  intros. depind H; eauto; try now (left; constructor).
   - inversion x.
   - right. edestruct IHhas_ty1 as [? | [? ?]]; try reflexivity; eauto.
    + edestruct (can_form_arr H H1) as [? [? ?]]; subst.
      eexists. econstructor.
    + eexists. econstructor. eauto.
  - right. edestruct IHhas_ty as [? | [? ?]]; try reflexivity; eauto.
    + edestruct (can_form_all H H1) as [? [? ?]]; subst. eexists. econstructor.
    + eexists. econstructor. eauto.
  - assert ((forall p, In p ts -> value (snd p)) \/ (exists p, In p ts /\ exists s', EV (snd p) => s')) as [|].
    { apply list_dec. intros (?&?) ?. cbn.
      assert (exists A, In (n, A) As) as (A&?). apply H1; eauto.
      eauto. }
    + left. constructor. intros. specialize (H4 (i, s)). eauto.
    + destruct H4 as ((l&s)&?&(s'&?)).
      right. exists (rectm (update ts l s')). econstructor; eauto.
  - right. edestruct IHhas_ty as [? | [? ?]]; eauto.
    + edestruct (can_form_rectm H H1) as [? [? ?]]; try reflexivity. subst.
      rename x into xs.
      enough (exists x, In (j, x) xs) as (?&?).
      * eexists. constructor. eauto.
      * inversion H; eauto.
    + eexists. constructor. eassumption.
  - edestruct (IHhas_ty1  t A0) as [|[? ?]]; eauto.
    + right. edestruct (pat_progress _ _ _ _ _ H H0). eexists. econstructor. eauto.
    + right. eexists. apply E_LetL; eauto.
Qed.


(** PRESERVATION *)


Lemma context_renaming_lemma {q q' p p' : nat} (Δ: ctx q') (Γ: dctx p' q') (s: tm q p) A (ξ :  fin q ->  fin q') (ζ:  fin p ->  fin p') Δ' (Γ' : dctx p q):
  (forall x,  ren1 ξ (Δ' x) = Δ (ξ x)) ->
  (forall (x:  fin p) , ren1 ξ (Γ' x) =  (Γ (ζ x))) ->
  TY Δ'; Γ' |- s : A -> TY Δ; Γ |- ren2 ξ ζ s : ren1 ξ A.
Proof.
  intros H H' ty. autorevert ty.
  depind ty; intros; asimpl in *; subst; try now (econstructor; eauto).
  - rewrite H'. constructor.
  - constructor. eapply IHty; eauto.
     destruct x; asimpl; cbn; eauto; asimpl.
  - cbn. econstructor. apply IHty; eauto.
    + destruct x; asimpl; cbn; eauto; try now asimpl. rewrite <- H. now asimpl.
    + intros. asimpl. rewrite <- H'. now asimpl.
  (** EXAMPLE 3 *) 
  - cbn. as_apply T_Tapp.
    2: asimpl; asimpl in IHty; eapply IHty; eauto.
    eapply sub_weak; eauto.
   - econstructor; eauto.
    + intros.
      eapply in_map_iff in H5. destruct H5 as ([]&?&?). inv H5.
      eapply in_map_iff in H6. destruct H6 as ([j A']&?&?). inv H5.
      eapply H3; eassumption.
  - cbn. econstructor; eauto. now apply in_map.
  - cbn. asimpl.
    apply letpat_ty  with (A := ren_ty ξ A)  (ABar := ABar >> (ren_ty ξ)); eauto.    
    (** EXAMPLE 4 *)
    + as_apply pat_ty_subst; eauto. 
    +  asimpl. eapply IHty2; eauto; asimpl.
       intros x.
       destruct (destruct_fin x) as [[x' ->] |[x' ->]]; asimpl; eauto.
       * unfold upRen_p. now asimpl.
       * unfold upRen_p. now asimpl.      
- econstructor. eauto. eapply sub_weak; eauto.
Qed.


Lemma context_morphism_lemma {q q' p p' :nat} (Δ: ctx q) (Δ': ctx q') (Γ: dctx p q) (s: tm q p) A (σ : fin q -> ty q') (τ:  fin p -> tm q' p') (Γ' : dctx p' q'):
  (forall x, SUB Δ' |- σ x <:  subst1 σ (Δ x)) ->
  (forall (x:  fin p) ,  TY Δ'; Γ' |- τ x : subst_ty σ (Γ x)) ->
  TY Δ; Γ |- s : A -> TY Δ'; Γ' |- subst2 σ τ s : subst1 σ A.
Proof.
   intros eq1 eq2 ty. autorevert ty.
   depind ty; intros; subst; asimpl; try now (econstructor; eauto; sub_refl).
   - constructor. eapply IHty; eauto.
     destruct x; asimpl; cbn; eauto; asimpl.
     (** EXAMPLE 5 *)
     + as_apply context_renaming_lemma; eauto; now asimpl.
     +  constructor.     
    - constructor. apply IHty; eauto.
      + destruct x; asimpl; cbn; eauto.        
        * (** EXAMPLE 6  *) 
          as_apply sub_weak; eauto.
      + intros x. asimpl.
        (** EXAMPLE 7 *)
        as_apply context_renaming_lemma;eauto.
      (** EXAMPLE 8 *)  
    - as_apply T_Tapp. eauto.
      2: asimpl in IHty; apply IHty; eauto.
      eapply sub_substitution; eauto.
  - econstructor; eauto.
    + intros.
      eapply in_map_iff in H5. destruct H5 as ([]&?&?). inv H5.
      eapply in_map_iff in H4. destruct H4 as ([j A']&?&?). inv H4.
      eapply H3; eauto.
  - econstructor; eauto. now apply in_map.
  - econstructor; eauto.
    eapply pat_ty_subst; eauto.
      apply IHty2.
      * eauto.
      * intros x.
        destruct (destruct_fin x) as [[x' ->] |[x' ->]]; asimpl; eauto.
        -- eapply T_Var'. now asimpl.           
            (** EXAMPLE 9 *)
        --  as_apply context_renaming_lemma; eauto; try apply eq2; try now asimpl.
          intros. now asimpl.     
   - econstructor.
    + eapply IHty; eauto.
    + eapply sub_substitution; eauto.
Qed.

Lemma ty_inv_abs {q p : nat} Δ Γ A A' B C (s: tm q (S p)):
  TY Δ;Γ |- abs A s : C   ->   SUB Δ |- C <: arr A' B   ->
  (SUB Δ |- A' <: A /\
    exists B', TY Δ; A .: Γ |- s : B' /\ SUB Δ |- B' <: B).
Proof.
  intros H. depind H; intros.
  - inv H0. split; eauto.
   - edestruct (IHhas_ty  _ _ _ _ (eq_refl _) (sub_trans _  _ _ _ H0 H1)) as (?&?&?&?).
     split.
     + assumption.
     + eauto.
Qed.

Lemma ty_subst {p q:nat} (Gamma: dctx p q) (Delta: ctx q) Delta' s A:
    (forall x, SUB Delta' |- Delta' x <: Delta x) ->
  TY Delta; Gamma |- s : A -> TY Delta'; Gamma |- s : A.
Proof.
  intros eq H. autorevert H. depind H; eauto; intros; try now (econstructor; eauto).
  - econstructor; eauto. asimpl. eapply IHhas_ty.
    destruct x; asimpl; cbn; eauto.
    + asimpl.
      eapply sub_weak; try reflexivity. apply eq.
  - econstructor; eauto.
    (** EXAMPLE 10  *)
    as_apply sub_substitution.
    3: apply H0.
    intros x. asimpl. econstructor. eauto.   
    (** EXAMPLE 11  *)
  - econstructor; eauto. as_apply sub_substitution. 3: apply H0.
    intros x. econstructor. asimpl. eapply eq.
Qed.

Lemma ty_inv_tabs {q p:nat} {Δ Γ A A' B C} (s : tm (S q) p):
  TY Δ;Γ |- tabs A s : C -> SUB Δ |- C <: all A' B   ->
  (SUB Δ |- A' <: A /\ exists B',
   TY (A'.:Δ) >> ren_ty ↑; Γ >> ren_ty ↑ |- s : B' /\ SUB (A' .: Δ) >> ren_ty ↑ |- B' <: B).
Proof.
  intros H. depind H; intros.
  - inv H0. split; eauto.
    eexists. split; eauto.
    eapply ty_subst; try eapply H.
    destruct x; asimpl; cbn; eauto.
    eapply sub_weak; try reflexivity; eauto.
  - eauto using sub_trans.
Qed.

Parameter pat_ty_eval : forall m n p pt s A (Gamma: fin n -> ty m) Gamma' Delta sigma, @pat_ty m p pt A Gamma' -> TY Delta; Gamma |- s : A -> @pat_eval m n p pt s sigma -> forall (x: fin p), TY Delta; Gamma |- sigma x : Gamma' x.

Theorem preservation (q p:nat) Δ Γ (s: tm q p) t A :
  TY Δ;Γ |- s : A -> EV s => t ->
  TY Δ;Γ |- t : A.
Proof.
  intros H_ty H_ev. autorevert H_ev.
  induction H_ev; intros; eauto using ty.
  all: try now (depind H_ty; [econstructor; eauto|eapply T_Sub; eauto]).
  - depind H_ty; [|eauto].
    + inv H_ty1; subst.
      (** EXAMPLE 12 *)
      * as_apply context_morphism_lemma; eauto.
         -- intros. asimpl. repeat constructor.  now apply sub_refl.
        -- intros [|].
           --- cbn; asimpl; eauto. econstructor; eauto.   
           --- asimpl. eauto.
      * pose proof (ty_inv_abs   _ _ _ _ _ _ _ H H0) as (?&?&?&?).
        eapply T_Sub; eauto.
        (** EXAMPLE 13 *)
        as_apply context_morphism_lemma; eauto.
        -- intros. asimpl. repeat constructor. apply sub_refl.
        -- intros [|].
           --- cbn; asimpl; eauto; econstructor; eauto.
           --- cbn; asimpl; eauto; econstructor; eauto.
     + asimpl. econstructor; eauto.
  - depind H_ty; eauto.
    + depind H_ty.
      * asimpl in H_ty.
        eapply context_morphism_lemma; try eapply H_ty; eauto.
        -- destruct x; asimpl; cbn; eauto; try now asimpl.
           --- asimpl; eauto using sub_refl.
       -- intros x. asimpl. constructor.
      * pose proof (ty_inv_tabs _ H_ty H) as (?&?&?&?).
        eapply T_Sub.  asimpl in *.
        eapply context_morphism_lemma; eauto.
        -- auto_case; asimpl; eauto.
        -- intros z. asimpl. constructor.
        -- eapply sub_substitution; eauto.
           auto_case; asimpl; eauto.
    + econstructor; eauto.
  -  depind H_ty; eauto.
    + depind H_ty.
      * eapply H2; eauto.
      * pose proof (ty_inv_rec _ H_ty H  _ _ _ H1 H0) as(?&?&?).
        subst. eapply T_Sub; eauto.
    + econstructor; eauto.
  - depind H_ty.
    (** EXAMPLE 14 *)
    + as_apply context_morphism_lemma; eauto.
    (** EXAMPLE 15 *)  
        * intros. as_apply SA_Trans. now apply sub_refl.
      * intros. destruct (destruct_fin x) as [[]|[]]; subst.
        -- asimpl. eapply pat_ty_eval; eauto.
        -- asimpl. constructor. 
    + eapply T_Sub; eauto.
  - depind H_ty; [|eapply T_Sub; eauto].
    econstructor; eauto.
    + intros.
      apply update_char in H5 as [|(->&->)]; eauto.
Qed.
End Pattern.
