Require Export Basics.


Definition Var := nat.

Lemma var_eqdec : forall (m n: Var), {m = n} + {m <> n}.
  decide equality.
Defined.

Unset Elimination Schemes.
Inductive exp := Zero
               | App (s t: exp) : exp
               | Lam (s: exp): exp
               | Inst (s: exp) (σ: sexp): exp
               | VarExp (X: Var) : exp
with sexp :=    I : sexp
                | Shift : sexp
                | Cons (s: exp) (σ: sexp) : sexp
                | Comp (σ τ: sexp) : sexp
                | VarSExp (Y: Var) : sexp.
Set Elimination Schemes.
Scheme exp_ind := Induction for exp Sort Type
with  sexp_ind := Induction for sexp Sort Type.
Combined Scheme sigma_ind from exp_ind, sexp_ind.

Notation "s [ σ ]" := (Inst s σ).
Notation "σ >> τ" := (Comp σ τ) (at level 56, right associativity).
Notation "s .: σ" := (Cons s σ) (at level 58).
Notation "↑" := Shift.

Scheme exp_ind2 := Induction for exp Sort Prop
with sexp_ind2 := Induction for sexp Sort Prop.
Combined Scheme sigma_ind2 from exp_ind2, sexp_ind2.

Scheme exp_ind3 := Induction for exp Sort Prop.
Scheme sexp_ind3 := Induction for sexp Sort Prop.


Fixpoint exp_size (s: exp) : nat :=
  match s with
  | App s t => 1 + exp_size s + exp_size t
  | Lam s => 1 + exp_size s
  | s[σ] => 1 + exp_size s + sexp_size σ
  | _ => 1
  end
with sexp_size (σ: sexp) : nat :=
  match σ with
  | s .: σ => 1 + exp_size s + sexp_size σ
  | σ >> τ => 1 + sexp_size σ + sexp_size τ
  | _ => 1
  end.



Lemma expression_eqdec : (forall s t : exp, {s = t} + {s <> t}) *
                           (forall σ τ : sexp, {σ = τ} + {σ <> τ}).
  apply sigma_ind; intros.
  - destruct t; (try (right; discriminate)).
    + left. reflexivity.
  - destruct t0; (try (right; discriminate)).
    + specialize (H t0_1). specialize (H0 t0_2).
      destruct H.
      * destruct H0.
        ** rewrite e. rewrite e0. left. reflexivity.
        ** rewrite e. right. unfold not in *. intros. inversion H; eauto.
      * destruct H0.
        **  rewrite e. right. unfold not in *. intros. inversion H; eauto.
        **  right. unfold not in *. intros. inversion H; eauto.
  - destruct t; (try (right; discriminate)).
    case (H t); intros.
    rewrite e. now left.
    unfold not in *. right; intros.  inversion H0; eauto.
  - destruct t; (try (right; discriminate)).
    case (H t); intros.
    case (H0 σ0); intros.
    rewrite e. rewrite e0. now left.
    unfold not in *. right. intros. inversion H1; eauto.
    unfold not in *. right. intros. inversion H1; eauto.
  - destruct t; (try (right; discriminate)).  
    case (var_eqdec X X0); intros; eauto.
    unfold not in *. right. intros. inversion H; eauto.
  - destruct τ; (try (right; discriminate)).
    now left.
  - destruct τ; (try (right; discriminate)).
    now left.
  - destruct τ; (try (right; discriminate)).
    case (H s0); intros.
    case (H0 τ); intros.
    rewrite e. rewrite e0. now left.
    rewrite e. unfold not in *. right; intros. inversion H1; eauto.
    unfold not in *.  right; intros. inversion H1; eauto.
  - destruct τ0; (try (right; discriminate)).
    case (H τ0_1); intros.
    case (H0 τ0_2); intros.
    rewrite e. rewrite e0. now left.
    unfold not in *. right; intros. inversion H1; eauto.
    unfold not in *. right; intros. inversion H1; eauto.
  - destruct τ; (try (right; discriminate)).
    case (var_eqdec Y Y0); intros; eauto.
    unfold not in *. right. intros. inversion H; eauto.
Qed.

Lemma exp_eqdec : forall s t: exp, {s=t} + {s <> t}.
  intros.
  pose proof expression_eqdec.
  destruct H.
  exact (s0 s t).
Defined.

Lemma sexp_eqdec : forall σ τ: sexp, {σ=τ} + {σ <> τ}.
  intros.
  pose proof expression_eqdec.
  destruct H.
  exact (s0 σ τ).
Defined.

Inductive SortedVar : Type :=
| exp_var : Var -> SortedVar
| sexp_var : Var -> SortedVar.

Inductive SortedExp : Type :=
| Exp : exp -> SortedExp
| SExp : sexp -> SortedExp.

Lemma sortedvar_eqdec : forall (v1 v2: SortedVar), {v1=v2} + {v1<>v2}.
  decide equality.
  - apply var_eqdec.
  - apply var_eqdec.
Qed.


Fixpoint vars_of_exp (s : exp) {struct s} : set SortedVar := 
match s with
 | Zero     => empty_set _
 | App s t  => set_union sortedvar_eqdec (vars_of_exp s) (vars_of_exp t)
 | Lam s => vars_of_exp s                      
 | Inst s σ => set_union sortedvar_eqdec (vars_of_exp s) (vars_of_sexp σ)
 | VarExp X => set_add sortedvar_eqdec (exp_var X) (empty_set _)
end
with vars_of_sexp (σ: sexp) {struct σ} : set SortedVar :=
 match σ with
 | I  => empty_set _
 | Shift => empty_set _
 | Comp σ τ => set_union sortedvar_eqdec (vars_of_sexp σ) (vars_of_sexp τ)
 | Cons s σ => set_union sortedvar_eqdec (vars_of_exp s) (vars_of_sexp σ)
 | VarSExp X => set_add sortedvar_eqdec (sexp_var X) (empty_set _)
end.



Lemma NoDup_exps_vars : (forall t, NoDup (vars_of_exp t)) /\ (forall σ, NoDup (vars_of_sexp σ)).
Proof.
  apply sigma_ind2; intros; simpl; trivial; try now apply NoDup_nil.
  - apply set_union_nodup; trivial.
  - apply set_union_nodup; trivial.
  - apply NoDup_cons. intro. trivial. apply NoDup_nil.
  - apply set_union_nodup; trivial.
  - apply set_union_nodup; trivial.
  - apply NoDup_cons. intro. trivial. apply NoDup_nil.
Qed.


Lemma exps_size_gt_0 : (forall s, exp_size s > 0) /\ (forall σ, sexp_size σ> 0).
Proof.
  apply sigma_ind2; intros; simpl; trivial; try lia.
Qed.
  
Lemma exp_size_σmin_lam : forall s σ, exp_size (Lam s[Zero .: σ >> ↑]) > exp_size (Lam s)[σ].
Proof.
  intros. simpl. lia.
Qed.

Lemma exp_size_σmin_app : forall s t σ,  exp_size (App s[σ] t[σ]) > exp_size ( (App s t)[σ]).
Proof.
  intros. simpl. lia.
Qed.

Lemma exp_size_σmin_monad : forall s σ τ, exp_size (s[σ >> τ]) >= exp_size (s[σ][τ]).
Proof.
  intros. simpl. lia.
Qed.

Lemma sexp_size_σmin_comp : forall σ τ ρ, sexp_size (σ >> τ >> ρ) >= sexp_size ((σ>> τ) >> ρ).
Proof.
  intros. simpl. lia.
Qed.

Lemma sexp_size_σmin_cons : forall s σ τ, sexp_size (s[τ] .: σ >> τ) >= sexp_size ( (s .: σ) >> τ).
Proof.
  intros. simpl. lia.
Qed.

                                                 
Lemma s_noteq_app : forall s t, s = App s t -> False.
  intro s.
  induction s using exp_ind3; intros; try (discriminate H).
  injection H as H_l H_r. eauto.
Qed.

Lemma t_noteq_app : forall t s, t = App s t -> False.
  intro t.
  induction t using exp_ind3; intros; try (discriminate H).
  injection H as H_l H_r. eauto.
Qed.

Lemma s_noteq_lam : forall s, s = Lam s -> False.
Proof.
  intro s.
  induction s using exp_ind3; intros; try (discriminate H).
  injection H as H_'. eauto.
Qed.
  
Lemma s_noteq_inst : forall s σ, s = Inst s σ -> False.
Proof.
  intro s.
  induction s using exp_ind3; intros; try (discriminate H).
  injection H as H_l H_r. eauto.
Qed.  

Lemma σ_noteq_cons : forall σ s, σ = Cons s σ -> False.
Proof.
  intro σ.
  induction σ using sexp_ind3; intros; try (discriminate H).
  injection H as H_l H_r. eauto.
Qed.  


Lemma σ_noteq_comp : forall σ τ, σ = σ >> τ -> False.
Proof.
  intro σ.
  induction σ using sexp_ind3; intros; (try (discriminate H)).
  injection H as H_l H_r. eauto.
Qed.

Lemma τ_noteq_comp : forall τ σ, τ = σ >> τ -> False.
Proof.
  intro τ.
  induction τ using sexp_ind3; intros; (try (discriminate H)).
  injection H as H_l H_r. eauto.
Qed.

