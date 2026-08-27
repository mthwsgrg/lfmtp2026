Require Export List ListSet.
Export ListNotations.
Require Export Lia.

Section SetPropertiesWithEqDec.
  
  Context {A: Type} {AEq_dec : forall (x y:A), {x=y} + {x <> y}}.


Lemma set_nocommon_1_2 : forall S S', (forall (X: A), set_In X S -> ~set_In X S') <-> (forall (X: A), set_In X S' -> ~set_In X S) .
  intros.
  split ; intros; unfold not in *; intros;now specialize (H _ H1). 
Qed.

Lemma set_nocommon_1_3: forall S S', (forall X, set_In X S -> ~set_In X S') <-> set_inter AEq_dec S S' = [].
  intros.
  split.
  -  revert S'. induction S; intros.
     +  now simpl.
     +  simpl.
        specialize (H a) as H_a.
        simpl in H_a. specialize (H_a (or_introl eq_refl)).
        apply (set_mem_complete2 AEq_dec) in H_a.
        rewrite H_a.
        apply IHS; intros.
        apply H. simpl. now right.     
  - revert S'.
    induction S; intros.
    + destruct H0.
    + simpl in *.
      destruct H0.
      * subst.
        destruct (set_mem AEq_dec X S') eqn: HEqn.
        inversion H.
        now apply (set_mem_complete1 AEq_dec).
      * apply IHS; eauto.
        destruct (set_mem AEq_dec a S').
        inversion H.
        assumption.      
Qed.


Lemma set_nocommon_1_3_for: forall S S', (forall X, set_In X S -> ~set_In X S') -> set_inter AEq_dec S S' = [].
Proof.
  apply set_nocommon_1_3.
Qed.

Lemma set_nocommon_1_3_back: forall S S', set_inter AEq_dec S S' = [] -> (forall X, set_In X S -> ~set_In X S').
Proof.
  apply set_nocommon_1_3.
Qed.


Lemma set_nocommon_3_4 : forall S S', set_inter AEq_dec S S' = [] <-> set_inter AEq_dec S' S = [].
Proof.
  intros S S'.
  split; intros; apply set_nocommon_1_3; apply set_nocommon_1_2;    now apply set_nocommon_1_3.  
Qed.

Lemma set_nocommon_inter_forall : forall S S', set_inter AEq_dec S S' = [] -> (forall X, set_In X S -> ~set_In X S').  
Proof.
  eapply set_nocommon_1_3.
Qed.  

Lemma set_nocommon_inter_forall_flip : forall S S', set_inter AEq_dec S S' = [] -> (forall X, set_In X S' ->
                                                                                ~set_In X S).
Proof.
  intros.
  rewrite set_nocommon_3_4 in H.
  eapply set_nocommon_inter_forall.
  apply H.
  apply H0.
Qed.
Lemma set_nocommon_forall_inter : forall S S', (forall X, set_In X S -> ~set_In X S') ->
                                          set_inter AEq_dec S S' = [].
Proof.
  eapply set_nocommon_1_3.
Qed.  

Lemma set_nocommon_forall_inter_flip : forall S S', (forall X, set_In X S' -> ~set_In X S) ->
                                               set_inter AEq_dec S S' = [].
Proof.
  intros.
  rewrite set_nocommon_3_4.
  now apply set_nocommon_forall_inter.
Qed.

Lemma set_list_app_neq :  forall P a b, a<> b -> set_add AEq_dec b (a :: P) = a :: (set_add AEq_dec b P).
Proof.
  intros.
  simpl.
  destruct (AEq_dec b a) as [Heq | Hn].
  congruence.
  reflexivity.
Qed.

Lemma set_list_app_eq :  forall P a, set_add AEq_dec a (a :: P) =  a :: P.
Proof.
  intros.
  simpl.
  destruct (AEq_dec a a). 
  reflexivity.
  contradiction.
Qed.


Lemma set_union_assoc : forall a X Y Z,  set_In a (set_union AEq_dec X (set_union AEq_dec Y Z)) <->
                                                                                   set_In a (set_union AEq_dec (set_union AEq_dec X Y) Z).
Proof.
  intros. split.
  intros. apply set_union_elim in H.
  destruct H. apply set_union_intro1. now apply set_union_intro1.
  apply set_union_elim in H. destruct H.
  apply set_union_intro1. now apply set_union_intro2.
  now repeat apply set_union_intro2.

  intros. apply set_union_elim in H.
  destruct H.  apply set_union_elim in H.
  destruct H. now apply set_union_intro1.
  apply set_union_intro2. now apply set_union_intro1.
  now repeat apply set_union_intro2.
Qed. 

Lemma subset_list : forall (l l' : list A),
  NoDup l  ->
  (forall b, In b l -> In b l') ->
  length l <= length l'.
Proof.
  intros l l' H_nodup H_incl.
  apply NoDup_incl_length.
  - exact H_nodup.
  - exact H_incl.
Qed.

Lemma subset_list' : forall (l l' : list A),
     NoDup l ->                     
     (forall b, In b l -> In b l') ->
     (exists a', In a' l' /\ ~ In a' l) ->
     length l < length l' .
Admitted.

End SetPropertiesWithEqDec.
      

(* Lemmas for natural numbers *)

Lemma nat_leq_inv : forall m n, n <= m -> m >= n.
Proof. intros; lia. Qed.


Lemma nat_lt_inv : forall m n, n < m -> m > n.
Proof. intros; lia. Qed.
