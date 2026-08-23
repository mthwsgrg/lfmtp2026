Require Export List ListSet.
Export ListNotations.


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
Admitted.

Lemma set_nocommon_inter_forall_flip : forall S S', set_inter AEq_dec S S' = [] -> (forall X, set_In X S' ->
                                                                                ~set_In X S).
Admitted.

Lemma set_nocommon_forall_inter : forall S S', (forall X, set_In X S -> ~set_In X S') ->
                                          set_inter AEq_dec S S' = [].
Admitted.

Lemma set_nocommon_forall_inter_flip : forall S S', (forall X, set_In X S' -> ~set_In X S) ->
                                               set_inter AEq_dec S S' = [].
Admitted.

End SetPropertiesWithEqDec.
      

