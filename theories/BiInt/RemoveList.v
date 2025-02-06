Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.

From Undecidability.FOL Require Import Syntax.Facts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.

From FOL Require Import ExistsT.
From FOL Require Import BiInt.BiInt SyntaxFeatures.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Import BiIntSyntax.


Section Remove.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Existing Instance falsity_on.

  Context {eq_dec_preds : eq_dec Σ_preds}.
  Context {eq_dec_funcs : eq_dec Σ_funcs}.

Lemma In_dec : forall l (a : form) , (In a l) + ((In a l) -> False).
Proof.
induction l.
- right. intro. destruct H.
- intro a0. pose (IHl a0). destruct s.
  * left. apply in_cons. assumption.
  * destruct (eq_dec_form eq_dec_funcs eq_dec_preds a a0).
    + subst. left. apply in_eq.
    + right. intro. inversion H.
      { apply n. assumption. }
      { apply f. assumption. }
Qed.

(* Let us prove some lemmas about remove. *)

Lemma in_not_touched_remove : forall l1 a0 a1,
        In a0 l1 -> a0 <> a1 -> In a0 (remove (eq_dec_form eq_dec_funcs eq_dec_preds) a1 l1).
Proof.
induction l1.
- intros. inversion H.
- intros. simpl. destruct (eq_dec_form eq_dec_funcs eq_dec_preds a1 a).
  * subst. apply IHl1. inversion H. exfalso. apply H0. auto. assumption. assumption.
  * inversion H. subst. apply in_eq. apply in_cons. apply IHl1. assumption. assumption.
Qed.

Lemma remove_dist_app {A : Type} (Heq_dec : forall x y : A, {x = y} + {x <> y}) :
        forall (a : A) l1 l2, (@remove A Heq_dec a (l1 ++ l2)) =
                              (@remove A Heq_dec a l1) ++ (@remove A Heq_dec a l2).
Proof.
intros a l1. induction l1.
- intro l2. rewrite app_nil_l. simpl. reflexivity.
- intro l2. simpl. destruct (Heq_dec a a0).
  * apply IHl1.
  * simpl. rewrite IHl1. reflexivity.
Qed.

Lemma remove_not_in_anymore : forall l A,
          (In A (remove (eq_dec_form eq_dec_funcs eq_dec_preds) A l)) -> False.
Proof.
induction l.
- intros. simpl in H. inversion H.
- intros. simpl in H. destruct (eq_dec_form eq_dec_funcs eq_dec_preds A a). subst. apply IHl in H. assumption.
  inversion H. apply n. symmetry. assumption. apply IHl in H0. assumption.
Qed.

Lemma in_remove_in_init : forall l A B,
    In A (remove (eq_dec_form eq_dec_funcs eq_dec_preds) B l) -> In A l.
Proof.
induction l.
- intros. simpl. inversion H.
- intros. destruct (eq_dec_form eq_dec_funcs eq_dec_preds A a). subst. apply in_eq. apply in_cons.
  pose (IHl A B). apply i. simpl in H. destruct (eq_dec_form eq_dec_funcs eq_dec_preds B a).
  * subst. assumption.
  * inversion H. exfalso. apply n. symmetry. assumption. assumption.
Qed.

Lemma remove_preserv_NoDup : forall l A, NoDup l -> 
  NoDup (remove (eq_dec_form eq_dec_funcs eq_dec_preds) A l).
Proof.
induction l.
- intros. simpl. apply NoDup_nil.
- intros. simpl. destruct (eq_dec_form eq_dec_funcs eq_dec_preds A a).
  * subst. apply IHl. inversion H. assumption.
  * apply NoDup_cons. intro. apply in_remove_in_init in H0. inversion H. apply H3. assumption.
    apply IHl. inversion H. assumption.
Qed.

Lemma NoDup_destr_split : forall l1 l2 (A : form), NoDup (l1 ++ A :: l2) -> NoDup (l1 ++ l2).
Proof.
induction l1.
- intros. rewrite app_nil_l. rewrite app_nil_l in H. inversion H. assumption.
- intros. simpl. apply NoDup_cons. intro. inversion H. subst. apply H3. apply in_app_or in H0.
  destruct H0. apply in_or_app. left. assumption. apply in_or_app. right. apply in_cons.
  assumption. simpl in H. inversion H. subst. apply IHl1 with (A:=A). assumption.
Qed.

Lemma remove_le_length : forall l A, length (remove (eq_dec_form eq_dec_funcs eq_dec_preds) A l) <= length l.
Proof.
induction l.
- intros. simpl. reflexivity.
- intros. simpl. destruct (eq_dec_form eq_dec_funcs eq_dec_preds A a).
  * subst. apply le_S. apply IHl.
  * simpl. apply le_n_S. apply IHl.
Qed.

Lemma remove_In_smaller_length : forall l A,
                                 In A l -> length (remove (eq_dec_form eq_dec_funcs eq_dec_preds) A l) < length l.
Proof.
induction l.
- intros. inversion H.
- intros. simpl. destruct (eq_dec_form eq_dec_funcs eq_dec_preds A a).
  * subst. unfold lt. apply le_n_S. apply remove_le_length.
  * simpl. rewrite <- Nat.succ_lt_mono. apply IHl. inversion H. subst. exfalso. apply n. auto.
    assumption.
Qed.

Lemma double_remove {A : Type} (Heq_dec : forall x y : A, {x = y} + {x <> y}) :
      forall a l, (@remove A Heq_dec a (@remove A Heq_dec a l)) = (@remove A Heq_dec a l).
Proof.
intros a l. induction l.
- simpl. reflexivity.
- simpl. destruct (Heq_dec a a0).
  * subst. apply IHl.
  * simpl. destruct (Heq_dec a a0).
    + exfalso. apply n. assumption.
    + rewrite IHl. reflexivity.
Qed.

Lemma permut_remove {A : Type} (Heq_dec : forall x y : A, {x = y} + {x <> y}) :
      forall a0 a1 l, (@remove A Heq_dec a0 (@remove A Heq_dec a1 l)) =
                      (@remove A Heq_dec a1 (@remove A Heq_dec a0 l)).
Proof.
intros a0 a1 l. induction l.
- simpl. reflexivity.
- simpl. destruct (Heq_dec a1 a).
  * subst. simpl. destruct (Heq_dec a0 a).
    + subst. reflexivity.
    + simpl. destruct (Heq_dec a a). apply IHl. exfalso. apply n0. reflexivity.
  * simpl. destruct (Heq_dec a0 a).
    + subst. assumption.
    + simpl. destruct (Heq_dec a1 a). exfalso. apply n. assumption.
      rewrite IHl. reflexivity.
Qed.

Lemma In_remove_diff : forall l A B, In A (remove (eq_dec_form eq_dec_funcs eq_dec_preds) B l) -> A <> B.
Proof.
induction l ; intros.
- intro. simpl in H. assumption.
- simpl in H. destruct (eq_dec_form eq_dec_funcs eq_dec_preds B a).
  * subst. apply IHl. assumption.
  * inversion H.
    + subst. intro. apply n. symmetry. assumption.
    + apply IHl. assumption.
Qed.


(* Now we define remove_list and prove some lemmas about it. *)

Fixpoint remove_list (l1 l2: list form) : list form :=
match l1 with
  | nil => l2
  | h1 :: t1 => remove (eq_dec_form eq_dec_funcs eq_dec_preds) h1 (remove_list t1 l2)
end.

Lemma remove_list_of_nil : forall (l : list form), remove_list l nil = nil.
Proof.
induction l.
- simpl. reflexivity.
- simpl. rewrite IHl. simpl. reflexivity.
Qed.

Lemma app_remove_list : forall (l1 l2 l3 : list form),
        remove_list (l1 ++ l2) l3 = remove_list l1 (remove_list l2 l3).
Proof.
induction l1.
- simpl. firstorder.
- induction l2.
  * intro l3. rewrite app_nil_r. simpl. reflexivity.
  * intro l3. simpl. pose (IHl1 (a0 :: l2) l3). simpl in e.
    rewrite e. reflexivity.
Qed.

Lemma remove_list_preserv_NoDup : forall l1 l2, NoDup l2 -> NoDup (remove_list l1 l2).
Proof.
induction l1.
- intros. simpl. assumption.
- intros. simpl. apply IHl1 in H. apply remove_preserv_NoDup with (A:=a) in H.
  assumption.
Qed.

Lemma remove_list_cont : forall l1 A, In A l1 -> (forall l2, In A (remove_list l1 l2) -> False).
Proof.
induction l1.
- intros. inversion H.
- intros. inversion H.
  * subst. simpl in H0. apply remove_not_in_anymore in H0. assumption.
  * simpl in H0. pose (IHl1 A H1 l2). apply f. apply in_remove_in_init with (B:= a). assumption.
Qed.

Lemma remove_list_dist_app : forall (l1 l2 l3 : list form),
        remove_list l1 (l2 ++ l3) = (remove_list l1 l2) ++ (remove_list l1 l3).
Proof.
induction l1.
- intros. simpl. reflexivity.
- simpl. intros. rewrite IHl1. simpl. rewrite remove_dist_app. reflexivity.
Qed.

Lemma permut_remove_remove_list : forall a (l1 l2 : list form),
      remove (eq_dec_form eq_dec_funcs eq_dec_preds) a (remove_list l1 l2) =
      remove_list l1 (remove (eq_dec_form eq_dec_funcs eq_dec_preds) a l2).
Proof.
intros a l1. generalize dependent a. induction l1 ; simpl.
- reflexivity.
- intros. rewrite permut_remove. rewrite IHl1. reflexivity.
Qed.

Lemma swap_remove_list : forall (l1 l2 l3 : list form),
      remove_list (l1 ++ l2) l3 = remove_list (l2 ++ l1) l3.
Proof.
induction l1.
- intros. rewrite app_nil_l. rewrite app_nil_r. reflexivity.
- induction l2.
  * rewrite app_nil_l. rewrite app_nil_r. reflexivity.
  * intro l3. simpl. rewrite IHl1. simpl. rewrite permut_remove.
    rewrite <- IHl2. simpl. rewrite IHl1. reflexivity.
Qed.

Lemma redund_remove_remove_list : forall a (l1 l2 : list form),
      remove (eq_dec_form eq_dec_funcs eq_dec_preds) a (remove_list (remove (eq_dec_form eq_dec_funcs eq_dec_preds) a l1) l2) = 
      remove (eq_dec_form eq_dec_funcs eq_dec_preds) a (remove_list l1 l2).
Proof.
intro a. induction l1.
- intro l2. simpl. reflexivity.
- intro l2. simpl. destruct (eq_dec_form eq_dec_funcs eq_dec_preds a a0).
  * rewrite IHl1. subst. rewrite double_remove. reflexivity.
  * simpl. rewrite permut_remove. rewrite IHl1. apply permut_remove.
Qed.

Lemma redund_remove : forall (l1 l2 l3 : list form) a,
      remove (eq_dec_form eq_dec_funcs eq_dec_preds) a (remove_list l1 (remove_list (remove (eq_dec_form eq_dec_funcs eq_dec_preds) a l2) l3)) =
      remove (eq_dec_form eq_dec_funcs eq_dec_preds) a (remove_list l1 (remove_list l2 l3)).
Proof.
intros. repeat rewrite <- app_remove_list. rewrite swap_remove_list.
rewrite app_remove_list. rewrite redund_remove_remove_list. rewrite <- app_remove_list.
rewrite swap_remove_list. reflexivity.
Qed.

Lemma redund_remove_list : forall (l1 l2 l3 : list form),
      remove_list l1 (remove_list (remove_list l1 l2) l3) = remove_list l1 (remove_list l2 l3).
Proof.
induction l1 ; intros ; simpl.
- reflexivity.
- rewrite redund_remove. rewrite IHl1. reflexivity.
Qed.

Lemma remove_list_in_single : forall (l1 : list form) a, (In a l1) -> remove_list l1 (a :: nil) = nil.
Proof.
induction l1.
- intros. inversion H.
- intros. inversion H.
  * subst. simpl. rewrite permut_remove_remove_list. simpl. destruct (eq_dec_form eq_dec_funcs eq_dec_preds a0 a0).
    apply remove_list_of_nil. exfalso. apply n. reflexivity.
  * apply IHl1 in H0. simpl. rewrite H0. simpl. reflexivity.
Qed.

Lemma not_removed_remove_list : forall l2 l1 A, In A l2 -> (In A l1 -> False) -> In A (remove_list l1 l2).
Proof.
induction l2.
- intros. inversion H.
- induction l1.
  * intros. simpl. assumption.
  * intros. simpl. pose (@in_not_touched_remove (remove_list l1 (a :: l2))). pose (i A).
    pose (i0 a0). apply i1. apply IHl1. assumption. intro. apply H0. apply in_cons. assumption.
    clear i1. clear i0. clear i. destruct (eq_dec_form eq_dec_funcs eq_dec_preds A a0). intro. apply H0. subst. apply in_eq.
    assumption.
Qed.

Lemma add_remove_list_preserve_NoDup : forall (l1 l2 : list form),
            NoDup l1 -> NoDup l2 -> NoDup (l1 ++ (remove_list l1 l2)).
Proof.
induction l1.
- intros. rewrite app_nil_l. simpl. assumption.
- intros. simpl. apply NoDup_cons.
  * intro. apply in_app_or in H1. destruct H1. inversion H. apply H4. assumption.
    apply remove_not_in_anymore in H1. assumption.
  * rewrite permut_remove_remove_list. apply IHl1. inversion H. assumption.
    apply remove_preserv_NoDup. assumption.
Qed.

Lemma remove_list_is_in : forall l1 l2 A, In A l1 -> In A (l2 ++ (remove_list l2 l1)).
Proof.
intros. pose (In_dec l2 A). destruct s.
- apply in_or_app. left. assumption.
- apply in_or_app. right. apply not_removed_remove_list ; assumption.
Qed.

Lemma In_remove_same : forall l1 l2 A, In A l1 ->
                remove_list l1 (A :: l2) = remove_list l1 l2.
Proof.
induction l1.
- intros. inversion H.
- intros. inversion H.
  * subst. simpl. rewrite permut_remove_remove_list. simpl. destruct (eq_dec_form eq_dec_funcs eq_dec_preds A A).
    rewrite permut_remove_remove_list. reflexivity. exfalso. apply n. reflexivity.
  * simpl. pose (IHl1 l2 A H0). rewrite e. reflexivity.
Qed.

Lemma In_remove_length_same : forall l1 l2 A, In A l1 ->
                length (remove_list l1 (A :: l2)) = length (remove_list l1 l2).
Proof.
intros. rewrite In_remove_same. reflexivity. assumption.
Qed.

Lemma length_le_remove_list : forall (l1 l2 : list form), length (remove_list l1 l2) <= length l2.
Proof.
induction l1.
- intros. auto.
- intros. simpl. rewrite permut_remove_remove_list. pose (IHl1 (remove (eq_dec_form eq_dec_funcs eq_dec_preds) a l2)).
  apply Nat.le_trans with (m:=length (remove (eq_dec_form eq_dec_funcs eq_dec_preds) a l2)). assumption.
  apply remove_le_length.
Qed.

Lemma remove_list_singl_id_or_nil : forall l A, remove_list l (A :: nil) = nil \/ remove_list l (A :: nil) = [A].
Proof.
induction l.
- intros. right. auto.
- intros. pose (IHl A). destruct o. left. simpl. rewrite H. auto.
  simpl. rewrite H. destruct (eq_dec_form eq_dec_funcs eq_dec_preds A a).
  * subst. left. simpl. destruct (eq_dec_form eq_dec_funcs eq_dec_preds a a). reflexivity. exfalso. apply n.
    reflexivity.
  * right. simpl. destruct (eq_dec_form eq_dec_funcs eq_dec_preds a A). exfalso. apply n. symmetry. assumption.
    reflexivity.
Qed.

Lemma remove_list_non_empty_inter_smaller_length : forall l2 l1 A,
                                 In A l1 -> In A l2 -> length (remove_list l1 l2) < length l2.
Proof.
induction l2.
- intros. inversion H0.
- intros. simpl. destruct (eq_dec_form eq_dec_funcs eq_dec_preds A a).
  * subst. rewrite In_remove_length_same. 2: assumption. unfold lt. apply le_n_S.
    apply length_le_remove_list.
  * inversion H0.
    + exfalso. apply n. symmetry. assumption.
    + assert (a :: l2 = [a] ++ l2). auto. rewrite H2. rewrite remove_list_dist_app.
      rewrite app_length. pose (@remove_list_singl_id_or_nil l1 a). destruct o.
      rewrite H3. simpl. apply Nat.lt_lt_succ_r. apply IHl2 with (A:=A) ; assumption.
      rewrite H3. simpl. rewrite <- Nat.succ_lt_mono. apply IHl2 with (A:=A) ; assumption.
Qed.

Lemma remove_list_delete_head : forall l1 l2 l3 A, remove_list (l1 ++ A :: l2) (A :: l3) = remove_list (l1 ++ A :: l2) l3.
Proof.
induction l1 ; intros ; simpl.
- rewrite permut_remove_remove_list. simpl. destruct (eq_dec_form eq_dec_funcs eq_dec_preds A A). symmetry. apply permut_remove_remove_list.
  exfalso. apply n. reflexivity.
- rewrite IHl1. reflexivity.
Qed.

Lemma remove_list_delete_head_In : forall l1 l2 A, In A l1 -> remove_list l1 (A :: l2) = remove_list l1 l2.
Proof.
intros. pose (In_split A l1 H). destruct e. destruct H0. subst. apply remove_list_delete_head.
Qed.

Lemma remove_list_in_nil : forall l1 l2 l3 A,
        remove_list l1 (l2 ++ A :: l3) = nil ->
        (existsT2 l4 l5, l1 = l4 ++ A :: l5).
Proof.
induction l1.
- intros. simpl in H. destruct l2 ; inversion H.
- induction l2.
  * intros. simpl in H. rewrite permut_remove_remove_list in H. simpl in H. destruct (eq_dec_form eq_dec_funcs eq_dec_preds a A).
    + subst. exists nil. exists l1. auto.
    + pose (IHl1 nil (remove (eq_dec_form eq_dec_funcs eq_dec_preds) a l3)). simpl in s. apply s in H. destruct H. destruct s0.
      exists ([a] ++ x). exists x0. subst. auto.
  * intros. simpl in H. rewrite permut_remove_remove_list in H. simpl in H. destruct (eq_dec_form eq_dec_funcs eq_dec_preds a a0).
    + subst. pose (IHl2 l3 A). apply s. rewrite <- permut_remove_remove_list in H. simpl. assumption.
    + pose (IHl1 nil (remove (eq_dec_form eq_dec_funcs eq_dec_preds) a (l2 ++ A :: l3)) a0). pose (s H). repeat destruct s0.
      subst. apply IHl2 with (l3:= l3). simpl. rewrite permut_remove_remove_list.
      rewrite remove_list_delete_head in H. assumption.
Qed.

Lemma remove_list_is_nil : forall l1 l2, (remove_list l1 l2 = nil <-> (forall A, (In A l2) -> (In A l1))).
Proof.
induction l1.
- intro l2. split.
  * intros. simpl in H. rewrite <- H. assumption.
  * intros. simpl. destruct l2.
    + reflexivity.
    + exfalso. pose (H f). assert (In f (f :: l2)). apply in_eq. apply i in H0. inversion H0.
- induction l2.
  * split.
    + intros. inversion H0.
    + intros. apply remove_list_of_nil.
  * split.
    + intros. simpl in H. rewrite permut_remove_remove_list in H. simpl in H. destruct (eq_dec_form eq_dec_funcs eq_dec_preds a a0).
      subst. inversion H0. subst. apply in_eq. rewrite <- permut_remove_remove_list in H. simpl in IHl2.
      rewrite IHl2 in H. apply H in H1. destruct H1. subst. apply in_eq. apply in_cons. assumption.
      inversion H0. subst. apply in_cons. pose (@remove_list_in_nil l1 nil (remove (eq_dec_form eq_dec_funcs eq_dec_preds) a l2) A).
      simpl in s. apply s in H. destruct H. destruct s0. subst. apply in_or_app. right. apply in_eq.
      apply IHl2. 2: assumption. simpl. rewrite permut_remove_remove_list.
      pose (app_eq_nil (remove_list l1 (a0 :: nil)) (remove_list l1 (remove (eq_dec_form eq_dec_funcs eq_dec_preds) a l2))). simpl in a1.
      assert (H2: remove_list l1 (a0 :: nil) ++ remove_list l1 (remove (eq_dec_form eq_dec_funcs eq_dec_preds) a l2) = nil).
      rewrite <- remove_list_dist_app. simpl. assumption. apply a1 in H2. destruct H2. assumption.
    + intros. simpl. rewrite permut_remove_remove_list. simpl. destruct (eq_dec_form eq_dec_funcs eq_dec_preds a a0).
      { subst. rewrite <- permut_remove_remove_list. simpl in IHl2. rewrite IHl2. intros.
        pose (H A). apply i. apply in_cons. assumption. }
      { assert (H1: (forall (A : form), In A l2 -> In A (a :: l1))). intros. apply H.
        apply in_cons. assumption. apply IHl2 in H1.
        assert (H2: a0 :: remove (eq_dec_form eq_dec_funcs eq_dec_preds) a l2 = [a0] ++ remove (eq_dec_form eq_dec_funcs eq_dec_preds) a l2). auto.
        rewrite H2. rewrite remove_list_dist_app. clear H2. rewrite <- permut_remove_remove_list.
        simpl in H1. rewrite H1. rewrite app_nil_r. apply remove_list_in_single. pose (H a0).
        assert (H3: In a0 (a0 :: l2)). apply in_eq. apply i in H3. inversion H3. exfalso. apply n.
        assumption. assumption. }
Qed.

Lemma remove_delete_origin : forall l1 l2 (A B : form), (A <> B) ->
            length (remove (eq_dec_form eq_dec_funcs eq_dec_preds) A (l1 ++ B :: l2)) = S (length (remove (eq_dec_form eq_dec_funcs eq_dec_preds) A (l1 ++ l2))).
Proof.
induction l1.
- intros. repeat rewrite app_nil_l. simpl. destruct (eq_dec_form eq_dec_funcs eq_dec_preds A B). exfalso. apply H. assumption.
  simpl. reflexivity.
- intros. simpl. destruct (eq_dec_form eq_dec_funcs eq_dec_preds A a).
  * apply IHl1. assumption.
  * simpl. apply eq_S. apply IHl1. assumption.
Qed.

Lemma keep_list_delete_head_not_origin : forall l1 l2 l3 A, ((In A l1) -> False) ->
                length (remove_list l1 (l2 ++ A :: l3)) = S (length (remove_list l1 (l2 ++ l3))).
Proof.
induction l1.
- intros. simpl. rewrite app_length. simpl. rewrite app_length. auto.
- intros. simpl. repeat rewrite remove_list_dist_app. assert (In A l1 -> False).
  intro. apply H. apply in_cons. assumption. assert (A :: l3 = [A] ++ l3).
  auto. rewrite H1. rewrite remove_list_dist_app. pose (remove_list_singl_id_or_nil l1 A).
  destruct o. exfalso. rewrite remove_list_is_nil in H2. apply H0. apply H2.
  apply in_eq. rewrite H2. apply remove_delete_origin. intro. apply H. subst. apply in_eq.
Qed.

Lemma keep_list_delete_head_not_In : forall l1 l2 A, ((In A l1) -> False) ->
                length (remove_list l1 (A :: l2)) = S (length (remove_list l1 l2)).
Proof.
intros. pose (@keep_list_delete_head_not_origin l1 nil l2 A H). repeat rewrite app_nil_l in e.
assumption.
Qed.

Lemma In_remove_In_list : forall (A B : form) l, In A (remove (eq_dec_form eq_dec_funcs eq_dec_preds) B l) -> In A l.
Proof.
induction l ; intros.
- simpl in H. destruct H.
- simpl in H. destruct (eq_dec_form eq_dec_funcs eq_dec_preds B a).
  * subst. apply in_cons. apply IHl. assumption.
  * inversion H.
    + subst. apply in_eq.
    + apply in_cons. apply IHl. assumption.
Qed.

Lemma In_remove_list_In_list : forall A l1 l2, In A (remove_list l1 l2) -> In A l2.
Proof.
intro A. induction l1 ; intros.
- simpl in H. assumption.
- simpl in H. apply In_remove_In_list in H. apply IHl1. assumption.
Qed.

Lemma In_remove_list_In_list_not_In_remove_list : forall A l1 l2,
            In A (remove_list l1 l2) -> (In A l2 /\ ((In A l1) -> False)).
Proof.
intro A. induction l1 ; intros.
- simpl in H. split. assumption. intro. inversion H0.
- simpl in H. split. apply In_remove_In_list in H. apply IHl1. assumption. intro.
  inversion H0.
  * subst. apply remove_not_in_anymore in H. assumption.
  * apply In_remove_In_list in H. apply IHl1 in H. destruct H. apply H2. assumption.
Qed.

Lemma remove_list_incr_decr3 : forall (l3 l2 l1 : list form),
              (incl l1 l2) ->
              length (remove_list l2 l3) <= length (remove_list l1 l3).
Proof.
induction l3 ; intros.
- repeat rewrite remove_list_of_nil. auto.
- destruct (In_dec l2 a).
  + rewrite remove_list_delete_head_In. 2: assumption. destruct (In_dec l1 a).
    * rewrite remove_list_delete_head_In. 2: assumption. apply IHl3 ; auto.
    * rewrite keep_list_delete_head_not_In. 2: assumption. apply Nat.le_le_succ_r.
      apply IHl3. assumption.
  + repeat rewrite keep_list_delete_head_not_In. apply le_n_S. apply IHl3 ; auto.
    intro. apply f. apply H. assumption. assumption.
Qed.

Lemma remove_list_incr_decr1 : forall (l3 l1 l2: list form),
              (exists A, In A l2 /\ In A l3 /\ (In A l1 -> False)) ->
              (incl l1 l2) ->
              length (remove_list l2 l3) < length (remove_list l1 l3).
Proof.
induction l3.
- intros. destruct H. destruct H. destruct H1. exfalso. inversion H1.
- intros. destruct H. destruct H. destruct H1. destruct (eq_dec_form eq_dec_funcs eq_dec_preds a x).
  * subst. rewrite remove_list_delete_head_In. 2: assumption.
    rewrite keep_list_delete_head_not_In. 2: assumption. unfold lt.
    apply le_n_S. apply remove_list_incr_decr3. assumption.
  * inversion H1. exfalso. apply n ; assumption.
    assert (H4: exists A : form, In A l2 /\ In A l3 /\ (In A l1 -> False)).
    exists x. auto. apply IHl3 in H4. 2 : assumption. unfold lt.
    destruct (In_dec l2 a).
    + rewrite remove_list_delete_head_In. 2: assumption. destruct (In_dec l1 a).
      { rewrite remove_list_delete_head_In. 2: assumption. apply H4. }
      { rewrite keep_list_delete_head_not_In. 2: assumption. apply le_n_S.
        unfold lt in H4. apply Nat.lt_le_incl. assumption. }
    + rewrite keep_list_delete_head_not_In. 2: assumption. rewrite keep_list_delete_head_not_In.
      unfold lt in H4. apply le_n_S. assumption. intro. apply f. apply H0. assumption.
Qed.

Lemma remove_list_incr_decr2 : forall (l4 l3 l1 : list form),
              (NoDup l4) ->
              (NoDup l3) ->
              (incl l4 l3) ->
              length (remove_list l1 l4) <= length (remove_list l1 l3).
Proof.
induction l4.
- intros. rewrite remove_list_of_nil. simpl. apply Nat.le_0_l.
- intros. destruct (In_dec l1 a).
  * rewrite remove_list_delete_head_In. 2: assumption. apply IHl4 ; try assumption.
    inversion H. assumption. unfold incl. intros. apply H1. apply in_cons. assumption.
  * rewrite keep_list_delete_head_not_In. 2: assumption. assert (H2: In a l3). apply H1.
    apply in_eq. pose (in_split a l3 H2). repeat destruct e. destruct H3. rewrite H3.
    rewrite keep_list_delete_head_not_origin. 2: assumption. apply le_n_S. apply IHl4.
    inversion H. assumption. subst. apply NoDup_destr_split with (A:=a). assumption.
    inversion H. unfold incl. intros. subst. assert (H9 : In a0 (a :: l4)). apply in_cons.
    assumption. pose (H1 a0 H9). apply in_app_or in i. destruct i. apply in_or_app. left.
    assumption. inversion H3. subst. exfalso. apply H6. assumption. apply in_or_app. right.
    assumption.
Qed.

Lemma remove_list_incr_decr4 : forall (l4 l3 l1: list form),
              (NoDup l4) ->
              (NoDup l3) ->
              (incl l4 l3) ->
              ((incl l3 l4) -> False) ->
              (exists A, (In A l3) /\ ((In A l1) -> False) /\ ((In A l4) -> False)) ->
              length (remove_list l1 l4) < length (remove_list l1 l3).
Proof.
induction l4.
- intros. rewrite remove_list_of_nil. simpl. destruct H3. destruct H3. destruct H4. pose (In_split x l3 H3).
  destruct e. destruct H6. subst. rewrite keep_list_delete_head_not_origin. 2: assumption.
  apply Nat.lt_0_succ.
- intros. destruct (In_dec l1 a).
  * rewrite remove_list_delete_head_In. 2: assumption. apply IHl4 ; try assumption.
    inversion H. assumption. unfold incl. intros. apply H1. apply in_cons. assumption.
    intro. apply H2. unfold incl. intros. apply in_cons. apply H4. assumption. destruct H3.
    destruct H3. destruct H4. exists x. repeat split ; try assumption. intro. apply H5.
    apply in_cons. assumption.
  * rewrite keep_list_delete_head_not_In. 2: assumption. assert (In a l3). apply H1.
    apply in_eq. pose (In_split a l3 H4). destruct e. destruct H5. subst.
    rewrite keep_list_delete_head_not_origin. 2 : assumption. rewrite <- Nat.succ_lt_mono.
    apply IHl4. inversion H. assumption. apply NoDup_destr_split with (A:=a). assumption.
    unfold incl. intros. pose (H1 a0). assert (In a0 (a :: l4)). apply in_cons. assumption.
    apply i in H6. apply in_app_or in H6. destruct H6. apply in_or_app. left. assumption.
    inversion H6. subst. inversion H. exfalso. apply H9. assumption. apply in_or_app. right.
    assumption. intro. apply H2. unfold incl. intros. apply in_app_or in H6. destruct H6.
    apply in_cons. apply H5. apply in_or_app. left. assumption. inversion H6. subst. apply in_eq.
    apply in_cons. apply H5. apply in_or_app. right. assumption.
    destruct H3. destruct H3. destruct H5. exists x1. repeat split ; try assumption.
    apply in_app_or in H3. destruct H3. apply in_or_app. left. assumption. inversion H3.
    subst. exfalso. apply H6. apply in_eq. apply in_or_app. right. assumption.
    intro. apply H6. apply in_cons. assumption.
Qed.

Lemma remove_list_incr_decr : forall (l1 l2 l3 l4 : list form),
              (NoDup l4) ->
              (NoDup l3) ->
              (exists A, In A l2 /\ In A l3 /\ (In A l1 -> False)) ->
              (incl l1 l2) ->
              (incl l4 l3) ->
              length (remove_list l2 l4) < length (remove_list l1 l3).
Proof.
intros. unfold lt.
pose (@remove_list_incr_decr2 _ _ l1 H H0 H3).
repeat destruct H1. destruct H4. destruct (In_dec l4 x).
- assert (H6: (exists A, In A l2 /\ In A l4 /\ (In A l1 -> False))).
  exists x. repeat split ; assumption. pose (@remove_list_incr_decr1 l4 l1 l2 H6 H2).
  unfold lt in l0. apply Nat.le_trans with (m:=length (remove_list l1 l4)) ; assumption.
- assert ((incl l3 l4) -> False). intros. apply f. apply H6. assumption.
  assert ((exists A, (In A l3) /\ ((In A l1) -> False) /\ ((In A l4) -> False))). exists x. auto.
  pose (@remove_list_incr_decr3 l4 l2 l1 H2). pose (@remove_list_incr_decr4 l4 l3 l1 H H0 H3 H6 H7).
  unfold lt in l5. apply le_n_S in l0.
  apply Nat.le_trans with (m:=S (length (remove_list l1 l4))) ; assumption.
Qed.

Lemma In_remove_list_remove_redund : forall l1 l2 a, In a l1 ->
                remove (eq_dec_form eq_dec_funcs eq_dec_preds) a (remove_list l1 l2) = remove_list l1 l2.
Proof.
induction l1.
- intros. inversion H.
- intros. simpl. inversion H.
  * subst. rewrite double_remove. reflexivity.
  * pose (IHl1 l2 a0 H0). rewrite permut_remove. rewrite e. reflexivity.
Qed.

Lemma In_matters_remove_list : forall l1 l2, (incl l1 l2 /\ incl l2 l1) -> (forall l0,
                                    remove_list l1 l0 = remove_list l2 l0).
Proof.
induction l1.
- intros. destruct H. destruct l2. auto. unfold incl in H0. pose (H0 f). assert (In f (f :: l2)).
  apply in_eq. apply i in H1. inversion H1.
- intros. destruct H. simpl. pose (H a). assert (In a (a :: l1)). apply in_eq. apply i in H1.
  apply in_split in H1. destruct H1. destruct H1. subst. destruct (In_dec l1 a).
  * rewrite In_remove_list_remove_redund. 2: assumption. apply IHl1. split. intro. intro.
    apply H. apply in_cons. assumption. intro. intro. apply H0 in H1. inversion H1. subst.
    assumption. assumption.
  * rewrite swap_remove_list. simpl. rewrite <- redund_remove_remove_list with (l1:=(x0 ++ x)).
    pose (IHl1 (remove (eq_dec_form eq_dec_funcs eq_dec_preds) a (x0 ++ x))). rewrite e.
    auto. split. intro. intro. apply in_not_touched_remove. assert (In a0 (a :: l1)). apply in_cons.
    assumption. apply H in H2. apply in_app_or in H2. destruct H2. apply in_or_app. right. assumption.
    inversion H2. subst. exfalso. apply f. assumption. apply in_or_app. left. assumption.
    intro. subst. apply f. assumption. intro. intro. pose (@In_remove_diff (x0 ++ x) _ _ H1).
    pose (@In_remove_In_list a0 a (x0 ++ x) H1). assert (In a0 (x ++ a :: x0)). apply in_app_or in i0.
    destruct i0. apply in_or_app. right. apply in_cons. assumption. apply in_or_app. left. assumption.
    apply H0 in H2. inversion H2. exfalso. apply n. symmetry. assumption. assumption.
Qed.

End Remove.
