Require Import FOL.ModelTheory.LogicalPrinciples.
Require Import FOL.ModelTheory.GeneralisedAxioms.
Local Set Implicit Arguments.

(* Separating blurred drinker paradoxes *)

Lemma BDP_DP_local :
  (forall A, BDP_on A -> DP_on A) -> LPO.
Proof.
  intros H. apply DP_nat_impl_LPO, H.
  intros P. exists (fun n => n). tauto.
Qed.

Definition worlds : Type :=
  option bool.

Definition acc (w w' : worlds) : Prop :=
  match w, w' with
  | None, _ => True
  | Some true, Some true => True
  | Some false, Some false => True
  | _, _ => False
  end.

Definition DP_heyting_on A :=
  forall P : A -> worlds -> Prop, (forall b w w', acc w w' -> P b w -> P b w')
    -> exists b, forall w : worlds, P b w -> forall w', acc w w' -> forall b', P b' w'.

Definition flip (b : bool) (w : worlds) : Prop :=
  match b, w with
  | true, Some true => True
  | false, Some false => True
  | _, _ => False
  end.

Lemma DP_heyting_unit :
  DP_heyting_on unit.
Proof.
  intros P HP. exists tt. intros w Hw w' Hw' []. now apply (HP tt w w').
Qed.

Lemma DP_heyting_bool :
  ~ DP_heyting_on bool.
Proof.
  intros H. destruct (H flip) as [[] H'].
  - intros [] [[]|] [[]|]; cbn; tauto.
  - apply (H' (Some true) I (Some true) I false).
  - apply (H' (Some false) I (Some false) I true).
Qed.

Lemma BDP_DP_bool :
  ~ (forall A, GenBDP_on bool A -> DP_heyting_on A).
Proof.
  intros H. apply DP_heyting_bool, H.
  intros P. exists (fun b => b). tauto.
Qed.

(* Separating blurred choice axioms *)

Lemma BCC_CC :
  (forall A, BCC_on A -> CC_on A) -> CC_on nat.
Proof.
  intros H. apply H. intros R HR. exists (fun n => n). apply HR.
Qed.

Lemma BCC_DCC :
  (BCC -> DDC) -> CC -> DC.
Proof.
  intros H cc. apply DC_iff_DDC_CC. split; trivial. apply H, CC_impl_BCC, cc.
Qed.

Lemma DC_BDP :
  (DC -> BDP) -> DC -> MP -> LEM.
Proof.
  intros H dc mp. apply BDP_MP_impl_LEM; try apply mp. apply H, dc.
Qed.

Definition UC_nat_nat :=
  forall (R : nat -> nat -> Prop), (forall n, exists! m, R n m)
    -> exists f : nat -> nat, forall n, R n (f n).

Lemma LEM_BCC :
  (LEM -> BCC) -> UC_nat_nat -> LEM -> CC.
Proof.
  intros H uc lem. apply CC_iff_BCC_CC_nat. split; try now apply H.
  intros R HR. destruct (uc (fun n m => R n m /\ ~ (exists k : nat, k < m /\ R n k))) as [f Hf].
  - intros n. destruct (HR n) as [m Hm]. induction (Wf_nat.lt_wf m) as [m _ IH].
    destruct (lem (exists k, k < m /\ R n k)) as [[y [H1 H2]]|H'].
    + now apply (IH y).
    + exists m. split; try now split.
      intros l [H3 H4]. destruct (PeanoNat.Nat.lt_total m l) as [Hl|[Hl|Hl]]; trivial.
      * contradict H4. now exists m.
      * contradict H'. now exists l.
  - exists f. intros n. apply Hf.
Qed.


