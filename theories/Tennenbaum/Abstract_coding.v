Require Import Lia.

From FOL.Tennenbaum Require Import DN_Utils.

Section Coding.

(** We want to capture more abstractly what is needed for the coding
  theorem to hold. Originally we used divisibility for numbers, but we
  can more generally assume that there is some binary predicate satisfying
  the following two axioms.
*)
Variable In : nat -> nat -> Prop.

Notation "u ∈ c" := (In u c) (at level 45).

Hypothesis H_empty     : exists e, forall x, ~ x ∈ e.
Hypothesis H_extend  : forall n c, exists c', forall x, x ∈ c' <-> x = n \/ x ∈ c.


(** We can now prove that this binary relation can be used for encoding predicates.
 *)
Lemma bounded_coding p n :
  (forall x, x < n -> p x \/ ~ p x) ->
  exists c, forall u, (u < n -> (p u <-> u ∈ c)) /\ (u ∈ c -> u < n).
Proof.
  assert (forall u n, u < S n -> u < n \/ u = n) as E by lia.
  induction n.
  { intros. destruct H_empty as [e He]. 
    exists e. intros u. split; [lia|]. intros []%He. }
  intros Dec_p.
  destruct IHn as [c Hc], (Dec_p n ltac:(lia)) as [pn|pn'].
  1, 2: intros; apply Dec_p; lia.
  - destruct (H_extend n c) as [c' Hc']. exists c'.
    intros u. split.
    + intros [| ->]%E. split.
      * intros p_u%Hc; auto. apply Hc'; auto.
      * intros [->|]%Hc'; auto. now apply Hc.
      * split; eauto. intros _. apply Hc'; auto.
    + intros [->|H%Hc]%Hc'; auto.
  - exists c.
    intros u; split.
    + intros [| ->]%E; [now apply Hc|].
        split; [now intros ?%pn'|].
        intros H%Hc. lia.
    + intros H%Hc. lia.
Qed.

Lemma DN_bounded_lem p n :
  ~ ~ (forall x, x < n -> p x \/ ~ p x).
Proof.
  induction n as [|n IH].
  { DN.ret. lia. }
  DN.lem (p n). intros Hn.
  DN.bind IH. DN.ret. intros x Hx.
  assert (x < n \/ x = n) as [| ->] by lia.
  all: auto.
Qed.

Corollary DN_coding p n :
  ~~ exists c, forall u, (u < n -> (p u <-> u ∈ c)) /\ (u ∈ c -> u < n).
Proof.
  eapply DN.bind_.
  - apply DN_bounded_lem.
  - intro. apply DN.ret_, (bounded_coding p n); eauto.
Qed.


End Coding.
