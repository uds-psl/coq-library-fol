From Stdlib Require Import Arith.Cantor Arith.PeanoNat Lia Vector Arith.Compare_dec List.
Require Import Undecidability.Shared.Libs.PSL.Vectors.Vectors.
Import ListNotations.
Notation vec := t.
Notation "'Σ' x .. y , p" :=
    (sig (fun x => .. (sig (fun y => p)) ..))
    (at level 200, x binder, right associativity,
    format "'[' 'Σ'  '/  ' x  ..  y ,  '/  ' p ']'")
: type_scope.

Section property.

    Context {X Y: Type}.
    Variable R: X -> X -> Prop.
    Variable R_bi: X -> Y -> Prop.
    Variable R_tr: X -> X -> X -> Prop.

    Definition total := forall x, exists y, R_bi x y.
    Definition trans := forall x y z, R x y -> R y z -> R x z.
    Definition total_tr := forall x y, exists z, R_tr x y z.
    Definition direct := forall x y, exists z, R_bi x z /\ R_bi y z.


    Definition dec (X: Type) : Type := X + (X -> False).
    Definition logical_dec (X: Prop): Prop := X \/ (X -> False).
    
    Definition eqdec X := forall x y: X, dec (x = y).
    Definition function_rel' := forall x, exists! y, R_bi x y.

    Definition consf (f: Y -> X) := fun x y => R (f x) (f y).

End property.

Notation decidable p := (forall x, dec (p x)).
Notation logical_decidable p := (forall x, logical_dec (p x)).
Notation decider p := (forall x, dec (p x)).
Notation "R ∘ f" := (consf R f) (at level 30).

(** * Standard and Blurred Logical Principles *)

Section axiom.

    Implicit Type (X: Type).

    Definition DC_on X :=
        forall (R: X -> X -> Prop) , total R ->
            exists f: nat -> X, forall n, R (f n) (f (S n)).

    Definition DC_on' {X} (R: X -> X -> Prop) :=
        total R ->
            exists f: nat -> X, forall n, R (f n) (f (S n)).

    Definition DC_root_on X (R: X -> X -> Prop) := 
        total R -> forall x: X,
            exists f: nat -> X, f 0 = x /\ forall n, R (f n) (f (S n)).

    Definition BCC_on X := forall (R: nat -> X -> Prop),
        total R -> exists f: nat -> X, forall n, exists m, R n (f m).

    Definition BDC_on A := forall R : A -> A -> Prop, 
        (forall x, exists y, R x y) -> 
            exists f : nat -> A, total (R ∘ f).

    Definition BDC2_on X := forall R: X -> X -> X -> Prop,
        total_tr R -> 
            exists f: nat -> X, forall x y, exists z, R (f x) (f y) (f z).

    Definition OBDC_on X := forall R: X -> X -> X -> Prop,
        exists f: nat -> X, 
            total_tr R <-> forall x y, exists z, R (f x) (f y) (f z).

    Definition CC_on X := forall R: nat -> X -> Prop,
        total R -> exists f: nat -> X, forall n, R n (f n).

    Definition BDP_on X := forall (P: X -> Prop),
        exists f: nat -> X,
            (forall n, P (f n)) -> (forall x, P x).

    Definition BEP_on X := forall (P: X -> Prop),
        exists f: nat -> X,
            (exists x, P x) -> (exists n, P (f n)).

    Definition DDC_on X := forall (R: X -> X -> Prop),
        trans R -> direct R ->
            exists f: nat -> X, direct (R ∘ f).

    Definition DC__Δ := 
        forall X (R: X -> X -> Prop), (forall x y, dec (R x y)) -> X -> DC_on' R.

    Definition PDC_root_on X (R: X -> X -> Prop) :=
        (forall x, exists y, R x y) -> forall w,
            exists f : nat -> X -> Prop, function_rel' f /\ f 0 w /\ forall n, exists x y, f n x /\ f (S n) y /\ R x y.

    Definition OAC_on X Y :=
        forall (R : X -> Y -> Prop), exists f, total R -> forall x, R x (f x).

    Definition AC_on A B := forall (R : A -> B -> Prop), total R -> exists f : A -> B, forall x, R x (f x).

    Definition DC := forall X, X -> DC_on X.
    Definition DC_root := forall X (R: X -> X -> Prop), DC_root_on R.
    Definition PDC_root := forall X (R: X -> X -> Prop), PDC_root_on R.
    Definition BCC := forall X, X -> BCC_on X.
    Definition BDC := forall X, X -> BDC_on X.
    Definition BDC2 := forall X, X -> BDC2_on X.
    Definition OBDC := forall X, X -> OBDC_on X.
    Definition CC := forall X, X -> CC_on X.
    Definition CC_nat := CC_on nat.
    Definition BDP := forall X, X -> BDP_on X.
    Definition BEP := forall X, X -> BEP_on X.
    Definition DDC := forall X, X -> DDC_on X.
    Definition OAC := forall X Y, X -> Y -> OAC_on X Y.
    Definition AC  := forall X Y, X -> Y -> AC_on X Y.

End axiom.

Section BDC_BCC.

Definition BDC_root:=
  forall A (R : A -> A -> Prop), 
        forall a: A, (forall x, exists y, R x y) ->
            exists f : nat -> A, f 0 = a /\ forall x, exists y, R (f x) (f y).

Inductive reachable {X} (R : X -> X -> Prop) x0 x : Prop :=
    | base : R x0 x -> reachable R x0 x
    | step y : reachable R x0 y -> R y x -> reachable R x0 x.

Definition reachable' {X} (R : X -> X -> Prop) x0 x :=
    exists f : nat -> X, exists N, f 0 = x0 /\ f (S N) = x /\ forall n, n <= N -> R (f n) (f (S n)).
    

Lemma reach_reach' {X} (R : X -> X -> Prop) x0 x :
    reachable R x0 x -> reachable' R x0 x.
Proof.
    induction 1.
    - exists (fun n => match n with 0 => x0 | _ => x end), 0. split; trivial. split; trivial.
        intros n. inversion 1; subst. apply H.
    - destruct IHreachable as (f & N & H1 & H2 & H3).
        exists (fun n => if PeanoNat.Nat.leb n (S N) then f n else x), (S N). split. 2: split.
        + rewrite Compare_dec.leb_correct; try lia. apply H1.
        + rewrite Compare_dec.leb_correct_conv; try lia. reflexivity.
        + intros n HN. assert (n <= N \/ n = S N) as [Hn| ->] by lia.
        * rewrite ?Compare_dec.leb_correct; try lia. now apply H3.
        * rewrite Compare_dec.leb_correct, Compare_dec.leb_correct_conv; try lia. now rewrite H2.
Qed.

Lemma BDC_impl_BDC_root:
    BDC -> BDC_root .
Proof.
    intros dc A R w total_R.
    destruct (total_R w) as [y0 Hy0]. 
    pose (a0 := exist _ y0 (@base _ R _ _ Hy0)).
    assert ({ x | reachable R w x }) as inst. easy.
    destruct (dc { x | reachable R w x } inst (fun a b => R (proj1_sig a) (proj1_sig b)) ) as [f Hf].
    - intros [x Hx]. destruct (total_R x) as [y Hy]. exists (exist _ y (@step _ R w y x Hx Hy)). apply Hy.
    - destruct (f 0) as [x Hx] eqn : H0.
      destruct (@reach_reach' _ _ _ _ Hx) as (g & N & H1 & H2 & H3).
      exists (fun n => if PeanoNat.Nat.leb n N then g n else proj1_sig (f (n - N - 1))). split.
      + cbn. apply H1.
      + intros n. assert (n <= N \/ n > N) as [Hn|Hn] by lia.
        * assert (S n <= N \/ n = N) as [Hn'| ->] by lia. 
          -- exists (S n). rewrite ?Compare_dec.leb_correct; try lia. now apply H3.
          -- exists (S N). rewrite Compare_dec.leb_correct, Compare_dec.leb_correct_conv; try lia.
             assert (S N - N - 1 = 0) as -> by lia. rewrite H0. cbn. rewrite <- H2. apply H3. auto.
        * rewrite ?Compare_dec.leb_correct_conv; try lia.
        destruct (Hf  (n - N - 1)).
        exists (x0 + N + 1). 
        rewrite ?Compare_dec.leb_correct_conv; try lia.
        assert (x0 + N + 1 - N - 1 = x0) by lia. 
        rewrite H4.
        apply H.
Qed.

Theorem BDC_root_impl_BCC:
    BDC_root -> BCC.
Proof.
    intros DC A a' R H0.
    set (R' (p q:nat*A) := fst q = S (fst p) /\ R (fst p) (snd q)).
    destruct (H0 0) as (y0,Hy0).
    destruct (DC (prod nat A) ) with(R:=R') (a := (0, y0)) as (f,(Hf0,HfS)).
    - intros (n, a). destruct (H0 n) as [w Hw].
      exists (S n, w); easy.
    - assert (forall n, exists w, fst (f w) = n).
      + induction n.
      exists 0. now rewrite Hf0.
      destruct IHn as [w Hw].
      destruct (HfS w) as [y Hy].
      exists y. unfold R' in Hy.
      rewrite Hw in Hy.
      now destruct Hy.
      +  exists (fun n => snd (f n)).
      intro n'.
      destruct (H n') as [nw Hnw].
      specialize HfS with nw as [ny Hny].
      exists ny. 
      destruct Hny.
      now rewrite Hnw in H2.
Qed.

Theorem BDC_impl_BCC: BDC -> BCC.
Proof.
    intros ?; apply BDC_root_impl_BCC.
    now apply BDC_impl_BDC_root.
Qed.


End BDC_BCC.


Section incl.

    Definition incl_f {X} (f1 f2: nat -> X) := forall n, exists m, f1 n = f2 m.

End incl.

Notation "f1 ⊆ f2" := (incl_f f1 f2) (at level 30).

Section incl_fact.

    Definition trans_incl {X: Type} (f1 f2 f3: nat -> X) :
        f1 ⊆ f2 -> f2 ⊆ f3 -> f1 ⊆ f3.
    Proof.
        intros h1 h2 x.
        destruct (h1 x) as [y Hy].
        destruct (h2 y) as [z Hz].
        exists z; congruence.
    Qed.

End incl_fact.

Section merge.

    Definition even n := {m | n = 2 * m}.
    Definition odd n  := {m | n = 2 * m + 1}.
    Definition even_odd_dec n : even n + odd n.
    Proof.
        induction n as [|n [H1|H1]]; [left; exists 0; lia|..].
        - right; destruct H1 as [k H]; exists k; lia.
        - left; destruct H1 as [k H]; exists (S k); lia.
    Defined.

    Definition merge {X} (f1 f2: nat -> X): nat -> X :=
        fun n => match even_odd_dec n with 
            | inl L => f1 (proj1_sig L)
            | inr R => f2 (proj1_sig R)
        end.

End merge.

Notation "'to_merge_l' x" := (2 * x) (at level 30).
Notation "'to_merge_r' x" := (2 * x + 1) (at level 30).
Notation "f1 ∪ f2" := (merge f1 f2) (at level 34).

Section merge_fact.

    Context {X: Type}.
    Context (f1 f2 f3: nat -> X).

    Lemma union_eval_l x : (f1 ∪ f2) (to_merge_l x) = f1 x.
    Proof.
        unfold "∪"; destruct (even_odd_dec (to_merge_l x)).
        - destruct e; cbn; f_equal; nia.
        - destruct o. nia.
    Qed.

    Lemma union_eval_r x : (f1 ∪ f2) (to_merge_r x) = f2 x.
    Proof.
        unfold "∪"; destruct (even_odd_dec (to_merge_r x)).
        - destruct e. nia.
        - destruct o; cbn; f_equal; nia.
    Qed.

    Lemma union_incl_l : f1 ⊆ (f1 ∪ f2).
    Proof. now intros x; exists (to_merge_l x); rewrite union_eval_l. Qed.

    Lemma union_incl_r : f2 ⊆ (f1 ∪ f2).
    Proof. now intros x; exists (to_merge_r x); rewrite union_eval_r. Qed.

End merge_fact.


Section BCC_DDC_impl_BDC2.

    Section inner_mode.
(* Hypotheis we have *)
    Hypothesis BCC: BCC.
    Hypothesis DDC: DDC.

(* Promise by BDC2 *)
    Variable X: Type.
    Variable R: X -> X -> X -> Prop.
    Variable total_R: total_tr R.

(* Skolem relation *)
    Definition F (f1 f2: nat -> X) :=
        (forall n m, exists k, R (f1 n) (f1 m) (f2 k)) /\ (f1 ⊆ f2).

    Notation "f1 ⇒ f2" := (F f1 f2) (at level 29).

    Theorem trans_F: trans F.
    Proof.
        intros f1 f2 f3 [H1 H1'] [H2 H2']; split.
        - intros n m. destruct (H1 n m) as [w Hw].
          destruct (H2' w) as [ww Hww].
          exists ww; now rewrite <- Hww.
        - intros x; destruct (H1' x) as [y Hy]; destruct (H2' y) as [w Hw].
          exists w; congruence.
    Qed.

    Theorem total_F: total F.
    Proof using BCC total_R.
        intros f1.
        assert (forall n m, exists x, R (f1 n) (f1 m) x).
        firstorder.
        pose (R' n x := let '(n1, n2) := of_nat n in R (f1 n1) (f1 n2) x).
        destruct (@BCC X (f1 42) R') as [f2 Hf2]. 
        { intros n; unfold R'; destruct (of_nat n); firstorder. }
        exists (f1 ∪ f2); split; [intros n m|].
        destruct (Hf2 (to_nat (n, m))) as [w Hw].
        exists (to_merge_r w); rewrite union_eval_r.  
        now unfold R' in Hw; rewrite cancel_of_to in Hw.
        apply union_incl_l.
    Qed.

    Theorem direct_F: direct F.
    Proof.
        intros f1 f2.
        destruct (total_F f1) as [f1' [Hf1 Hf1']], (total_F f2) as [f2' [Hf2 Hf2']].
        exists (f1' ∪ f2'); repeat split.
        - intros n m; destruct (Hf1 n m) as [k Hk].
          now exists (to_merge_l k); rewrite union_eval_l.
        - eapply trans_incl; [exact Hf1' | eapply union_incl_l].
        - intros n m; destruct (Hf2 n m) as [k Hk].
          now exists (to_merge_r k); rewrite union_eval_r.
        - eapply trans_incl; [exact Hf2' | eapply union_incl_r].
    Qed.

        Section inner_mode_by_direct_T.

        (* By DDC, there is a direct countable set *)
        Variable T: nat -> (nat -> X).
        Hypothesis direct_T: direct (F ∘ T).

        Definition f x := let '(n, m) := of_nat x in T n m.

        Fact eq_co_domain_f : f ⊆ f.
        Proof.
            now intros x; exists x.
        Qed.

        Lemma bounded_f:
            forall x y: nat, exists k a b, T k a = (f x) /\ T k b = (f y).
        Proof.
            intros x y; unfold f; 
            destruct (of_nat x) as [x1 x2], (of_nat y) as [y1 y2].
            destruct (direct_T x1 y1) as [w [[_ Hxw] [_ Hyw]]].
            destruct (Hxw x2) as [x3 Hx3], (Hyw y2) as [y3 Hy3].
            now exists w, x3, y3.
        Qed.

        Fact fixpoint_F: F f f.
        Proof.
            split; [intros n m| apply eq_co_domain_f].
            destruct (bounded_f n m) as [k (a & b & <- & <-)].
            destruct (direct_T k k) as [Sk [[Hk _] _]].
            destruct (Hk a b) as [w Hw].
            exists (to_nat (Sk, w)).
            now unfold f; rewrite cancel_of_to.
        Qed.

        End inner_mode_by_direct_T.

    Fact res: X -> exists f: nat -> X, (forall x y, exists z, R (f x) (f y) (f z)).
    Proof using DDC BCC total_R.
        intros x; edestruct (@DDC _  (fun _ => x) F trans_F direct_F) as [T HT].
        exists (f T).
        now apply fixpoint_F.
    Qed.

    End inner_mode.

    Theorem res_BDC2: BCC -> DDC -> BDC2.
    Proof.
        intros BCC ddc X R x H.
        apply res; auto.
    Qed.

End BCC_DDC_impl_BDC2.


Section BDC2_impl_BCC_DDC.

    Lemma BDC2_impl_BDC_on A: BDC2_on A -> BDC_on A.
    Proof.
        intros H R Rtot.
        destruct (H (fun x _ z => R x z)) as [f Hf].
        { intros ? _; cbn. now eapply Rtot. }
        exists f. intros ?; eapply Hf.
        exact 42.
    Qed.

    Lemma BDC2_impl_BDC: BDC2 -> BDC.
    Proof. intros H A a. apply BDC2_impl_BDC_on. eauto. Qed.

    Lemma BDC2_impl_DDC: BDC2 -> DDC.
    Proof.
        intros H X x R _ Rd.
        destruct (H X x (fun x y z => R x z /\ R y z)) as [f Hf].
        { intros a b; eapply Rd. }
        eexists f. intros a b.
        eapply Hf.
    Qed.



End BDC2_impl_BCC_DDC.


Section OBDC_implies_BDP_BEP_BDC2.

    Lemma OBDC_impl_BDP_on (A: Type): OBDC_on A -> BDP_on A.
    Proof.
        intros H P.
        pose (R (x y z: A) := P x).
        destruct (H R) as [f [_ Hf]].
        exists f; intros Hdp y.
        assert (forall x y, exists z, R (f x) (f y) (f z)) as H1.
        { intros ? ?; exists 42; unfold R; apply Hdp. }
        destruct (Hf H1 y y) as [? HP].
        now unfold R in HP.
    Qed.

    Lemma OBDC_impl_BEP_on (A: Type): OBDC_on A -> BEP_on A.
    Proof.
        intros H P.
        pose (R (x y z: A) := P z).
        destruct (H R) as [f [Hf _]].
        exists f; intros Hdp.
        assert (forall x y, exists z, R x y z) as H1.
        { intros ? ?. unfold R. apply Hdp. }
        specialize (Hf H1 42 42). now unfold R in Hf.
    Qed.

    Lemma OBDC_impl_BDC2_on (X: Type): OBDC_on X -> BDC2_on X.
    Proof.
        intros H R Htot.
        destruct (H R) as [f Hf].
        rewrite Hf in Htot.
        exists f. apply Htot.
    Qed.
    

End OBDC_implies_BDP_BEP_BDC2.

Section DC_impl_DDC_BCC.

    Lemma DC_impl_DDC: DC -> DDC.
    Proof.
        intros DC A a R Tr H.
        destruct (DC A a R) as [f Hf].
        { intro x; destruct (H x x) as [z [Hz _]]; exists z; auto. }
        assert (forall x y, x < y -> R (f x) (f y)) as mono.
        { intros i j E.
          destruct (j - i) eqn:E'. lia.
          assert (j = i + S n) as -> by lia.
          induction n in i |-*. 
          rewrite Nat.add_1_r. apply Hf.
          eapply Tr. apply IHn. 
          rewrite !Nat.add_succ_r. apply Hf. }
          exists f; intros n m; exists (S (Nat.max n m)).
          split; apply mono; lia.
    Qed.

    Lemma DC_impl_BDC: DC -> BDC.
    Proof.
        intros H X R x Rtot.
        destruct (H X R x Rtot) as [f Hf].
        exists f. intros k. exists (S k).
        now apply Hf.
    Qed.

    Definition iter (n:nat) {A} (f:A->A) (x:A) : A :=
        nat_rect (fun _ => A) x (fun _ => f) n.

    Theorem BDC_CC_nat_impl_DC:
        BDC -> CC_nat -> DC.
    Proof.
        intros BDC CC_nat A a R tR. 
        destruct (BDC A a R tR) as [f Hf].
        destruct (CC_nat (fun n m => R (f n) (f m)) Hf) as [g Hg].
        exists (fun n => f (iter n (fun n => g n) 0)).
        intro n; cbn.
        now destruct (Hf ((iter n (fun n : nat => g n) 0))) as [[] Hg'].
    Qed.

    Lemma DC_impl_DC_root :
        DC -> DC_root.
    Proof.
        intros H X R HR x0.
        destruct (HR x0) as [y0 Hy0]. pose (a0 := exist _ y0 (@base _ R _ _ Hy0)).
        destruct (H { x | reachable R x0 x } a0 (fun a b => R (proj1_sig a) (proj1_sig b))) as [f Hf].
        -  intros [x Hx]. destruct (HR x) as [y Hy]. exists (exist _ y (@step _ R x0 y x Hx Hy)). apply Hy.
        - destruct (f 0) as [x Hx] eqn : H0.
            destruct (@reach_reach' _ _ _ _ Hx) as (g & N & H1 & H2 & H3).
            exists (fun n => if PeanoNat.Nat.leb n N then g n else proj1_sig (f (n - N - 1))). split.
            + cbn. apply H1.
            + intros n. assert (n <= N \/ n > N) as [Hn|Hn] by lia.
            * assert (S n <= N \/ n = N) as [Hn'| ->] by lia. 
                -- rewrite ?Compare_dec.leb_correct; try lia. now apply H3.
                -- rewrite Compare_dec.leb_correct, Compare_dec.leb_correct_conv; try lia.
                assert (S N - N - 1 = 0) as -> by lia. rewrite H0. cbn. rewrite <- H2. apply H3. auto.
            * rewrite ?Compare_dec.leb_correct_conv; try lia.
                assert (S n - N - 1 = S (n - N - 1)) as -> by lia. apply Hf.
    Qed.

    Lemma total_list {X Y} {R : X -> Y -> Prop} L :
        (forall x, exists y, R x y) -> exists L', Forall2 R L L'.
      Proof.
        intros HTot. induction L as [ | x L [L' IH]].
        - exists []. econstructor.
        - destruct (HTot x) as [y H]. exists (y :: L').
          now econstructor.
      Qed.

    Lemma AC_impl_DC: AC -> DC.
    Proof.
      intros ac X x R HR. destruct (ac _  _ x x R HR) as [f Hf].
      exists (fun n => iter n f x). intros n. apply Hf.
    Qed.

    Theorem DC_impl_CC: DC_root -> CC.
    Proof.
    intros dc A a R HR.
    destruct (HR 0) as [a0 HA].
    unshelve edestruct (dc (prod nat A) (fun p q => fst q = S (fst p) /\ R (fst p) (snd q))) as [f H].
    - exact (0, a0). 
    - intros []. cbn. destruct (HR n) as [a' HA']. exists (S n, a'). cbn. tauto.
    - assert (HF : forall n, fst (f n) = n).
        { induction n. now rewrite (proj1 H). rewrite <- IHn at 2. apply H. }
        exists (fun n => snd (f (S n))). intros n. rewrite <- (HF n) at 1. apply H.
    Qed.

    Theorem CC_impl_BCC: CC -> BCC.
    Proof.
        intros H A R a Htot.
        destruct (H A R a Htot) as [f Hf].
        eexists f; intro n; exists n.
        eauto.
    Qed.


    Theorem CC_impl_CC_nat: CC -> CC_nat.
    Proof.
        intros H; apply H. exact 42.
    Qed.

    Lemma CC_iff_BCC_CC_nat: CC <-> BCC /\ CC_nat.
    Proof.
        split.
        - intros CC; split; [apply CC_impl_BCC| apply CC_impl_CC_nat]; easy.
        - intros [bcc CC_nat] A a R totalR.
          destruct (bcc A a R totalR) as [f Pf].
          unfold CC_on in CC_nat.
          destruct (CC_nat (fun x y => R x (f y))) as [g Pg]. 
          { intros x; apply Pf. }
         now exists (fun n => f (g n)).
    Qed.

End DC_impl_DDC_BCC.

Section LBDC_VBDC.

    Definition VBDC:=
        forall (A: Type) (R: forall {n}, vec A n -> A -> Prop), 
            A -> (forall n (v: vec A n), exists w, R v w) ->
            (exists f: nat -> A, forall n (v: vec nat n), exists m, R (Vector.map f v) (f m)).

    Definition LBDC :=
        forall (A: Type) (R: list A -> A -> Prop), 
            (forall (v: list A), exists w, R v w) ->
            (exists f: nat -> A, forall (v: list nat), exists m, R (map f v) (f m)).

    Fact any_length_sig n : Σ l: list nat, length l = n.
    Proof.
        exists ((fix f n := match n with | O => nil | S n => 0 :: (f n) end) n).
        induction n; try easy; cbn.
        now rewrite IHn.
    Qed.

    Fact LBDC_impl_BCC: LBDC -> BCC.
    Proof.
        intros BDC_list A a R total_R.
        pose (R' (l: list A) (a: A) := R (length l) (a)).
        destruct (BDC_list _ R') as [g Hg].
        - intro v; exact (total_R (length v)).
        - exists g. intro n.
          destruct (@any_length_sig n).
          destruct (Hg x) as [w Hw].
          exists w. unfold R' in Hw.
          now rewrite length_map, e in Hw.
    Qed.
    Fact to_map_of_eq_map {A B} (v: list A) (g: A -> B) : to_list (Vector.map g (of_list v)) = map g v.
    Proof.
        rewrite to_list_map.
        now rewrite to_list_of_list_opp.
    Qed.

    Fact length_map_to_list {A B n} (v: vec A n) (g: A -> B): length (map g (to_list v)) = n.
    Proof.
        rewrite length_map.
        now rewrite length_to_list.
    Qed.
    
    Lemma vec_list_map X Y n (v : Vector.t X n) (g : X -> Y) (H : n = length (map g (to_list v))) :
        of_list (map g (to_list v)) = cast (Vector.map g v) H.
    Proof.
        induction v; cbn; trivial. now rewrite <- IHv.
    Qed.
    
    Lemma cast_refl X n (v : Vector.t X n) :
        cast v (Logic.eq_refl) = v. 
    Proof.
        induction v; cbn; trivial. now rewrite IHv.
    Qed.
    
    Lemma vec_list_map' X Y n (P : forall n, Vector.t Y n -> Prop) (v : Vector.t X n) (g : X -> Y) :
        P (length (map g (to_list v))) (of_list (map g (to_list v))) <-> P n (Vector.map g v).
    Proof.
        assert (H : n = length (map g (to_list v))).
        - now rewrite length_map, length_to_list.
        - unshelve erewrite vec_list_map; try apply H.
        destruct H. now rewrite cast_refl.
    Qed.
    
    Lemma vec_list_map'' X Y n (P : forall n, Vector.t Y n -> Y -> Prop) (v : Vector.t X n) (g : X -> Y) w :
        P (length (map g (to_list v))) (of_list (map g (to_list v))) w <-> P n (Vector.map g v) w.
    Proof.
        assert (H : n = length (map g (to_list v))).
        - now rewrite length_map, length_to_list.
        - unshelve erewrite vec_list_map; try apply H.
        destruct H. now rewrite cast_refl.
    Qed.

    Fact LBDC_iff_VBDC: VBDC <-> LBDC .
    Proof.
    split.
    - intros BDC A R totalR.
        pose (R' n (l: vec A n) (a: A) := R (to_list l) a).
        destruct (totalR nil) as [a _].
        destruct (BDC _ R' a) as [g Hg].
        intros n v; exact (totalR (to_list v)).
        exists g; intro v. 
        destruct (Hg _ (of_list v)) as [w Hw]; exists w.
        unfold R' in Hw.
        now rewrite <- to_map_of_eq_map.
    - intros BDC_list A R a totalR.
        pose (R' (l: list A) (a: A) := R (length l) (of_list l) a).
        destruct (BDC_list _ R') as [g Hg].
        intro v; exact (totalR _ (of_list v)).
        exists g.  intros n v. 
        destruct (Hg (to_list v)) as [w Hw].
        unfold R' in Hw. exists w. revert Hw.
        now rewrite (vec_list_map'' R).
    Qed.

    Lemma LBDC_impl_BDC2: LBDC -> BDC2.
    Proof.
        intros ldc A a R HR.
        pose (R' := fun l y => match l with | a::b::_ => R a b y | _ => True end).
        destruct (ldc _ R') as [f Hf].
        - intros [|x [|y l]]; cbn; try now exists a.
          now destruct (HR x y) as [w Hw]; exists w.
        - exists f. intros n m. 
          destruct (Hf (n::m::nil) ) as [w Hw].
          now exists w.
    Qed.


End LBDC_VBDC.



Section Result.

    Theorem OBDC_impl_BDP_BEP_on (A: Type):
        OBDC_on A -> BDC2_on A /\ BDP_on A /\ BEP_on A.
    Proof.
        intros H; split;
        [now apply OBDC_impl_BDC2_on|now split; [apply OBDC_impl_BDP_on| apply OBDC_impl_BEP_on]].
    Qed.

    Theorem BDC2_iff_DDC_BCC:
        BDC2 <-> (DDC /\ BCC).
    Proof.
        split.
        - intros H; split. 
            now apply BDC2_impl_DDC.
            now apply BDC_impl_BCC, BDC2_impl_BDC.
        - intros [H1 H2]. now apply res_BDC2.
    Qed.

    Theorem DC_iff_BDC_CC_nat: 
        DC <-> BDC /\ CC_nat.
    Proof.
        split; intros H.
        - split; [now apply DC_impl_BDC |now apply CC_impl_CC_nat, DC_impl_CC, DC_impl_DC_root].
        - now destruct H; apply BDC_CC_nat_impl_DC; [|easy].
    Qed.

    Theorem DC_impl_BDC2: 
        DC -> BDC2.
    Proof.
          intro H. rewrite BDC2_iff_DDC_BCC; split.
          now apply DC_impl_DDC.
          now apply CC_impl_BCC, DC_impl_CC, DC_impl_DC_root.
    Qed.
    

    Theorem DC_iff_BDC2_CC_nat:
        DC <-> BDC2 /\ CC_nat.
    Proof.
        split.
        - intros H; split.
          rewrite BDC2_iff_DDC_BCC; split.
          now apply DC_impl_DDC.
          now apply CC_impl_BCC, DC_impl_CC, DC_impl_DC_root.
          now apply CC_impl_CC_nat, DC_impl_CC, DC_impl_DC_root.
        - intros [H1 H2]. rewrite DC_iff_BDC_CC_nat; split; [|easy].
          now apply BDC2_impl_BDC.
    Qed.


    Theorem DC_iff_DDC_CC:
        DC <-> DDC /\ CC.
    Proof.
        split.
        - intros H; split.
        now apply DC_impl_DDC.
        now apply DC_impl_CC, DC_impl_DC_root.
        - intros [H1 H2]. rewrite DC_iff_BDC_CC_nat; split.
        specialize (CC_impl_BCC H2) as H3.
        apply BDC2_impl_BDC. now rewrite BDC2_iff_DDC_BCC.
        now apply CC_impl_CC_nat.  
    Qed.

    Fact CC_impl_BCC_on (A: Type): CC_on A -> BCC_on A.
    Proof.
        intros H R Htot.
        destruct (H R Htot) as [f Hf].
        eexists f; intro n; exists n.
        eauto.
    Qed.

    Fact DC_impl_BDC_on (A: Type): DC_on A -> BDC_on A.
    Proof.
        intros H R Htot.
        destruct (H R Htot) as [f Hf].
        exists f; intros x; exists (S x).
        unfold consf; eauto.
    Qed.


End Result.

Section DP_EP.

    Definition DP_on (X: Type) := forall P: X -> Prop, 
        exists x, P x -> (forall x, P x).

    Definition EP_on (X: Type) := forall P: X -> Prop,
        exists x, (exists x, P x) -> P x.

End DP_EP.

Section BDP_BEP_scheme.

    Definition BDP_scheme (domain range: Type) :=
        forall P: domain -> Prop, exists f: range -> domain,
            (forall n: range, P (f n)) -> forall x, P x.

    Definition BEP_scheme (domain range: Type) :=
        forall P: domain -> Prop, exists f: range -> domain,
            (exists x, P x) -> (exists m, P (f m)).

End BDP_BEP_scheme.

Notation BDP_to A := (forall domain, domain -> @BDP_scheme domain A).
Notation BEP_to A := (forall domain, domain -> @BEP_scheme domain A).

Notation BDP' := (@BDP_to nat).
Notation BEP' := (@BEP_to nat).

Notation DP := (@BDP_to unit).
Notation EP := (@BEP_to unit).

Notation BDP₁ := (@BDP_scheme nat unit).
Notation BEP₁ := (@BEP_scheme nat unit).

Section scheme_facts_basic.

    Fact scheme_facts_basic11: forall A, BDP_scheme A A.
    Proof. intros A P. exists (fun n => n). eauto. Qed. 

    Fact scheme_facts_basic12: forall A, BEP_scheme A A.
    Proof. intros A P. exists (fun n => n). eauto. Qed.

    Fact scheme_facts_basic2: forall A B C, 
            BDP_scheme A B -> BDP_scheme B C -> BDP_scheme A C.
    Proof. intros A B C H1 H2.
           intros P . destruct (H1 P) as [f Hf].
           destruct (H2 (fun n => P (f n))) as [h Hh].
           exists (fun a => f (h a)). firstorder.
    Qed.

    Fact scheme_facts_basic3: forall A B C, 
            BEP_scheme A B -> BEP_scheme B C -> BEP_scheme A C.
    Proof. intros A B C H1 H2.
        intros P. destruct (H1 P) as [f Hf].
        destruct (H2 (fun n => P (f n))) as [h Hh].
        exists (fun a => f (h a)). firstorder.
    Qed.



    Fact scheme_facts_basic41: forall A B, inhabited B -> BDP_scheme A unit -> BDP_scheme A B.
    Proof.
        intros A B [b] H P.
        destruct (H P) as [f Hf].
        exists (fun _ => f tt). 
        intros. apply Hf. intros []. now apply H0.
    Qed.

    Fact scheme_facts_basic42 A: BDP_scheme A unit <-> DP_on A.
    Proof.
        split; intros H P.
        - destruct (H P); try easy.
            exists (x tt); intro h.
            apply H0. now intros [].
        - destruct (H P); try easy.
            exists (fun _ => x).
            intros; apply H0, H1. exact tt.
    Qed.

    Fact scheme_facts_basic51: forall A B, inhabited B -> BEP_scheme A unit -> BEP_scheme A B.
    Proof.
        intros A B [b] H P.
        destruct (H P) as [f Hf].
        exists (fun _ => f tt).
        intros. apply Hf in H0. exists b. now destruct H0 as [[] H0].
    Qed.

    Fact scheme_facts_basic52 A: BEP_scheme A unit <-> EP_on A.
    Proof.
        split; intros H P.
        - destruct (H P); try easy.
            exists (x tt); intro h.
            destruct H0 as [[] Pu]; easy. 
        -  destruct (H  P); try easy.
            exists (fun _ => x).
            intros. exists tt. now apply H0, H1.
    Qed.
    
End scheme_facts_basic.

Section scheme_facts_1.

    Definition WPFP := (forall b: nat -> bool, exists a: nat -> bool, (exists n, b n = false) <-> (forall n, a n = true)).
    Definition LEM := (forall P, P \/ ~ P).
    Definition LPO := (forall f : nat -> bool, (forall x, f x = false) \/ (exists x, f x = true)).
    Definition IP_on A := forall (P:A -> Prop) (Q:Prop), (Q -> exists x, P x) -> exists x, Q -> P x.
    Definition IP := forall A, inhabited A -> IP_on A.
    Definition BIP_on (A:Type) (B: Type) := forall (P:A -> Prop) (Q:Prop),(Q -> exists x, P x) -> exists (f: B -> A), Q -> (exists m, P (f m)).
    Definition BIP := forall (A:Type) (P:A -> Prop) (Q:Prop),  inhabited A -> BIP_on A nat.
    Definition KS := forall P, exists f : nat -> bool, P <-> exists n, f n = true.
    Definition KS' :=   forall P : Prop, exists f : nat -> bool, (P -> ~ forall n, f n = false) /\ ((exists n, f n = true) -> P).
    Definition ODC := forall X (R: X -> X -> Prop) , X -> exists f: nat -> X, total R -> forall n, R (f n) (f (S n)).

    Lemma BDP_impl_KS':
        BDP -> KS'.
    Proof.
        intros dp P.
        destruct (dp (option P) None (fun x => match x with Some x => ~ P | _ => True end)) as [f H].
        exists (fun n => if f n then true else false). split.
        - intros HP. intros H'. refine (H _ (Some HP) HP).
          intros n. specialize (H' n). destruct f; try discriminate. exact I.
        - intros [n Hn]. destruct (f n); try tauto. discriminate.
      Qed.

    Lemma BEP_KS :
        BEP -> KS.
    Proof.
        intros dp P.
        destruct (dp (option P) None (fun x => match x with Some x => P | _ => False end)) as [f H].
        exists (fun n => if f n then true else false). split.
        - intros HP. destruct H as [n Hn].
            + exists (Some HP). apply HP.
            + exists n. destruct (f n); tauto.
        - intros [n Hn]. destruct (f n); try discriminate. exact p.
    Qed.

End scheme_facts_1.

Section scheme_facts_2.
    Fact DP_is_DP: 
        DP <-> (forall A (P: A -> Prop), A -> exists x, P x -> forall x, P x).
    Proof.
        split; intros.
        - destruct (H A X P); try easy.
            exists (x tt); intro h.
            apply H0. now intros [].
        - intros P. destruct (H domain P); try easy.
            exists (fun _ => x).
            intros; apply H0, H1. exact tt.
    Qed.

    Fact EP_is_EP: 
        EP <-> (forall A (P : A -> Prop), A -> exists x, (exists x, P x) -> P x).
    Proof.
        split; intros.
        - destruct (H A X P); try easy.
            exists (x tt); intro h.
            destruct H0 as [[] Pu]; easy. 
        - intros P. destruct (H domain P); try easy.
            exists (fun _ => x).
            intros. exists tt. now apply H0, H1.
    Qed.

    Lemma DP_impl_LEM : DP -> LEM.
    Proof.
        intros dp P.
        rewrite DP_is_DP in dp.
        destruct (dp (option (P \/ ~ P)) (fun x => match x with Some x => ~ P | _ => True end) None) as [[x|] H].
        - exact x.
        - right. intros HP. now apply (H I (Some (or_introl HP))).
    Qed.

    Lemma DP_iff_LEM : DP <-> LEM.
    Proof.
        split. apply DP_impl_LEM.
        intros H X x P.
        destruct (H (exists x, ~ P x)) as [L|R].
        - destruct L as [w Pw].
          exists (fun _ => w). intros Px. 
          specialize (Px tt). exfalso. easy.
        - exists (fun _ => x). intros _ w.
          destruct (H (P w)); [easy|].
          exfalso. apply R. now exists w.
    Qed.

    Fact BDP_BDP₁_iff_DP: BDP /\ BDP₁ <-> DP.
    Proof.
        split.
        - intros [H1 H2] X x P.
          destruct (H1 _ x P) as [f Hf].
          destruct (H2 (fun n => P (f n))) as [f' Hf'].
          exists (fun n => f (f' tt)).
          intros. apply Hf. intros. apply Hf'.
          intros []. apply H. exact tt.
        - intros H; split; [|apply H].
          intros X x P. destruct (H X x P) as [f Hf].
          exists (fun n => f tt). intros.
          apply Hf. intros []. apply H0. all: exact 42.
    Qed.

    Lemma BDP_BDP₁_iff_LEM: (BDP /\ BDP₁) <-> LEM.
    Proof.
        split.
        - intro H. rewrite BDP_BDP₁_iff_DP in H.
          now apply DP_impl_LEM.
        - intros H. rewrite BDP_BDP₁_iff_DP.
          now rewrite DP_iff_LEM.
    Qed.

    Lemma EP_impl_LEM : EP -> LEM.
    Proof.
        intros dp P.
        rewrite EP_is_EP in dp.
        destruct 
        (dp (option (P \/ ~ P))  (fun x => match x with  |Some x => P  | _ => False end)  None) as [[x|] H].
        - exact x.
        - right. intros HP. apply H. exists (Some (or_introl HP)). exact HP.
    Qed.

    Lemma EP_iff_LEM: EP <-> LEM.
    Proof.
        split. apply EP_impl_LEM.
        intros H X x P.
        destruct (H (exists x, P x)) as [[w Pw]|R].
        - exists (fun _ => w). intros _. now exists tt. 
        - exists (fun _ => x). intros [w Pw].
          exfalso. apply R. now exists w.
    Qed.
    

    Fact BEP_BEP₁_iff_EP: BEP /\ BEP₁ <-> EP.
    Proof.
        split.
        - intros [H1 H2] X x P .
            destruct (H1 _ x P) as [f Hf].
            destruct (H2 (fun n => P (f n))) as [f' Hf'].
            exists (fun n => f (f' tt)).
            intros. apply Hf, Hf' in H. destruct H as [[] Hk].
            now exists tt.
        - intros H; split; [|apply H].
            intros X P x. destruct (H X P x) as [f Hf].
            exists (fun n => f tt). intros.
            apply Hf in H0. destruct H0 as [[] H0].
            now exists 42. exact 42.
    Qed.

    Lemma BEP_BEP₁_iff_LEM: (BEP /\ BEP₁) <-> LEM.
    Proof.
        split.
        - intro H. rewrite BEP_BEP₁_iff_EP in H.
            now apply EP_impl_LEM.
        - intros H. rewrite BEP_BEP₁_iff_EP.
            now rewrite EP_iff_LEM.
    Qed.

    Definition MP :=
        forall f : nat -> bool, ~ ~ (exists n, f n = true) -> exists n, f n = true.

    Definition DN := forall P, ~ ~ P -> P.

    Lemma BDP_MP_impl_LEM :
        BDP -> MP -> LEM.
    Proof.
        intros dp mp P.
        destruct (dp (option (P \/ ~ P)) None (fun x => match x with Some x => ~ (P \/ ~ P) | _ => True end)) as [f H].
        destruct (mp (fun n => if f n then true else false)) as [n Hn].
        - intros H'. assert (H1 : ~ ~ (P \/ ~ P)) by tauto. apply H1. intros H2.
            refine (H _ (Some H2) H2). intros n. destruct f eqn: Hf; try exact I.
            contradict H'. exists n. now rewrite Hf.
        - destruct (f n); try tauto. discriminate.
    Qed.

    Fact LEM_iff_DN: LEM <-> DN.
    Proof.
        split.
        intros H P H1. specialize (H P) as [H|H].
        exact H. contradict (H1 H).
        intros H P. apply H.
        intros H1. apply H1.
        right. intro p. apply H1.
        now left.
    Qed.

    Lemma BDP_MP_iff_LEM: 
        (BDP /\ MP) <-> LEM.
    Proof.
        split; [intros [h1 h2]; now apply BDP_MP_impl_LEM|].
        intros; split.
        - rewrite <- DP_iff_LEM in H.
          intros X x P. destruct (H X x P) as [f Hf].
          exists (fun _ => f tt); intros HI; apply Hf.
          intros []. apply HI; exact 42.
        - intros P H'. rewrite LEM_iff_DN in H.
          now apply H.
    Qed.


    Lemma BEP_MP_impl_DN :
        BEP -> MP -> DN.
    Proof.
        intros dp mp P HP.
        destruct (dp (option P) None (fun x => match x with Some x => P | _ => False end)) as [f H].
        destruct (mp (fun n => if f n then true else false)) as [x Hx].
        - intros H'. apply HP. intros HP'. apply H'. destruct H as [n Hn].
            + exists (Some HP'). apply HP'.
            + exists n. destruct (f n); tauto.
        - destruct (f x); try discriminate. exact p.
    Qed.

    Lemma BEP_MP_iff_LEM :
        (BEP /\ MP) <-> LEM.
    Proof.
        split; [intros [h1 h2]; rewrite LEM_iff_DN; now apply BEP_MP_impl_DN|].
        intros; split.
        - rewrite <- EP_iff_LEM in H.
            intros X x P. destruct (H X x P) as [f Hf].
            exists (fun _ => f tt). intros HI. exists 42.
            now destruct (Hf HI) as [[] ?].
        - intros P H'. rewrite LEM_iff_DN in H.
            now apply H.
    Qed.


    Lemma KS_LPO_LEM: KS -> LPO -> LEM.
    Proof.
        intros KS LPO P. 
        destruct (KS P) as [f Pf].
        destruct (LPO f) as [H|H].
        - right; intro p. 
            rewrite Pf in p.
            destruct p as [w Pw].
            specialize (H w).
            congruence.
        - left; now rewrite Pf.
    Qed.

    Lemma BDP_LPO_impl_LEM : BDP -> LPO -> LEM.
    Proof.
        intros dp lpo P.
        destruct (dp (option (P \/ ~ P)) None (fun x => match x with Some x => ~ P | _ => True end)) as [f H].
        destruct (lpo (fun n => if f n then true else false)) as [Hf|[x Hx]].
        - right. intros HP. refine (H _ (Some (or_introl HP)) HP).
            intros n. specialize (Hf n). destruct (f n); try discriminate. trivial.
        - destruct (f x); try discriminate. trivial.
    Qed.

    Lemma DP_nat_impl_LPO: DP_on nat -> LPO.
    Proof.
        intros dp f. 
        specialize (dp (fun n => f n = false)).
        destruct dp.
        destruct (f x) eqn: E.
        - right. now exists x.
        - left. now apply H.
    Qed.

    Lemma EP_nat_impl_LPO: EP_on nat -> LPO.
    Proof.
        intros H f. destruct (H (fun n => f n = true)) as [x Hx].
        destruct (f x) eqn: Hf.
        - right. now exists x.
        - left. intros n. destruct (f n) eqn: Hn; trivial.
          symmetry. apply Hx. now exists n.
    Qed.

    Fact EP_impl_IP: EP -> IP.
    Proof.
        intros.
        intros A [a] P Q HP.
        destruct (H A a P). 
        exists (x tt); intros Q'%HP.
        destruct H0 as [[] P']; easy.
    Qed.

    Fact IP_iff_EP: IP <-> EP.
    Proof.
        split; [|apply EP_impl_IP].
        intros IP A IA. intros P.
        destruct (IP A (inhabits IA) P (exists x, P x)).
        easy. exists (fun v => x).
        intros P'. exists tt. now apply H.
    Qed.

    Fact IP_iff_LEM: IP <-> LEM.
    Proof.
        rewrite IP_iff_EP.
        apply EP_iff_LEM.
    Qed.

    Lemma there_are_equivalent:
        (IP <-> LEM) /\ (EP <-> LEM) /\ (DP <-> LEM).
    Proof.
        split. apply IP_iff_LEM.
        split. apply EP_iff_LEM.
        apply DP_iff_LEM.
    Qed.
    

    Fact BEP_impl_BIP A B: BEP_scheme A B -> BIP_on A B.
    Proof.
        intros BDP' P Q  HP.
        destruct (BDP' P).
        exists x; intros Q'%HP.
        now apply H.
    Qed.
    
    Fact BIP_iff_BEP A B: BIP_on A B <-> BEP_scheme A B.
    Proof.
        split; [|apply BEP_impl_BIP].
        intros BIP P.
        destruct (BIP P (exists x, P x)).
        easy. now exists x.
    Qed.

    Fact DC_IP_implies_ODC: DC -> IP -> ODC.
    Proof.
        intros DC IP A R w.
        specialize (DC_impl_DC_root DC) as DC_r.
        apply IP. constructor; exact (fun _ => w).
        intros DC'%(DC A w R); eauto.
    Qed.

End scheme_facts_2.

Section AboutOAC.

    Lemma OAC_impl_AC_IP A B (x : A) :
        OAC_on A B -> AC_on A B /\ IP_on B.
    Proof.
        intros H. split.
        - intros R HR. destruct (H R) as [f Hf]. exists f. apply Hf, HR.
        - intros P Q H1. destruct (H (fun _ y => P y)) as [f Hf].
            exists (f x). intros HQ. apply Hf. intros _. apply H1, HQ.
    Qed.

    Lemma IP_AC_impl_OAC A B (y : B): 
        AC_on A B -> IP_on B -> OAC_on A B.
    Proof.
        intros H1 H2 R. destruct (H1 (fun x y => (exists y, R x y) -> R x y)) as [f Hf].
        - intros x. apply H2. easy. 
        - exists f. intros H. intros x. apply (Hf x (H x)).
    Qed.

End AboutOAC.
