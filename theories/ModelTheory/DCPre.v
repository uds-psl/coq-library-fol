From Stdlib Require Import Arith Lia Nat PeanoNat ConstructiveEpsilon.
Require Export FOL.ModelTheory.LogicalPrinciples.

Notation "'Σt' x .. y , p" :=
    (sigT (fun x => .. (sigT (fun y => p)) ..))
        (at level 200, x binder, right associativity,
        format "'[' 'Σt'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Notation unique p := (forall x y, p x -> p y -> x = y).

Notation pi1 := projT1.

(** * Utils *)

Lemma W' (p : nat -> Prop) :
    decidable p -> ex p -> sig p.
Proof.
    intros H. apply constructive_indefinite_description_nat.
    intros n. destruct (H n); [now left | now right].
Qed.

Lemma W (p : nat -> Prop) :
    decidable p -> ex p -> sigT p.
Proof.
    intros H1 H2. destruct (W' H1 H2) as [n Hn]. now exists n.
Qed.


Section Least_witness.

    Definition nat_eqdec : eqdec nat.
    Proof.
        intros x y.
        destruct (Nat.eq_dec x y) as [H|H].
        - left. exact H.
        - right. exact H.
    Defined.

    Implicit Types (n k: nat).

    Definition safe (p: nat -> Prop) n := forall k, p k -> k >= n.
    Definition least (p: nat -> Prop) n := p n /\ safe p n.

    Fact least_unique (p: nat -> Prop) : unique (least p).
    Proof.
        intros x y [H1 H2] [H3 H4].
        enough (x <= y /\ y <= x) by lia. split.
        - apply H2, H3.
        - apply H4, H1.
    Qed.

    Fact safe_O p :
        safe p 0.
    Proof.
        intros k _. lia.
    Qed.

    Fact safe_S p n :
        safe p n -> ~p n -> safe p (S n).
    Proof.
        intros H1 H2 k H3.
        specialize (H1 k H3).
        enough (k <> n) by lia.
        intros ->. easy.
    Qed.

    Fact Logical_dec_safe (P: nat -> Prop):
        (forall n, P n \/ ~ P n) -> forall n, ex (least P) \/ safe P n.
    Proof.
        intros H n.
        induction n as [|n IH].
        - right. apply safe_O.
        - destruct IH as [IH|IH].
        + left. exact IH.
        + specialize (H n) as [H|H].
            * left. exists n. easy.
            * right. apply safe_S; assumption.
    Qed.

    Fact logical_dec_least (P: nat -> Prop):
        (forall n, P n \/ ~ P n) -> ex P -> ex (least P).
    Proof.
        intros H [y Py].
        destruct (@Logical_dec_safe _ H y) as [H'|H'].
        - easy.
        - exists y. split; easy.
    Qed.

End Least_witness.


Section DC_over_countable_set.

    Variable B: Type.
    Variable R:  B -> B -> Prop.
    Variable f: nat -> B.
    Hypothesis sur: forall n, exists m, f m = n.

    Lemma exists_next:
    (forall x, exists y, R x y) ->
        Σt f: nat -> B, forall b, exists n, R b (f n).
    Proof.
        intro total; exists f; intro b.
        destruct (total b) as [c Rbc], (sur c) as [m p].
        exists m. now rewrite p.
    Qed.

    Lemma DC_ω:
        (forall x y, dec (R x y)) -> (DC_root_on R).
    Proof.
        intros dec__R total root.
        destruct (exists_next total) as [h P].
        assert(forall b, decidable (fun n : nat => R b (h n))) as dec__R' by easy.
        specialize (fun b => (@W (fun n => R b (h n)) (dec__R' b) (P b))) as WO.
        exists (fix g n := match n with O => root | S n => h (pi1 (WO (g n))) end).
        split; try easy; intro n; cbn.
        destruct (WO ((fix g n:= match n with 0 => root |S n' => h (pi1 (WO (g n'))) end) n)); easy.
    Qed.

End DC_over_countable_set.

Section PDC_over_countable_set.

    Variable B: Type.
    Variable R:  B -> B -> Prop.
    Variable f: nat -> B.
    Variable g: B -> nat.
    Hypothesis bij_l: forall n, g (f n) = n.
    Hypothesis bij_r: forall b, f (g b) = b.
    Hypothesis logical_dec__R': forall x y, logical_dec (R x y).

    Fixpoint least_pred w n b :=
        match n with
        | O => b = w
        | S n => exists! bn, least_pred w n bn /\ least (fun x => R bn (f x)) (g b)
        end.

    Lemma exists_next_pred:
        (forall x, exists y, R x y) ->
            forall b, exists n, least (fun n => R b (f n)) n. 
    Proof.
        intros total__R b.
        destruct (total__R b) as [next Rbnext].
        apply logical_dec_least. {now intro n; specialize (logical_dec__R' b (f n)). }
        exists (g next).
        now rewrite bij_r.
    Qed.

    Lemma functional_least_pred root:
        (forall x, exists y, R x y) ->
            function_rel' (least_pred root).
    Proof.
        intros total__R n; induction n.
        - exists root; constructor; cbn; try easy.
        - destruct IHn as [v [p1 p2]].
        destruct (exists_next_pred total__R v) as [next Rrn].
        exists (f next); split; try easy; cbn.
        exists v; constructor; try easy. 
        split; try easy.
        now rewrite bij_l.
        intros v' [p _]; now apply p2.
        intros fnext' (p1' & p2' & p3).
        enough (g (f next) = g fnext').
        rewrite bij_l in H. rewrite H. easy.
        specialize(p3 p1' p2').
        unshelve eapply least_unique.
        exact (fun x : nat => R p1' (f x)).
        destruct p2' as [H1 H2].
        rewrite (p2 _ H1) in Rrn.
        now rewrite bij_l. easy.
    Qed.

    Lemma root_least_pred root: least_pred root O root.
    Proof.
        now intros.
    Qed.

    Lemma successor_least_pred root:
        (forall x, exists y, R x y) ->
            (forall n, exists x y, least_pred root n x /\ least_pred root (S n) y /\ R x y).
    Proof.
        intro total__R; induction n; cbn.
        - exists root.
        destruct (exists_next_pred total__R root) as [next Rrn].
        exists (f next); split; try easy; split.
        + rewrite bij_l; exists root; constructor; easy.
        + now destruct Rrn as (a_name & _).
        - destruct IHn as (x & y & nx & [bn [P1 P2]] & R'xy); exists y.
        destruct (exists_next_pred total__R y) as [next Rrn].
        exists (f next); split; try easy.
        exists bn; constructor; easy.
        split. 2: { now destruct Rrn. }
        exists y; constructor.
        split. exists bn; now constructor.
        now rewrite bij_l.
        intros y' ([b' [P1' P1'']] & P2').
        rewrite bij_l in P2'.
        enough (g y = g y'). { rewrite <- (bij_r y), <- (bij_r y'); now f_equal. }
        unshelve eapply least_unique.
        exact  (fun x : nat => R b' (f x)).
        destruct P1; destruct P1'.
        destruct (functional_least_pred root total__R n) as [x_n [_ uni_x]].
        enough (bn = b') as re. now rewrite <- re. 
        now rewrite <- (uni_x bn), <- (uni_x b').
        easy.
    Qed.

    Theorem DC_pred_ω: @PDC_root_on B R.
    Proof.
        intros total w.
        exists(least_pred w); split.
        - exact (functional_least_pred w total).
        - split; exact(root_least_pred w) + exact(successor_least_pred w total).
    Qed.

End PDC_over_countable_set.

Section StrongInduction.

    Definition strong_induction (p: nat -> Type) :
    (forall x, (forall y, y < x -> p y) -> p x) -> forall x, p x.
    Proof.
        intros H x; apply H.
        induction x; [intros; lia| ].
        intros; apply H; intros; apply IHx; lia.
    Defined.

End StrongInduction.

Tactic Notation "strong" "induction" ident(n) := induction n using strong_induction.

Section EO_choice.
    Definition even n := Σt m, n = 2 * m.
    Definition odd n := Σt m, n = 2 * m + 1.
    Definition EO_dec n : even n + odd n.
    Proof.
        induction n as [|n [H1|H1]]; [left; exists 0; lia|..].
        - right; destruct H1 as [k H]; exists k; lia.
        - left; destruct H1 as [k H]; exists (S k); lia.
    Defined.

    Lemma EO_false n: 
        (even n) * (odd n) -> False.
    Proof.
        intros ([k Pk] &[t Pt]); lia.
    Qed.

End EO_choice.













