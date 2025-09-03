From Coq Require Import Arith Lia Nat PeanoNat.
Require Export FOL.ModelTheory.LogicalPrinciples.

Notation "'Σ' x .. y , p" :=
    (sigT (fun x => .. (sigT (fun y => p)) ..))
        (at level 200, x binder, right associativity,
        format "'[' 'Σ'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Notation unique p := (forall x y, p x -> p y -> x = y).
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.

(** * Utils *)

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

    Definition XM := forall P, P \/ ~P.

    Fact xm_least_safe :
    XM -> forall p n, ex (least p) \/ safe p n.
    Proof.
    intros H p.
    induction n as [|n IH].
    - right. apply safe_O.
    - destruct IH as [IH|IH].
        + left. exact IH.
        + specialize (H (p n)) as [H|H].
        * left. exists n. easy.
        * right. apply safe_S; assumption.
    Qed.

    Fact least_safe_ex_least :
    (forall p n, ex (least p) \/ safe p n) -> forall p, ex p -> ex (least p).
    Proof.
    intros H p [n H1].
    specialize (H p n) as [H|H].
    * exact H.
    * exists n. easy.
    Qed.

    Fact XM_ex_least:
        XM -> forall p, ex p -> ex (least p).
    Proof.
        intro; now apply least_safe_ex_least, xm_least_safe.
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

Section WO.

    Implicit Types n k: nat.
    Variable p: nat -> Prop.
    Variable p_dec: decidable p.

    Inductive T (n: nat) : Prop := C (phi: ~p n -> T (S n)).

    Lemma T_base n :
        p n -> T n.
    Proof.
        intros H. constructor. intros H1. destruct (H1 H).
    Qed.

    Lemma T_step n :
        T (S n) -> T n.
    Proof.
        intros H. constructor. intros _. exact H.
    Qed.

    Lemma T_zero n :
        T n -> T 0.
    Proof.
        induction n as [|n IH].
        auto. intros H. apply IH. apply T_step, H.
    Qed.

    Lemma V n :
        p n -> T 0.
    Proof.
        intros H. eapply T_zero, T_base, H.
    Qed.

    Lemma W' :
        forall n, T n -> sig p.
    Proof.
        refine (fix F n a {struct a} := let (phi) := a in
                            match p_dec n with
                            inl H => _ | inr H => _
                            end).
        exact (Sig p n H). exact (F (S n) (phi H)).
    Qed.

    Theorem W :
        ex p -> sig p.
    Proof.
        intros H. apply W' with 0.
        destruct H as [n H]. apply V with n, H.
    Qed.

End WO.

Section DC_over_countable_set.

    Variable B: Type.
    Variable R:  B -> B -> Prop.
    Variable f: nat -> B.
    Hypothesis sur: forall n, exists m, f m = n.

    Lemma exists_next:
    (forall x, exists y, R x y) ->
        Σ f: nat -> B, forall b, exists n, R b (f n).
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
    
    About Vectors.vector_to_list_length.

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

Section Cantor.

    Definition next a : nat * nat :=
        match a with
        | (0,y) => (S y, 0)
        | (S x, y) => (x, S y)
        end.

    Fixpoint decode n : nat * nat :=
        match n with
        | 0 => (0,0)
        | S n' => next (decode n')
        end.

    Fixpoint sum n : nat :=
        match n with
        | 0 => 0
        | S n' => S n' + sum n'
        end.

    Definition encode_p '(x, y) : nat :=
        sum (x + y) + y.

    Fact encode_next a :
        encode_p (next a) = S (encode_p a).
    Proof.
        destruct a as [[|x] y]; cbn -[sum].
        - rewrite !Nat.add_0_r. rewrite Nat.add_comm. reflexivity.
        - assert (forall x y, x + S y = S (x + y)) by lia.
        rewrite !H. reflexivity.
    Qed.

    Opaque encode_p. 

    Fact encode_decode n :
        encode_p (decode n) = n.
    Proof.
    induction n as [|n IH]; cbn.
    - reflexivity.
    - rewrite encode_next, IH. reflexivity.
    Qed.

    Fact decode_encode a :
        decode (encode_p a) = a.
    Proof.
    revert a.
    enough (forall n a, encode_p a = n -> decode n = a) by eauto.
    induction n as [|n IH]; intros [x y]; cbn.
    - destruct x, y; cbn [encode_p]; cbn; easy.
    - destruct y.
        + destruct x.
        * discriminate.
        * change (S x, 0) with (next (0,x)).
            rewrite encode_next.
            intros [= <-].
            f_equal. apply IH. reflexivity.
        + change (x, S y) with (next (S x, y)). 
        rewrite encode_next.
        intros [= <-].
        f_equal. apply IH. reflexivity.
    Qed.

    Definition encode a b := encode_p (a, b).
    Definition π__1 x := fst (decode x).
    Definition π__2 x := snd (decode x).

    Lemma cantor_paring: forall x, encode (π__1 x) (π__2 x) = x.
    Proof.
        intro x; unfold encode, π__1, π__2.
        rewrite <- (surjective_pairing (decode x)).
        now rewrite encode_decode.
    Qed.

    Lemma cantor_left: forall x y, π__1 (encode x y) = x.
    Proof.
        intros x y; unfold encode, π__1.
        now rewrite decode_encode.
    Qed.

    Definition cantor_right: forall x y, (π__2 (encode x y)) = y.
    Proof.
        intros x y; unfold encode, π__2.
        now rewrite decode_encode.
    Qed.

End Cantor.

Section EO_choice.

    Definition even n := Σ m, n = 2 * m.
    Definition odd n := Σ m, n = 2 * m + 1.
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












