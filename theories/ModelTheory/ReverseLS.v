Require Import Undecidability.FOL.Syntax.BinSig.
Require Import Coq.Logic.EqdepFacts Coq.Logic.FinFun.
Require Import FOL.ModelTheory.DCPre.
Require Import FOL.ModelTheory.Core.
Require Import Program.Equality Vectors.VectorDef.
Require Import Coq.Arith.Peano_dec.

(** * Reverse Analysis of DLS *)

Section LSBDPBEP.

    Existing Instance sig_empty.
    Existing Instance sig_binary.

    Instance sig_unary : preds_signature | 0 :=
        {| preds := unit;  ar_preds := fun _ => 1 |}.

    Fact Unary_countable: countable_sig.
    Proof.
        repeat split.
        - exists (fun _ => None); intros [].
        - exists (fun _ => Some tt). intros []. now exists 42.
        - intros []. - intros [] []. now left.
    Qed.

    Instance interp__U (A: Type) (P: A -> Prop): interp A :=
        {
            i_func := fun F v => match F return A with end;
            i_atom := fun P' v => P (hd v)
        }.

    Definition model__U (A: Type) (P: A -> Prop): model := 
        {|
            domain := A;
            interp' := (@interp__U A P)
        |}.

    Lemma LS_impl_BEP: DLS -> BEP.
    Proof.
        intros LS A a P. destruct (LS _ _ Unary_countable (model__U P) a) as [i_N [ (phi_ & nth_ & Hphi) [h emb]]].
        exists (fun n => h (phi_ n)).
        specialize (emb (∃ (atom tt) (cons _ ($0) 0 (nil _))) phi_) as emb'; cbn in emb'.
        intro H'. destruct emb' as [H1 [t Ht]].
        exact H'. exists (nth_ t). rewrite Hphi.
        specialize (emb ((atom tt) (cons _ ($0) 0 (nil _))) (fun n => t)) ; cbn in emb.
        unfold ">>" in emb. now rewrite <- emb.
    Qed.

    Lemma LS_impl_BDP: DLS -> BDP.
    Proof.
        intros LS A a P.  destruct (LS _ _ Unary_countable (model__U P) a) as [i_N [ (phi_ & nth_ & Hphi) [h emb]]].
        exists (fun n => h (phi_ n)).
        specialize (emb (∀ (atom tt) (cons _ ($0) 0 (nil _))) phi_) as emb'; cbn in emb'.
        intro H'; apply emb'. intro d.
        specialize (emb ((atom tt) (cons _ ($0) 0 (nil _))) (fun n => d) ); cbn in emb.
        rewrite emb; unfold ">>". specialize (H' (nth_ d)).
        now rewrite Hphi in H'.
    Qed.

End LSBDPBEP.

Section LS_implies_BDC.

    Section proof_env.

    Existing Instance sig_empty.
    Existing Instance sig_binary.

    Fact Binary_countable: countable_sig.
    Proof.
        repeat split.
        - exists (fun _ => None); intros [].
        - exists (fun _ => Some tt). intros []. now exists 42.
        - intros []. - intros [] []. now left.
    Qed.

        Variable B: Type.
        Variable R: B -> B  -> Prop.

        Instance interp__B' : interp B :=
        {
            i_func := fun F v => match F return B with end;
            i_atom := fun P v => R (hd v) (hd (tl v))
        }.

        Definition Model__B': model :=
        {|
            domain := B;
            interp' := interp__B'
        |}.

        Import VectorNotations.

        Definition tuple' := [($1); ($0)].
        Definition coding_totality' := ∀ ∃ (atom tt tuple').

        Lemma total_coding':
            inhabited B -> (forall x, exists z, R x z) <-> Model__B' ⊨[_] coding_totality'.
        Proof.
            intros [b]; cbn; split; intros; eauto.
            destruct (H (fun _ => b) x); eauto.
        Qed.

        Definition BDC_on' X (R: X -> X -> Prop) :=
            X -> total R -> 
                exists f: nat -> X, forall x, exists z, R (f x) (f z).

        Lemma impl_BDC:  DLS -> inhabited B -> BDC_on' R.
        Proof.
            intros HLS [b]. destruct (HLS _ _ Binary_countable Model__B' b) as [N [(phi_ & nth_ & Hphi) [h Hh]]].
            intros b' Ht. exists (fun x => h (phi_ x)).
            specialize (Hh coding_totality') as Hh1. cbn in Hh1.
            rewrite <-  Hh1 in Ht; [| exact (fun _ => phi_ 42)]. 
            specialize (Hh (atom tt tuple')) as Hh0.
            cbn in Hh0.
            intros x. destruct (Ht (phi_ x)) as [w Hw].
            pose (ρ n := match n with O => w | _ => phi_ x end).
            specialize (Hh0 ρ); cbn in Hh0.
            rewrite Hh0 in Hw. exists (nth_ w). rewrite Hphi.
            unfold ">>" in Hw. easy.
        Qed.

    End proof_env.

    Theorem LS_impl_BDC: DLS -> BDC.
    Proof.
        intros H X x R; eapply impl_BDC; eauto.
    Qed.

    Theorem LS_CC_impl_DC: CC_nat -> DLS -> DC.
    Proof.
        intros H1 H2%LS_impl_BDC. 
        apply BDC_CC_nat_impl_DC; eauto.
    Qed.

End LS_implies_BDC.

Section LS_implies_OBDC.

    Instance sig_B : preds_signature | 0 := {| preds := unit;  ar_preds := fun _ => 3 |}.

    Existing Instance sig_empty.
    
    Fact Tri_countable: countable_sig.
    Proof.
        repeat split.
        - exists (fun _ => None); intros [].
        - exists (fun _ => Some tt). intros []. now exists 42.
        - intros []. - intros [] []. now left.
    Qed.

    Variable B: Type.
    Variable R: B -> B -> B -> Prop.

    Instance interp__B : interp B :=
    {
        i_func := fun F v => match F return B with end;
        i_atom := fun P v => R (hd v) (hd (tl v)) (hd (tl (tl v)))
    }.

    Definition Model__B: model :=
    {|
        domain := B;
        interp' := interp__B
    |}.

    Import VectorNotations.

    Definition tuple := [($2); ($1); ($0)].
    Definition coding_totality := ∀ ∀ ∃ (atom tt tuple).

    Lemma total_coding:
        inhabited B -> (forall x y, exists z, R x y z) <-> Model__B ⊨[_] coding_totality.
    Proof.
        intros [b]; cbn; split; intros; eauto.
        destruct (H (fun _ => b) x y); eauto.
    Qed.

    Definition OBDC_on' X (R: X -> X -> X -> Prop) :=
        X -> exists f: nat -> X, 
            total_tr R <-> forall x y, exists z, R (f x) (f y) (f z).

    Lemma impl_OBDC: DLS -> OBDC_on' R.
    Proof.
        intros HLS b. destruct (HLS _ _ Tri_countable Model__B b) as [N [(phi_ & nth_ & Hphi) [h Hh]]].
        exists (fun x => h (phi_ x)).
        specialize (Hh coding_totality) as Hh1. cbn in Hh1.
        rewrite <-  Hh1; [| exact phi_].
        specialize (Hh (atom tt tuple)) as Hh0. cbn in Hh0.
        split.
        - intros. destruct (H (phi_ x) (phi_ y)) as [w Hw].
          pose (ρ n := match n with O => w | 1 => phi_ y | _ => phi_ x end).
          specialize (Hh0 ρ); cbn in Hh0. rewrite Hh0 in Hw.
          exists (nth_ w). unfold ">>" in Hw. cbn in Hw.
          now rewrite !Hphi. 
        - intros H d1 d2.
          destruct (H (nth_ d1) (nth_ d2)) as [w Hw]. rewrite !Hphi in Hw.
          exists (phi_ w). pose (ρ n := match n with O => phi_ w |1 => d2 |_ => d1 end).
          specialize (Hh0 ρ); cbn in Hh0.
          rewrite Hh0.
          now unfold ">>"; cbn.
    Qed.

End LS_implies_OBDC.

    Theorem LS_impl_OBDC: DLS -> OBDC.
    Proof.
        intros H X R x; eapply impl_OBDC; eauto.
    Qed.

(* 
Section LS_imples_BCC.

    Instance sig_A : preds_signature | 0 :=
        {| preds := nat;  ar_preds := fun _ => 1 |}.

    Fact ω_countable: countable_sig.
    Proof.
        repeat split.
        - exists (fun _ => None); intros [].
        - exists (fun n => Some n). intros n. now exists n.
        - intros [].  - intros n m. induction n in m |-*; destruct m.
          now left. now right. now right. 
          elim (IHn m); firstorder.
    Qed.

    Variable A: Type.
    Variable P: nat -> A -> Prop.
    Instance interp_A : interp A :=
    {
        i_func := fun F v => match F return A with end;
        i_atom := fun n v => P n (hd v)
    }.

    Definition model_A: model :=
    {|
        domain := A;
        interp' := interp_A
    |}.

    Definition BCC_on' (B: Type) (P': nat -> B -> Prop) :=
        B -> (forall x, exists y, P' x y) ->
            exists f: nat -> B, forall n, exists m, P' n (f m).

    Theorem impl_BCC: DLS -> @BCC_on' A P.
    Proof.
        
        intros HLS a total_R.
        destruct (HLS _ _ ω_countable model_A a) as [N [(phi_ & nth_ & Hphi) [h Hh]]].
        assert (forall n ρ, ρ ⊨ (∃ (atom _ _ _ _ n (cons _ ($0) _ (nil _))))).
        - cbn; intros; apply total_R.
        -  assert (forall m (ρ : env term), ρ ⊨ (∃ atom m (cons term $0 0 (nil term)))).
          + intro m; specialize (ele_el__h (∃ atom m (cons term $0 0 (nil term)))).
            intro rho; rewrite ele_el__h.
            cbn; apply total_R.
          + exists (fun n => h (phi_ n)).
            intro m; destruct (H0 m var) as [x Hx].
            exists (nth_ x).
            specialize (ele_el__h (atom m (cons term ($0) 0 (nil term))) (fun _ => x)).
            cbn in ele_el__h.
            rewrite Hphi.
            unfold ">>" in ele_el__h; rewrite <- ele_el__h.
            now cbn in Hx.
    Qed.

End LS_imples_BCC.

    Theorem LS_impl_BCC: LS -> BCC.
    Proof.
        intros H X R HR.
        eapply impl_BCC; eauto.
    Qed. *)

(* 
Section joint.

    Definition forall_times {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} {ff : falsity_flag} 
        n (phi : form) :=  iter (fun psi => ∀ psi) n phi.

    Fixpoint join_rev {X n} (v : t X n) (rho : nat -> X) :=
        match v with
        | Vector.nil _ => rho
        | Vector.cons _ x n w => join_rev w (x.:rho)
        end.

    Fixpoint join {X n} (v : t X n) (rho : nat -> X) :=
        match v with
        | Vector.nil _ => rho
        | Vector.cons _ x n w => x.:(join w rho)
        end.

End joint.

 Notation "v '∗' rho" := (join v rho) (at level 20).
 Notation "v '∗r' rho" := (join_rev v rho) (at level 20).

Section joint_facts.

    Fixpoint vec_snoc {X n} (v: vec X n) (x:X) : vec X (S n) := 
        match v with
        nil _ => cons _ x _ (nil _)
        | cons _ y _ v => cons _ y _ (vec_snoc v x) end.

    Fixpoint vec_rev {X n} (v: vec X n): vec X n := match v with
        | nil _ => nil _ 
        | cons _ x _ v => vec_snoc (vec_rev v) x
        end.

    Lemma vec_rev_snoc {X n} (v : vec X n) (x : X) :
        vec_rev (vec_snoc v x) = cons _ x _ (vec_rev v).
    Proof.
    induction v in x|-*.
    - easy.
    - cbn. rewrite IHv. cbn. reflexivity.
    Qed.

    Lemma rev_rev_eq {X n} (v: vec X n):
        vec_rev (vec_rev v) = v.
    Proof.
    induction v.
    - easy.
    - cbn. rewrite vec_rev_snoc, IHv. easy.
    Qed.

    Lemma joint_cons {A: Type} {n: nat} (v: vec A n) h rho: 
        v ∗ (h .: rho) =  (append v (cons _ h _ (nil _))) ∗ rho.
    Proof.
        induction v; cbn. { easy. }
        now rewrite IHv.
    Qed.

    Lemma snoc_joint {A: Type} {n: nat} (v: vec A n) h ρ:
        vec_snoc v h ∗ ρ = v ∗ (h .: ρ) .
    Proof.
        induction v. 
        - cbn. easy.
        - cbn. now rewrite IHv.
    Qed.

    Lemma snoc_joint_rev {A: Type} {n: nat} (v: vec A n) (h: A) ρ:
        (vec_snoc v h) ∗r ρ = (h .: (v ∗r ρ)).
    Proof.
        induction v in ρ |-*; cbn.
        - easy.
        - now rewrite IHv.
    Qed.
    
    Lemma forall_times_joint_rev `{ interp} n phi ρ:
        ρ ⊨ forall_times n phi <-> forall v : vec _ n, (v ∗r ρ) ⊨ phi.
    Proof.
        split.
        - intros Hp v; revert Hp; revert ρ. 
        dependent induction v; cbn. {easy. }
        + intros rho HI.
            specialize (HI h).
            now apply IHv in HI.
        - revert ρ; induction n; cbn.
        + intros ρ Hp; now specialize (Hp (nil _)).
        + intros ρ Hp d.
            apply IHn; intro v.
            now specialize (Hp (cons _ d _ v)).
    Qed.

    Lemma join_rev_join {A n} (v: vec A n) ρ: v ∗r ρ = vec_rev v ∗ ρ .
    Proof.
        dependent induction v.
        - cbn. easy.
        - cbn. rewrite IHv.
          now rewrite snoc_joint.
    Qed.

    Lemma join_join_rev {A n} (v: vec A n) ρ: (vec_rev v) ∗r ρ = v ∗ ρ .
    Proof.
        dependent induction v.
        - cbn. easy.
        - cbn. rewrite <- IHv.
          rewrite snoc_joint_rev.
          reflexivity.
    Qed.

    Definition append_joint_rev {X n} h (t: vec X n) ρ:
        append t (cons X h 0 (nil X)) ∗r ρ = (h .: t ∗r ρ).
    Proof.
        revert ρ; induction t; cbn. { easy. }
        intro ρ.  now rewrite IHt.
    Qed.

    Lemma lookup_join {A} m n (w : vec _ m) (ρ : nat  -> A) : 
        (w ∗ ρ) (m + n) = ρ n.
    Proof.
    induction w in ρ,n|-*.
    - cbn. easy.
    - cbn. apply IHw.
    Qed.

    Lemma lookup_join_comp {A B: Type} {n}  (h: A -> B) (v : vec A n) ρ p2 : 
        ((v ∗ ρ) >> h) (Fin2Restrict.f2n p2) = (nth (map h v) p2).
    Proof.
    induction p2 in v,ρ|-*.
    - cbn. dependent induction v; easy.
    - unfold FinFun.Fin2Restrict.f2n in *.
        dependent induction v.
        cbn. destruct (Fin.to_nat p2) as [p2n Hp2].
        cbn in *. apply IHp2.
    Qed.

    Lemma lookup_join_id X n (v : vec X n) ρ p2 : 
        (v ∗ ρ) (Fin2Restrict.f2n p2) = nth v p2.
    Proof.
        pose (lookup_join_comp (fun x => x) v ρ p2) as H.
        now rewrite !VectorSpec.map_id in H.
    Qed.

    Lemma forall_joint `{interp} n phi ρ:
        ρ ⊨ forall_times n phi <-> forall v : vec _ n, (v ∗ ρ) ⊨ phi.
    Proof.
        split; intros.
        - rewrite <- join_join_rev.
          now rewrite forall_times_joint_rev in H0.
        - rewrite forall_times_joint_rev.
          intros v.
          specialize (H0 (vec_rev v)).
          now rewrite join_rev_join.
    Qed.

End joint_facts. *)
(* 
Section VBDC.

    Variable A: Type.
    Variable R: forall {n}, vec A n -> A -> Prop.

    Instance sig_L : preds_signature | 0 :=
        {| preds := nat; ar_preds := fun n => S n |}.

    Fact v_counatble: countable_sig.
    Proof.
    repeat split.
    - exists (fun _ => None); intros [].
    - exists (fun n => Some n). intros n. now exists n.
    - intros [].  - intros n m. induction n in m |-*; destruct m.
        now left. now right. now right. 
        elim (IHn m); firstorder.
    Qed.

    Definition tl {A n} (v: vec A (S n)): vec A n :=
        match v with
        | cons _ _ _ w => w
        end.

    Definition hd {A n} (v: vec A (S n)): A :=
        match v with
        | cons _ x _ _ => x
        end.

    Instance interp__L : interp A :=
    {
        i_func := fun F v => match F return A with end;
        i_atom := fun n (v: vec A (S n)) => R  (tl v) (hd v)
    }.

    Fixpoint range {X} (f: nat -> X) (n m: nat)  :=
        match m with
        | 0 => nil _
        | S m => cons _ (f n) _ (range f (S n) m) 
        end.

    Lemma nth_var X m n p2 (f:nat -> X) : 
        (nth (range f m n) p2) = f (m + Fin2Restrict.f2n p2).
    Proof.
        induction p2 in m|-*.
        - cbn. f_equal. apply plus_n_O.
        - cbn. unfold FinFun.Fin2Restrict.f2n in *.
          cbn. destruct (Fin.to_nat p2) as [p2n Hp2]. cbn.
          specialize (IHp2 (S m)). cbn in *. rewrite plus_n_Sm in IHp2. easy.
    Qed.

    Lemma pick_up_v n m (w : vec _ m) v ρ :
        Vector.map (eval _ interp__L (w ∗ (v ∗ ρ))) (range var m n) = v.
    Proof.
        apply VectorSpec.eq_nth_iff. intros p1 p2 ->.
        erewrite nth_map. 2:reflexivity.
        rewrite nth_var. cbn.
        rewrite lookup_join.
        rewrite lookup_join_id. easy.
    Qed.

    Definition var_up n := range var 0 (S n).

    Notation "R[ N ]" := (atom N (var_up N)).
    Notation "∀⁺∃R[ N ]" := (forall_times N (∃ R[N])).

    Lemma coding {B} n m (v: vec B n) ρ (h: B -> A):
        ((m .: v ∗ ρ) >> h) ⊨ R[n] = R (map h v) (h m) .
    Proof.
        cbn; f_equal.
        apply VectorSpec.eq_nth_iff. intros p1 p2 ->.
        erewrite nth_map. 2:reflexivity.
        rewrite nth_var. cbn.
        change ((v ∗ ρ >> h) (Fin2Restrict.f2n p2) = nth (map h v) p2).
        rewrite lookup_join_comp. easy.
    Qed.

    Section under_LS.

    (* Consider a elementary countable model N of A *)

    Variable N: Type.
    Variable n_: nat -> N.
    Variable nth_: N -> nat.
    Hypothesis Ht: forall t, n_ (nth_ t) = t.

    Variable interp__N: interp N.
    Variable h: N -> A.
    Hypothesis el_N: forall φ (ρ: env N), ρ ⊨ φ <-> (ρ >> h) ⊨ φ.

    Hypothesis total_A: forall n (v: vec A n), exists w, R v w.

    Lemma M_sat_R n (ρ: env A):
        ρ ⊨ ∀⁺∃R[ n ].
    Proof.
        rewrite forall_joint; intro v.
        destruct (total_A v) as [w Hw].
        exists w. 
        specialize (@coding A n w v ρ (fun x => x)) as H.
        rewrite VectorSpec.map_id in H.
        rewrite <- H in Hw.
        revert Hw.
        now apply sat_ext; induction n.
    Qed.

    Lemma N_sat_R n (ρ: env N): 
        ρ ⊨ ∀⁺∃R[ n ].
    Proof.
        specialize (el_N ∀⁺∃R[ n ] ρ) as ->.
        apply M_sat_R.
    Qed.

    Lemma ex_N_sat_R {n} ρ (v: vec N n):
        exists m, (m.:( v ∗ ρ)) ⊨ R[n].
    Proof.
        specialize (N_sat_R n ρ) as H1'.
        rewrite forall_joint in H1'.
        now apply H1'.
    Qed.

    Lemma ex_A_sat_R {n} ρ (v: vec N n):
        exists m, ((m .: v ∗ ρ) >> h) ⊨ R[n].
    Proof.
        specialize (ex_N_sat_R ρ v) as [m Hm].
        exists m. now rewrite <- el_N.
    Qed.

    Lemma VBDC_under_LS:
        exists f: nat -> A, forall n (v: vec nat n), exists m, R (map f v) (f m).
    Proof.
        exists (fun n => h (n_ n)).
        intros n v.
        destruct (ex_A_sat_R (fun _ => (n_ 0)) (map n_ v)) as [m Hm].
        exists (nth_ m).
        rewrite Ht.
        rewrite coding in Hm.
        now rewrite map_map in Hm.
    Qed.

    End under_LS.

End VBDC. *)


(* Section LS_imples_BAC.

    Variable κ: Type.   
    Instance sig_κ : preds_signature | 0 :=
        {| preds := κ;  ar_preds := fun _ => 1 |}.
    Hypothesis LS: LS.

    Variable A: Type.
    Variable P: κ -> A -> Prop.

    Instance interp_κ : interp A :=
    {
        i_func := fun F v => match F return A with end;
        i_atom := fun n v => P n (hd v)
    }.

    Definition model_κ: model :=
    {|
        domain := A;
        interp' := interp_κ
    |}.

    Variable E_term: κ -> term. 
    Variable term_E: term -> κ. 
    Hypothesis E_Κ: forall w, E_term (term_E w) = w.

    Definition BAC_on Κ B (R: Κ -> B -> Prop) :=
        inhabited B -> (forall n, exists y, R n y) -> exists f : Κ -> B, forall n, exists w, R n (f w).

    Theorem LS_implies_WAC_κ:
        @BAC_on κ A P.
    Proof.
        intros [] total_R.
        assert (forall n ρ, ρ ⊨ (∃ (atom _ _ _ _ n (cons _ ($0) _ (nil _))))).
        - cbn; intros; apply total_R.
        - destruct (@LS model_κ) as [N [h ele_el__h] ]; eauto.
          assert ( forall (m: κ) (ρ : env term), ρ ⊨ (∃ atom m (cons term $0 0 (nil term)))).
          + intro m; specialize (ele_el__h (∃ atom m (cons term $0 0 (nil term)))).
            intro rho; rewrite ele_el__h.
            cbn; apply total_R.
          + exists (fun (n: κ) => h (E_term n)).
            intro m; destruct (H0 m var) as [x Hx].
            exists (term_E x).
            specialize (ele_el__h (atom m (cons term ($0) 0 (nil term))) (fun _ => x)).
            cbn in ele_el__h.
            rewrite E_Κ.
            unfold ">>" in ele_el__h; rewrite <- ele_el__h.
            now cbn in Hx.
    Qed.

End LS_imples_BAC. *)
