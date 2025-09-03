Require Export FOL.FullSyntax.
Require Export Undecidability.FOL.Syntax.Theories.
Require Import FOL.ModelTheory.DCPre.
Require Import Undecidability.Synthetic.ListEnumerabilityFacts.
Require Export Vector.

Local Set Implicit Arguments.

Declare Scope modelNotation.
Open Scope modelNotation.

Notation vec := t.

(** * Definition of Model Theory *)

Section model.
    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.

    Structure model :=
    {
        domain : Type;
        interp' : interp domain
    }.

    Coercion domain : model >-> Sortclass.

End model.

Arguments eval {_ _}.
Arguments i_func {_ _} _ _ _ _.
Arguments i_atom {_ _} _ _ _ _.
Arguments sat {_ _ _ _ _} _ _, {_ _ _} _ {_} _ _.

(* A interface s.t. interp' can be used as interp *)
Arguments interp' {_ _} _, {_ _ _}.

(* Declare some notation that distinguishes the different models *)

    (* Evaluate function in model M with argument v
    func: Σ_funcs 
    M: model
    v: vec M (sys_ar func) 
        : M
    *)
    Notation "func ₕ[ M ] v" := (i_func _ (interp' M) func v) (at level 19).

    (* Evaluate predicate in model M with argument v
    pred: Σ_preds
    M: model
    v: vec M (sys_ar [pred]) 
        : Prop
    *)
    Notation "pred ₚ[ M ] v" := (i_atom _ (interp' M) pred v) (at level 19).

    (* Evaluate term in model M under environment env
    term: term
    M: model
    env: nat → M
        : Prop
    *)
    Notation "term ₜ[ M ] env" := (eval _ (interp' M) env term) (at level 19).

    (* 
        M : model
        phi: form
            : (nat -> M) -> Prop
        ∀ env, Model ⊨[env] formula
    *)
    Notation "Model ⊨[_] phi" := (forall p, sat (interp' Model) p phi) (at level 21).

    (* 
        M: model
        ρ: nat -> M
        phi: form
            : Prop
        Model ⊨[env] formula
    *)
    Notation "Model ⊨[ ρ ] phi" := (sat (interp' Model) ρ phi) (at level 21).


Section Elementary.
    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.
    Context {ff : falsity_flag}.

    Definition elementary_equivalence M N :=
        forall phi, closed phi -> (M ⊨[_] phi) <-> (N ⊨[_] phi).

    Definition elementary_homomorphism (M N: model) (h: M -> N) :=
        forall phi ρ, M ⊨[ρ] phi <-> N ⊨[ρ >> h] phi.

End Elementary.

Notation "M ≡ N"  := (elementary_equivalence M N) (at level 30).
Notation "N ⪳[ h ] M"  := (@elementary_homomorphism _ _ _ N M h) (at level 30).
Notation "N ⪳ M"  := (exists h: N -> M, N ⪳[ h ] M) (at level 30).


Section Countable_Sig.

    Context {Σf : funcs_signature} {Σp : preds_signature}.

    Definition countable_sig `{Σf: funcs_signature} `{Σp: preds_signature}: Type :=
        EnumerabilityFacts.enumerable__T Σf * EnumerabilityFacts.enumerable__T Σp *
        (forall x y : Σf, Dec.dec (x = y)) * (forall x y : Σp, Dec.dec (x = y)).
    
    Lemma enum_form: countable_sig -> exists (phi_: nat -> form) nth_, forall phi, phi_ (nth_ phi) = phi.
    Proof.
        intros [[[h1 h2] h3] h4].
        edestruct enumT_form' as [nth Hnth]; eauto.
        apply enumT_full_logic_sym. apply enumT_full_logic_quant.
        pose (nth_ := fun n => match nth n with | Some f => f | None => ⊥ end).
        unfold EnumerabilityFacts.enumerator__T' in Hnth.
        assert (forall x : form, exists n : nat, nth_ n = x) as P.
        { intro x. destruct (Hnth x) as [w Hw]. exists w. unfold nth_. now rewrite Hw. }
        assert (forall n x: form, {n = x} + {~ n = x}) as decForm.
        { apply dec_form; eauto. apply  dec_full_logic_sym. apply dec_full_logic_quant.  }
        assert (forall f, decider (fun n : nat => nth_ n = f) ) as decP.
        { intros x y. destruct (decForm x (nth_ y)); [now left | right; eauto]. } 
        specialize (fun f => (@W (fun n => nth_ n = f) (decP f) (P f))) as phi_.
        exists nth_, (fun f => pi1 (phi_ f)). intro φ.  
        destruct (phi_ φ). eauto. 
    Qed.
    
    Lemma enum_term: countable_sig -> exists (phi_: nat -> term) nth_, forall phi, phi_ (nth_ phi) = phi.
    Proof.
        intros [[[h1 h2] h3] h4].
        apply enum_enumT in h1. destruct h1 as [f Hf].
        edestruct enumT_term as [nth Hnth]; eauto. 
        pose (nth_ := fun n => match nth n with | Some f => f | None => $42 end).
        unfold EnumerabilityFacts.enumerator__T' in Hnth.
        assert (forall x : term, exists n : nat, nth_ n = x) as P.
        { intro x. destruct (Hnth x) as [w Hw]. exists w. unfold nth_. now rewrite Hw. }
        assert (forall n x: term, {n = x} + {~ n = x}) as decTerm.
        { apply dec_term; eauto. }
        assert (forall f, decider (fun n : nat => nth_ n = f) ) as decP.
        { intros x y. destruct (decTerm x (nth_ y)); [now left | right; eauto]. } 
        specialize (fun f => (@W (fun n => nth_ n = f) (decP f) (P f))) as phi_.
        exists nth_, (fun f => pi1 (phi_ f)). intro φ.  
        destruct (phi_ φ). eauto. 
    Qed.

    Definition coutable_model M := 
        exists (to_M: nat -> M) (of_M: M -> nat), forall m, to_M (of_M m) = m.

End Countable_Sig.

Section LöwenheimSkolemTheorem.

    Definition syntatic_model_on `{funcs_signature} `{preds_signature} (M: model) :=  
        exists (N: interp term) (h: term -> M), 
            forall φ ρ, Build_model N ⊨[ρ] φ <-> M ⊨[ρ >> h] φ.

    Definition LöwenheimSkolemTheorem_on `{funcs_signature} `{preds_signature} (M: model) :=
        exists N: model, coutable_model N /\ N ⪳ M.

    Definition SyntaticLS := 
        forall (Σ_f: funcs_signature) (Σ_p: preds_signature),
            countable_sig -> forall M: model, M -> syntatic_model_on M.

    Definition DLS := 
        forall (Σ_f: funcs_signature) (Σ_p: preds_signature),
            countable_sig -> forall M: model, M -> LöwenheimSkolemTheorem_on M.

    Fact LS_correct: SyntaticLS -> DLS.
    Proof.
        intros H Σ_f Σ_p Hc M m.
        destruct (H _ _ Hc M m) as (I & h & HI).
        unshelve eexists. { econstructor. exact I. }
        split. destruct enum_term as (psi_ & nth'_ & Hpsi); eauto.
        exists psi_, nth'_; eauto.
        exists h. intros ??; apply HI.
    Qed.

End LöwenheimSkolemTheorem.

(* Definition LS_root :=
    forall (Σ_f: funcs_signature) (Σ_p: preds_signature),
        forall (M: model), forall m,
            exists (N: model), coutable_model N /\ 
                (exists h: N -> M, N ⪳[h] M /\ exists n: N, h n = m).

Definition bijective_comp {X Y} :=
    exists f g, (forall x: X, g (f x) = x) /\ forall y: Y, f (g y) = y.

Definition LS_root' :=
    forall (Σf : funcs_signature) (Σp : preds_signature) (M: model), forall m,
        exists (N: model), @bijective_comp N nat /\ (exists h: N -> M, elementary_homomorphism h /\ exists n: N, h n = m).
 *)
