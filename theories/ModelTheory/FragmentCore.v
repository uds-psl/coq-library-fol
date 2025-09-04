(* Basic definition in model theory *)

Require Export FOL.FragmentSyntax.
Require Export Undecidability.FOL.Syntax.Theories.
Local Set Implicit Arguments.
(* Local Unset Strict Implicit. *)


(** * Definition of Model Theory (Negative Fragment) *)


Require Export Vector.

Local Set Implicit Arguments.

    Declare Scope modelNotation.
    Open Scope modelNotation.

    Notation vec := t.

    Section model.
        Context {Σ_funcs : funcs_signature}.
        Context {Σ_preds : preds_signature}.

        Record model := 
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


Section Isomorphism.
    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.

    Definition preserve_func {M N: model} (h: M -> N) := 
        forall func v,
            h (func ₕ[M] v) = func ₕ[N] (map h v).

    Definition preserve_pred {M N: model} (h: M -> N) :=
        forall pred v,
            pred ₚ[M] v -> pred ₚ[N] (map h v).

    Definition strong_preserve_pred {M N: model} (h: M -> N) :=
        forall pred v,
            pred ₚ[M] v <-> pred ₚ[N] (map h v).

    Definition injective {M N} (f: M -> N) :=
        forall n m, f n = f m -> n = m.

    Definition surjective {M N} (f: M -> N) :=
        forall n: N, exists m: M, f m = n.

    Definition bijective {M N} (f: M -> N) :=
        injective f /\ surjective f. 

    Class homomorphism {M N: model} (h: M -> N) :=
    {
        func_preserved : preserve_func h;
        pred_preserved : preserve_pred h;
    }.

    Class strong_homomorphism {M N: model} (h: M -> N) :=
    {
        homomorphism' :: homomorphism h;
        pred_strong_preserved : strong_preserve_pred h
    }.

    Class embedding {M N: model} (h: M -> N) :=
    {
        strong_homomorphism' :: strong_homomorphism h;
        morphism_injectived : injective h
    }.

    Class isomorphism {M N: model} (h: M -> N) :=
    {
        embedding' :: embedding h;
        morphism_surjective : surjective h 
    }.

    Definition isomorphic {M N: model} :=
        exists h: M -> N, isomorphism h.


End Isomorphism.

Section FunctionalRelation.
    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.

    Definition total_rel (X Y : Type) (R : X -> Y -> Prop) :=
        forall x, exists y, R x y.

    Definition functional_rel X Y (R : X -> Y -> Prop) :=
        forall x y y', R x y -> R x y' -> y = y'.

    Definition function_rel {X Y} (R: X -> Y -> Prop) := 
        functional_rel R /\ total_rel R. 

    Definition rev {X Y} (R: X -> Y -> Prop) x y := R y x.

    Definition injective_rel X Y (R : X -> Y -> Prop) :=
        functional_rel (rev R).

    Definition surjective_rel (X Y : Type) (R : X -> Y -> Prop) :=
        total_rel (rev R).

    Definition bijective_rel X Y (R : X -> Y -> Prop) :=
        function_rel R /\ function_rel (rev R).

    Inductive map_rel {X Y: Type} (R: X -> Y -> Prop): forall n: nat, vec X n -> vec Y n -> Prop :=
        | nil_rel: map_rel R (nil _) (nil _)
        | cons_rel n x y (vx: vec X n) (vy: vec Y n): 
            map_rel R vx vy -> R x y -> map_rel R (cons _ x n vx) (cons _ y n vy).

    Definition preserve_func_rel {M N: model} (R: M -> N -> Prop) := 
        forall func v, exists v',
            R (func ₕ[M] v) (func ₕ[N] v') /\ map_rel R v v'.

    Definition preserve_pred_rel {M N: model} (R: M -> N -> Prop) :=
        forall pred v, exists v',
            (pred ₚ[M] v <-> pred ₚ[N] v') /\ map_rel R v v'.

    Class isomorphism_rel {M N: model} (R: M -> N -> Prop) :=
        {
            func_preserved_rel: preserve_func_rel R;
            pred_preserved_rel: preserve_pred_rel R;
            morphism_biject_rel: bijective_rel R
        }.

End FunctionalRelation.


Section Elementary.
    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.
    Context {ff : falsity_flag}.

    Definition theory_of_model (M: model): theory :=
        fun φ => closed φ /\ M ⊨[_] φ.

    Fact closed_theory_of_model M: closed_T (theory_of_model M).
    Proof.
        now intros phi [closed sat].
    Qed.

    Definition elementary_equivalence M N :=
        forall phi, closed phi -> (M ⊨[_] phi) <-> (N ⊨[_] phi).

    Definition elementary_homomorphism {M N: model} (h: (@domain _ _ M) -> (@domain _ _ N)) :=
        forall phi ρ, M ⊨[ρ] phi <-> N ⊨[ρ >> h] phi.

End Elementary.


Arguments closed_theory_of_model {_ _ _} _.

Notation "M ≡ N"  := (elementary_equivalence M N) (at level 30).
Notation "M ≅ N"  := (exists h: M -> N, isomorphism h) (at level 30).
Notation "M ≅ᵣ N" := (exists R: M -> N -> Prop, isomorphism_rel R) (at level 30).
Notation "N ⪳ M"  := (exists h: N -> M, elementary_homomorphism h) (at level 30).
Notation "N ⪳[ h ] M"  := (@elementary_homomorphism _ _ _ N M h) (at level 30).

Section LöwenheimSkolemTheorem.
    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.
    Context {ff : falsity_flag}.

    Definition syntatic_model_on (M: model) := 
        exists (N: interp term) (h: term -> M), 
            forall phi (ρ: env term), ρ ⊨ phi <-> M ⊨[ρ >> h] phi.

    Definition a_coutable_model M :=
        exists f: nat -> M, surjective f.

    Definition LöwenheimSkolemTheorem :=
        forall M: model, exists N: model, a_coutable_model N /\ N ⪳ M.

    Definition LS := forall M, syntatic_model_on M.

    Hypothesis surjective_term: exists f: nat -> term, surjective f.

    Fact LS_correct: LS -> LöwenheimSkolemTheorem.
    Proof.
        intros H M.
        destruct (H M) as (I & h & HI).
        unshelve eexists. { econstructor. exact I. }
        split. apply surjective_term.
        exists h. intros ??; apply HI.
    Qed.

End LöwenheimSkolemTheorem.

