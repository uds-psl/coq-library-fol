(** * Basic First-Order Logic *)
(** ** Syntax *)
From Undecidability Require Import Shared.Libs.PSL.Vectors.Vectors.
From Undecidability Require Import Shared.ListAutomation.
From Undecidability.FOL Require Import Syntax.Core.
Import ListAutomationNotations.

Import Coq.Vectors.Vector.
Local Notation vec := t.




(* Full syntax *)

Module BiIntSyntax.

  Inductive full_logic_sym : Type :=
  | Conj : full_logic_sym
  | Disj : full_logic_sym
  | Impl : full_logic_sym
  | Excl : full_logic_sym.

  Inductive full_logic_quant : Type :=
  | All : full_logic_quant
  | Ex : full_logic_quant.

  Definition full_operators : operators :=
    {| binop := full_logic_sym ; quantop := full_logic_quant |}.

  #[export] Hint Immediate full_operators : typeclass_instances.

  Declare Scope full_syntax.
  Delimit Scope full_syntax with Ffull.

  #[global] Open Scope full_syntax.
  Notation "∀ Phi" := (@quant _ _ full_operators _ All Phi) (at level 50) : full_syntax.
  Notation "∃ Phi" := (@quant _ _ full_operators _ Ex Phi) (at level 50) : full_syntax.
  Notation "A ∧ B" := (@bin _ _ full_operators _ Conj A B) (at level 41) : full_syntax.
  Notation "A ∨ B" := (@bin _ _ full_operators _ Disj A B) (at level 42) : full_syntax.
  Notation "A → B" := (@bin _ _ full_operators _ Impl A B) (at level 43, right associativity) : full_syntax.
  Notation "A '--<' B" := (@bin _ _ full_operators _ Excl A B) (at level 43, right associativity) : full_syntax.
  Notation "⊥" := (falsity) : full_syntax.
  Notation "¬ A" := (A → ⊥) (at level 42) : full_syntax.
  Notation "⊤" := (⊥ → ⊥) : full_syntax.
  Notation "∞ A" := (⊤ --< A) (at level 42) : full_syntax.
  Notation "A ↔ B" := ((A → B) ∧ (B → A)) (at level 43) : full_syntax.

  Fixpoint impl {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} {ff : falsity_flag} (A : list form) phi :=
    match A with
    | [] => phi
    | psi :: A => bin _ _ full_operators _ Impl psi (impl A phi)
    end.

  Notation "A ==> phi" := (impl A phi) (right associativity, at level 55).

  Definition exist_times {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} {ff : falsity_flag} n (phi : form) := iter (fun psi => ∃ psi) n phi.
  Definition forall_times {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} {ff : falsity_flag} n (phi : form) := iter (fun psi => ∀ psi) n phi.

End BiIntSyntax.