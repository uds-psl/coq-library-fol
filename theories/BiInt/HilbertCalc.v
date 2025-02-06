Require Import List.
Export ListNotations.
Require Import Ensembles.
Require Import Arith.

From Undecidability.FOL Require Import Syntax.Facts.

From FOL Require Import GenT Gen.
From FOL Require Import BiInt.BiInt SyntaxFeatures.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Import BiIntSyntax.

(* In this file we define a Hilbert calculus based on sets for the first-order
   bi-intuitionistic logic FOBIL. *)

Section FOBIH.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

(* We define here the axioms. *)

Inductive Axioms (F : form) : Prop :=
 | A1 A B : F = (A → (B → A)) -> Axioms F
 | A2 A B C : F = (A → (B → C)) → ((A → B) → (A → C)) -> Axioms F
 | A3 A B : F = A → (A ∨ B) -> Axioms F
 | A4 A B : F = B → (A ∨ B) -> Axioms F
 | A5 A B C : F = (A → C) → ((B → C) → ((A ∨ B) → C)) -> Axioms F
 | A6 A B : F = (A ∧ B) → A -> Axioms F
 | A7 A B : F = (A ∧ B) → B -> Axioms F
 | A8 A B C : F = (A → B) → ((A → C) → (A → (B ∧ C))) -> Axioms F
 | A9 A : F = ⊥ → A -> Axioms F
 | BA1 A B : F= A → (B ∨ (A --< B)) -> Axioms F
 | BA2 A B : F = (A --< B) → ∞ (A → B) -> Axioms F
 | BA3 A B C : F = ((A --< B) --< C) → (A --< (B ∨ C)) -> Axioms F
 | BA4 A B : F = (¬ (A --< B)) → (A → B) -> Axioms F
 | QA1 A B : F =  (∀ (A[↑] → B)) → (A → ∀ B) ->  Axioms F
 | QA2 A t : F =  (∀ A) → A[t..] ->  Axioms F
 | QA3 A t : F =  (A[t..] → ∃ A) ->  Axioms F.

(* At last we can define our calculus FOBIH. *)

Inductive FOBIH_prv : (form -> Prop) -> form -> Prop :=
  | Id Γ A : In _ Γ A -> FOBIH_prv Γ A
  | Ax Γ A : Axioms A -> FOBIH_prv Γ A
  | MP Γ A B : FOBIH_prv Γ (A → B) ->  FOBIH_prv Γ A -> FOBIH_prv Γ B
  | DN Γ A : FOBIH_prv (Empty_set _) A ->  FOBIH_prv Γ (¬ ∞ A)
  | Gen Γ A : FOBIH_prv (fun x => exists B, ((x = (subst_form ↑) B) /\ In _ Γ B)) A -> FOBIH_prv Γ (∀ A)
  | EC Γ A B : FOBIH_prv (fun x => exists B, ((x = (subst_form ↑) B) /\ In _ Γ B)) (A → (B[↑])) -> FOBIH_prv Γ ((∃ A) → B).

(* Define the general notion of derivable pair. *)

Fixpoint list_disj (l : list form) : form :=
match l with
 | nil => ⊥
 | h :: t => h ∨ (list_disj t)
end.

Fixpoint list_conj (l : list form) : form :=
match l with
 | nil => ⊤
 | h :: t => h ∧ (list_conj t)
end.

Definition pair_der Γ Δ : Prop :=
    exists (l : list form), NoDup l /\ (forall A, List.In A l -> Δ A) /\
        FOBIH_prv Γ (list_disj l).


End FOBIH.
