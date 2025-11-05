From Undecidability.FOL Require Import Syntax.Core Arithmetics.Robinson.
From FOL Require Import ProofMode.
From Stdlib Require Import List.

Section Hil_def.
    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.
    Existing Instance falsity_on. 

    (** * Hilbert Systems *)

    Implicit Type p : peirce.

    Inductive hilAx: forall (ff: falsity_flag) (p: peirce), form -> Prop :=
    | HK phi psi {p}: hilAx p (phi → psi → phi)
    | HS phi psi tau {p}: hilAx p ((phi → psi → tau) → (phi → psi) → phi → tau)
    | CI phi psi {p}: hilAx p (phi → psi → phi ∧ psi)
    | CE1 phi psi {p}: hilAx p (phi ∧ psi → phi)
    | CE2 phi psi {p}: hilAx p (phi ∧ psi → psi)
    | DI1 phi psi {p}: hilAx p (phi → phi ∨ psi)
    | DI2 phi psi {p}: hilAx p (psi → phi ∨ psi)
    | DE phi psi tau {p}: hilAx p (phi ∨ psi → (phi → tau) → (psi → tau) → tau)
    | Ebot phi {p}: hilAx p (⊥ → phi)
    | AllE t phi {p}: hilAx p ((∀ phi) → phi[t..])
    | AllG phi {p}: hilAx p (phi → ∀ phi[↑])
    | AllD phi psi {p}: hilAx p ((∀ phi → psi) → (∀ phi) → (∀ psi)) 
    | ExI phi t {p}: hilAx p (phi[t..] → ∃ phi)
    | ExE phi psi {p}: hilAx p ((∃ phi) → (∀ phi → psi[↑]) → psi)
    | PC phi psi: hilAx class (((phi → psi) → phi) → phi).

    Inductive hilprv A |: forall (p: peirce), form -> Prop :=
    | MP phi psi {p}: hilprv p phi -> hilprv p (phi → psi) -> hilprv p psi
    | HilAx phi n {p}: hilAx p phi -> hilprv p (forall_times n phi)
    | ThAx phi {p}: In phi A -> hilprv p phi.

    Definition thilprv {p: peirce} (T: form -> Prop) (phi: form):=
        exists A, (forall phi, In phi A -> T phi) /\ hilprv A p phi.

End Hil_def.

Notation "A ⊢H phi" := (hilprv A _ phi) (at level 55).
Notation "A ⊢HI phi" := (@hilprv _ _ A intu phi) (at level 55).
Notation "A ⊢HC phi" := (@hilprv _ _ A class phi) (at level 55).
Notation "T ⊢HT phi" := (thilprv T phi) (at level 55).
Notation "T ⊢HTI phi" := (@thilprv _ _ intu T phi) (at level 55).
Notation "T ⊢HTC phi" := (@thilprv _ _ class T phi) (at level 55).
