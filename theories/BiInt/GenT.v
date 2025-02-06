
(* general purpose stuff, using Type rather than Prop *)

Set Implicit Arguments.
Require Import List.
Import ListNotations.
From FOL Require Import BiInt.ExistsT.
From FOL Require Import BiInt.Gen.

Require Export Coq.Classes.CRelationClasses.



Polymorphic Definition rlsT W := list W -> W -> Type.

(* how to express the empty set *)
Inductive emptyT {X : Type} : X -> Type := .

Lemma emptyT_any': forall (sty : Type) Q (prem : sty), emptyT prem -> Q prem.
Proof. intros. induction H. Qed.

Lemma emptyT_any: forall (sty : Type) Q (prem : sty), emptyT prem -> Q.
Proof. intros. induction H. Qed.

(* compare 
  https://coq.inria.fr/stdlib/Coq.Relations.Relation_Definitions.html *)
Polymorphic Definition relationT (A : Type) := A -> A -> Type.
Inductive empty_relT {A B : Type} : A -> B -> Type := .

Lemma rsub_emptyT {A B} r : @rsub A B empty_relT r.
Proof. intros u v e. destruct e. Qed.

Definition transitiveT W (R : relationT W) :=
  forall (x y z : W), R x y -> R y z -> R x z.

(*
Definition iffT A B : Type := (A -> B) * (B -> A).
*)
Lemma iffT_trans: forall A B C, iffT A B -> iffT B C -> iffT A C.
Proof.  unfold iffT. intros. destruct X.  destruct X0. tauto. Qed.

Lemma iffT_sym': forall A B, iffT A B -> iffT B A.
Proof.  unfold iffT. intros. destruct X. tauto. Qed.

Lemma iffT_refl: forall A, iffT A A.
Proof.  unfold iffT. intros. tauto. Qed.

Lemma iffT_D1': forall A B, iffT A B -> A -> B.
Proof.  unfold iffT. intros. tauto. Qed.

Lemma iffT_D2': forall A B, iffT B A -> A -> B.
Proof.  unfold iffT. intros. tauto. Qed.

(* simpler proof objects *)
Definition iffT_sym (A B : Type) (X : iffT A B) := let (f, g) := X in (g, f).
Definition iffT_D1 (A B : Type) (X : iffT A B) a := let (f, _) := X in f a.
Definition iffT_D2 (A B : Type) (X : iffT A B) b := let (_, g) := X in g b.

Lemma prod_mono A A' B B' : (A -> A') -> (B -> B') -> (A * B -> A' * B').
Proof. intros. destruct X1. tauto. Qed. 

Lemma iffT_prod A A' B B' : iffT A A' -> iffT B B' -> iffT (A * B) ( A' * B').
Proof. unfold iffT. intros. destruct X. destruct X0. 
split ; apply prod_mono ; assumption. Qed.

(* or defined versions of these
Definition prod_mono_d A A' B B' aa bb (ab : A * B) :=
  let (a, b) := ab in (aa a : A', bb b : B').

Definition iffT_prod_d A A' B B' (iaa : iffT A A') (ibb : iffT B B') :=
  let (af, ab) := iaa in 
    let (bf, bb) := ibb in (prod_mono af bf, prod_mono ab bb).
*)

Inductive AccT (A : Type) (R : A -> A -> Type) (x : A) : Type :=
    AccT_intro : (forall y : A, R y x -> AccT R y) -> AccT R x.

Definition well_foundedT (A : Type) (R : A -> A -> Type) :=
  forall a : A, AccT R a.

Inductive ForallT (A : Type) (P : A -> Type) : list A -> Type :=
    ForallT_nil : ForallT P []
  | ForallT_cons : forall (x : A) (l : list A),
                  P x -> ForallT P l -> ForallT P (x :: l).

Lemma ForallT_inv:
  forall (A : Type) (P : A -> Type) (a : A) (l : list A),
  ForallT P (a :: l) -> P a.
Proof.  intros. inversion X. subst. exact X0. Qed.

Lemma ForallT_cons_inv:
  forall (A : Type) (P : A -> Type) (x : A) (l : list A),
  ForallT P (x :: l) -> P x * ForallT P l.
Proof.  intros. inversion X. subst. split. exact X0. exact X1. Qed.

Lemma ForallT_single:
  forall (A : Type) (P : A -> Type) (x : A), iffT (ForallT P [x]) (P x).
Proof.  intros.  unfold iffT.  split ; intros. 
  inversion X. subst. exact X0. 
  apply ForallT_cons. exact X.  apply ForallT_nil. Qed. 

Definition ForallT_singleD A P x := iffT_D1 (@ForallT_single A P x).
Definition ForallT_singleI A P x := iffT_D2 (@ForallT_single A P x).

Lemma ForallT_cons_iff:
  forall (A : Type) (P : A -> Type) (x : A) (l : list A),
    iffT (ForallT P (x :: l)) (P x * ForallT P l).
Proof.  intros.  unfold iffT.  split ; intros. 
  apply ForallT_cons_inv.  exact X.
  destruct X. apply ForallT_cons. exact p. exact f. Qed.

Lemma ForallT_append:
  forall (X : Type) (P : X -> Type) (xs ys : list X),
  iffT (ForallT P (xs ++ ys)) (ForallT P xs * ForallT P ys).
Proof.  intros.  unfold iffT.
  induction xs. simpl. split ; intros. split. 
  apply ForallT_nil. exact X0. destruct X0. exact f0.
  destruct IHxs. split ; intros.
  simpl in X0. inversion X0. subst. apply p in X2. destruct X2.
  split. apply ForallT_cons ; assumption.  assumption.
  simpl.  destruct X0. inversion f0. subst.
  apply ForallT_cons. exact X0. apply f. split ; assumption. Qed.

Definition ForallT_appendD A P xs ys := iffT_D1 (@ForallT_append A P xs ys).
Definition ForallT_appendD1 A P xs ys aa := fst (@ForallT_appendD A P xs ys aa).
Definition ForallT_appendD2 A P xs ys aa := snd (@ForallT_appendD A P xs ys aa).
Definition ForallT_appendI' A P xs ys := iffT_D2 (@ForallT_append A P xs ys).
Definition ForallT_appendI A P xs ys ax ay := 
  @ForallT_appendI' A P xs ys (pair ax ay).

Lemma ForallT_2: forall (A : Type) (P : A -> Type) (x y : A),
      iffT (ForallT P [x; y]) (P x * P y).
Proof.  intros.  unfold iffT.  split ; intros.
inversion X. subst.  inversion X1. subst. tauto.
destruct X. apply ForallT_cons. exact p. 
apply ForallT_cons. exact p0.  apply ForallT_nil. Qed.

Lemma ForallT_map_2: forall (A B : Type) (P : B -> Type) (f : A -> B) (x y : A),
      iffT (ForallT P (map f [x; y])) (P (f x) * P (f y)).
Proof.  intros.  simpl.  apply ForallT_2. Qed. 

Lemma ForallT_map: forall (A B : Type) (P : B -> Type) (f : A -> B) (x : A),
      iffT (ForallT P (map f [x])) (P (f x)).
Proof.  intros.  simpl.  apply ForallT_single. Qed. 

Lemma ForallT_map_rev: forall (A B : Type) (P : B -> Type) (f : A -> B) (x : A),
      iffT (P (f x)) (ForallT P (map f [x])).
Proof. intros. simpl. split; intros HH; apply ForallT_single; tauto. Qed. 

Definition ForallT_2D A P x y := iffT_D1 (@ForallT_2 A P x y).
Definition ForallT_D1 A P x y aa := fst (@ForallT_2D A P x y aa).
Definition ForallT_D2 A P x y aa := snd (@ForallT_2D A P x y aa).
Definition ForallT_2I' A P x y := iffT_D2 (@ForallT_2 A P x y).
Definition ForallT_2I A P x y ax ay := @ForallT_2I' A P x y (pair ax ay).

Lemma ForallT_impl:
  forall (A : Type) (P Q : A -> Type),
  (forall a : A, P a -> Q a) -> forall l : list A, ForallT P l -> ForallT Q l.
Proof.  intros.  induction X0. apply ForallT_nil.
  apply ForallT_cons. apply X. apply p. assumption. Qed.

(*
ForallT_Exists_neg:
  forall (A : Type) (P : A -> Prop) (l : list A),
  ForallT (fun x : A => ~ P x) l <-> ~ Exists P l
ForallT_dec:
  forall (A : Type) (P : A -> Prop),
  (forall x : A, {P x} + {~ P x}) ->
  forall l : list A, {ForallT P l} + {~ ForallT P l}
ForallT_map_single:
  forall (A B : Type) (P : B -> Prop) (f : A -> B) (x : A),
  ForallT P (map f [x]) <-> P (f x)
*)


Inductive Forall2T (A B : Type) R : list A -> list B -> Type :=
    Forall2T_nil : Forall2T R [] []
  | Forall2T_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
                   R x y -> Forall2T R l l' -> Forall2T R (x :: l) (y :: l')
  .

Theorem Forall2T_app_inv_l : forall A B (R : A -> B -> Type) l1 l2 l',
  Forall2T R (l1 ++ l2) l' -> 
  sigT2 (fun l1' => Forall2T R l1 l1') (fun l1' => sigT2 (fun l2' =>
    Forall2T R l2 l2') (fun l2' => l' = l1' ++ l2')).
Proof. intros until l1. induction l1. simpl.
intros. exists []. apply Forall2T_nil.
exists l'. assumption. simpl. reflexivity.
simpl. intros. inversion_clear X.
apply IHl1 in X1. destruct X1.
exists (y :: x). apply Forall2T_cons ; assumption.
destruct s. subst. simpl. eexists. eassumption. reflexivity. Qed.

Theorem Forall2T_app_inv_r : forall A B (R : A -> B -> Type) l1' l2' l, 
  Forall2T R l (l1' ++ l2') ->
  sigT2 (fun l1 => Forall2T R l1 l1') (fun l1 => sigT2 (fun l2 => 
    Forall2T R l2 l2') (fun l2 => l = l1 ++ l2)).
Proof. intros until l1'. induction l1'. simpl.
intros. exists []. apply Forall2T_nil. 
exists l. assumption. simpl. reflexivity.
simpl. intros. inversion_clear X.
apply IHl1' in X1. destruct X1.
exists (x :: x0). apply Forall2T_cons ; assumption.
destruct s. subst. simpl. eexists. eassumption. reflexivity. Qed.

Theorem Forall2T_app : forall A B (R : A -> B -> Type) l1 l2 l1' l2',
  Forall2T R l1 l1' -> Forall2T R l2 l2' -> Forall2T R (l1 ++ l2) (l1' ++ l2').
Proof. intros until l1. induction l1. simpl.
intros. inversion_clear X. simpl. assumption.
intros. inversion_clear X. simpl. apply Forall2T_cons. assumption.
apply IHl1 ; assumption. Qed.

(* this isn't usable, because destruct doesn't work for first clause 
Inductive InT A (a : A) : list A -> Type :=
  | InT_eq : forall l, @InT A a (a :: l)
  | InT_cons : forall b l, @InT A a l -> @InT A a (b :: l).
 *)
  Ltac cET :=
  repeat match goal with
    | [ H : _ /\ _ |- _ ] => inversion_clear H
    | [ H : ex _ |- _ ] => inversion_clear H
    | [ H : False |- _ ] => contradiction H
    | [ H : sig _ |- _ ] => inversion_clear H
    | [ H : sigT _ |- _ ] => inversion_clear H
    | [ H : False |- _ ] => contradiction H
    | [ H : _ * _ |- _ ] => inversion_clear H
         end.

  Ltac cET_nr :=
  match goal with
    | [ H : _ /\ _ |- _ ] => inversion_clear H
    | [ H : ex _ |- _ ] => inversion_clear H
    | [ H : False |- _ ] => contradiction H
    | [ H : sig _ |- _ ] => inversion_clear H
    | [ H : sigT _ |- _ ] => inversion_clear H
    | [ H : False |- _ ] => contradiction H
    | [ H : _ * _ |- _ ] => inversion_clear H
    end.

Inductive InT A (a : A) : list A -> Type :=
  | InT_eq' : forall b l, b = a -> @InT A a (b :: l)
  | InT_cons : forall b l, @InT A a l -> @InT A a (b :: l).

Lemma InT_eq: forall A a l, @InT A a (a :: l).
Proof.  intros. apply InT_eq'. reflexivity. Qed.

Definition InT_2nd A (a b : A) l := InT_cons a (InT_eq b l).

Lemma InT_appL: forall A a X Y, InT (a : A) X -> InT a (X ++ Y).
Proof.  intros.  induction X0 ; simpl.  subst.
apply InT_eq.  apply InT_cons. assumption. Qed.

Lemma InT_appR: forall A a X Y, InT (a : A) Y -> InT a (X ++ Y).
Proof.  intros.  induction X ; simpl. assumption.
apply InT_cons. assumption. Qed.

Ltac solve_InT := apply InT_eq || 
  ((apply InT_cons || (apply InT_appL + apply InT_appR)) ; solve_InT).

Lemma InT_appE': forall A a Z, InT (a : A) Z -> 
  forall X Y, Z = X ++ Y -> InT a X + InT a Y.
Proof.  intros A a Z X. induction X ; intros.
destruct X ; simpl in H. subst. right. apply InT_eq.
injection H. intros. subst. left. apply InT_eq.
destruct X0 ; simpl in H. subst. right. apply InT_cons. assumption.
injection H. intros. subst. pose (@eq_refl (list A)). apply IHX in e.
destruct e. left. apply InT_cons. assumption.
right. assumption.  Qed.

Lemma InT_appE: forall A a X Y, InT (a : A) (X ++ Y) -> InT a X + InT a Y.
Proof.  intros. eapply InT_appE'. eassumption. reflexivity. Qed.

Lemma InT_nilE': forall A a Z any, InT (a : A) Z -> Z = [] -> any.
Proof. intros. induction X ; discriminate. Qed.

Lemma InT_nilE: forall A a any, InT (a : A) [] -> any.
Proof.  intros. eapply InT_nilE'. eassumption. reflexivity. Qed.

Lemma InT_split: forall (A : Type) (x : A) (l : list A),
  InT x l -> sigT (fun l1 => sigT (fun l2 => l = l1 ++ x :: l2)).
Proof. intros.  induction X.
exists [].  exists l. simpl. subst. reflexivity.
destruct IHX. destruct s. subst.
exists (b :: x0).  exists x1. simpl. reflexivity. Qed.

Lemma InT_inv: forall A a b Y, InT (a : A) (b :: Y) -> (b = a) + InT a Y.
Proof. intros.  inversion X ; subst ; tauto. Qed.

Lemma InT_map: forall (A B : Type) (f : A -> B) (l : list A) (x : A),
  InT x l -> InT (f x) (map f l).
Proof. intros. induction X.
subst. simpl. apply InT_eq.
simpl. apply InT_cons. assumption. Qed.

Lemma InT_mapE: forall (A B : Type) (f : A -> B) (l : list A) (y : B),
       (InT y (map f l)) -> (sigT (fun x => prod (f x = y) (InT x l))).
Proof. intros. 
induction l. eapply InT_nilE in X. apply X.
simpl in X.  inversion X. subst. exists a.
split. reflexivity.  apply InT_eq.
subst. apply IHl in X0. cD. exists X0. subst. split. reflexivity. 
apply InT_cons. exact X2. Qed.

Lemma InT_map_iffT: forall (A B : Type) (f : A -> B) (l : list A) (y : B),
       iffT (InT y (map f l)) (sigT (fun x => prod (f x = y) (InT x l))).
Proof. intros. apply pair. apply InT_mapE.
intro. cD. subst. apply InT_map. exact X1. Qed.

Definition InT_mapI A B f l y := iffT_D2 (@InT_map_iffT A B f l y).

Lemma InT_concat: forall (A : Type) a (xs : list A) pss,
     InT a xs -> InT xs pss -> InT a (concat pss).
Proof. intros. induction X0. subst. simpl. apply InT_appL. assumption.
simpl. apply InT_appR. assumption. Qed.

Lemma Forall2T_ex_l: forall A B (R : A -> B -> Type) xs ys x,
  Forall2T R xs ys -> InT x xs -> sigT2 (fun y => InT y ys) (fun y => R x y).
Proof. intros A B R xs ys x X. induction X.
intro. eapply InT_nilE in X. eassumption.
intro. inversion X0 ; subst. eexists. apply InT_eq. assumption.
apply IHX in X1. destruct X1. eexists. eapply InT_cons. eassumption.
assumption. Qed.

Lemma Forall2T_ex_r: forall A B (R : A -> B -> Type) xs ys x,
  Forall2T R ys xs -> InT x xs -> sigT2 (fun y => InT y ys) (fun y => R y x).
Proof. intros A B R xs ys x X. induction X.
intro. eapply InT_nilE in X. eassumption.
intro. inversion X0 ; subst. eexists. apply InT_eq. assumption.
apply IHX in X1. destruct X1. eexists. eapply InT_cons. eassumption.
assumption. Qed.

Lemma ForallT_forall: forall (A : Type) (P : A -> Type) (l : list A),
  iffT (ForallT P l) (forall x : A, InT x l -> P x).
Proof. intros.  induction l ; unfold iffT ; split ; intros.
  eapply InT_nilE in X0. exact X0. apply ForallT_nil.
  unfold iffT in IHl. destruct IHl. inversion X.
  inversion X0 ; subst ; firstorder.
  unfold iffT in IHl. destruct IHl. 
  apply ForallT_cons. apply X. apply InT_eq.
  apply f. intros. apply X. apply InT_cons. exact X0. Qed.

Definition ForallTD_forall A P x := iffT_D1 (@ForallT_forall A P x).
Definition ForallTI_forall A P x := iffT_D2 (@ForallT_forall A P x).

Lemma InT_In: forall A a Y, InT (a : A) Y -> In a Y.
Proof. intros. induction X. subst. apply in_eq.
apply in_cons. assumption. Qed.

Lemma In_InT: forall A a Y, In (a : A) Y -> ex (fun _ : InT a Y => True).
Proof.  intros.  induction Y. apply in_nil in H. contradiction.
apply in_inv in H. destruct H. subst. exists. apply InT_eq. apply I.
apply IHY in H. destruct H. exists. apply InT_cons. assumption. apply I. Qed.

(* generalise this *)
Definition anon (p : Type) := ex (fun _ : p => True).

Lemma anonI : forall p, p -> anon p.
Proof. intros.  unfold anon. exists. assumption. apply I. Qed.

Lemma InT_In': forall A a Y, ex (fun _ : InT (a : A) Y => True) -> In a Y.
Proof.  intros. destruct H. apply InT_In. assumption. Qed. 
(* why can't we do anon p -> p in general, we do it here?
  note, trying apply InT_In. before destruct H. causes the error below *)

(*
Lemma anonD : forall p, anon p -> p.
Proof. unfold anon. intros. destruct H.
Error: Case analysis on sort Type is not allowed for inductive definition ex.
*)
Lemma anonD : forall p (q : Prop), (p -> q) -> (anon p -> q).
Proof. unfold anon. intros. destruct H0. tauto. Qed.

Lemma anon_eq: forall P : Prop, anon P <-> P.
Proof. intros. unfold iff. split. apply anonD. tauto. apply anonI. Qed.  

Lemma InT_In_eq: forall A a Y, anon (InT (a : A) Y) <-> In a Y.
Proof. unfold anon. intros. unfold iff. split ; intros.
apply InT_In'. assumption. apply In_InT. assumption. Qed.

Lemma InT_In_eq': forall A a Y, anon (InT (a : A) Y) <-> In a Y.
Proof. intros. unfold iff. split.
apply anonD. apply InT_In.
intro. unfold anon.  apply In_InT. assumption. Qed.

Lemma anon_prod: forall t u, anon (prod t u) <-> anon t /\ anon u.
Proof.  intros.  unfold iff. unfold anon. split ; intros ; 
  cD ; try split ; exists ; tauto. Qed.

Lemma anon_sum: forall t u, anon (sum t u) <-> anon t \/ anon u.
Proof.  intros.  unfold iff. unfold anon. split ; intros ; sD ;
  [> left | right | | ] ; exists ; tauto. Qed.

(* doubt if converse is valid *)
Lemma anon_imp: forall t u, anon (t -> u) -> (anon t -> anon u).
Proof.  unfold anon. intros.  cD. exists ; tauto.  Qed.

Lemma anon_iffT: forall t u, anon (iffT t u) -> (anon t <-> anon u).
Proof.  unfold iff. unfold iffT. intros. 
rewrite -> anon_prod in H. destruct H. 
split ; intros ; eapply anon_imp ; eassumption. Qed.

Lemma anon_sigT: forall A P, anon (@sigT A P) -> @ex A (fun x => anon (P x)).
Proof.  unfold anon. intros. cD. eexists. eexists. eassumption. apply I. Qed.

Lemma anon_forall: forall T P, 
  anon (forall x : T, P x) -> forall x : T, anon (P x).
Proof.  unfold anon. intros. destruct H. exists. apply (x0 x). apply I. Qed.

Lemma ForallT_Forall': forall A (P : A -> Prop) (xs : list A),
  ForallT P xs -> Forall P xs.
Proof.  intros.  induction X. apply Forall_nil.
apply Forall_cons. assumption. assumption. Qed.

Lemma ForallT_Forall: forall A P (xs : list A),
  ForallT P xs -> Forall (fun x => anon (P x)) xs.
Proof.  intros.  induction X. apply Forall_nil.
apply Forall_cons. apply anonI. assumption. assumption. Qed.

Lemma Forall_ForallT: forall A P (xs : list A),
  Forall P xs -> anon (ForallT P xs).
Proof.  intros.  induction H. apply anonI. apply ForallT_nil.
unfold anon in IHForall. cD.  apply anonI. (* can't do this before cD *)
apply ForallT_cons ; assumption. Qed.

(* note proof carefully, intros then induction H fails,
  inversion H too early fails *)
Lemma Forall_ForallT': forall A P (xs : list A), Forall P xs -> ForallT P xs.
Proof.  intros. induction xs. apply ForallT_nil.
apply ForallT_cons. inversion H. subst. assumption.
apply IHxs.  inversion H. subst. assumption.
Qed.  

Lemma inhabited_anon: forall A, inhabited A <-> anon A.
Proof. unfold iff.  unfold anon.  intros.  split ; intros.
 destruct H. exists ; tauto.
 destruct H. apply inhabits. assumption. Qed.

Lemma want_left_prod_under_universal : forall (T : Type) (P : T -> Type) (Q1 : T -> Type) (S : Type),
    (forall y : T, P y -> ((Q1 y) * S)) ->
    forall y : T, P y -> Q1 y.
Proof. firstorder. Qed.

Lemma want_right_prod_under_universal : forall (T : Type) (P : T -> Type) (Q1 : T -> Type) (S : Type),
    (forall y : T, P y -> (S * (Q1 y))) ->
    forall y : T, P y -> Q1 y.
Proof. firstorder. Qed.

Lemma want_right_prod_under_universal' : forall (T : Type) (P : T -> Type) (Q1 S : T -> Type),
    (forall y : T, P y -> ((S y) * (Q1 y))) ->
    forall y : T, P y -> Q1 y.
Proof. firstorder. Qed.

Lemma want_prod_under_universal4 : forall (T : Type) (P : T -> Type) (Q1 Q2 Q3 Q4 : T -> Type),
    (forall y : T, P y -> ((Q1 y) * (Q2 y) * (Q3 y) * (Q4 y))) ->
    (forall y : T, P y -> Q1 y) *
    (forall y : T, P y -> Q2 y) *
    (forall y : T, P y -> Q3 y) *
    (forall y : T, P y -> Q4 y).
Proof. firstorder. Qed.

Lemma prod_nat_split : forall (P : (nat * nat) -> Type),
    (forall y : nat * nat, P y) ->
    (forall n m : nat, P (n,m)).
Proof. firstorder. Qed.


Inductive empty : Type := .

Lemma empty_explosion : forall (A : Type), empty -> A.
Proof. intros A H. inversion H. Qed.

Notation "T~ A" := (A -> empty) (at level 60).

Lemma False_empty : False -> empty.
Proof. intros H. inversion H. Qed.

Lemma empty_False : empty -> False.
Proof. intros H. inversion H. Qed.

Inductive leT (n : nat) : nat -> Type :=
  | leT_n : leT n n | leT_S : forall m : nat, leT n m -> leT n (S m).

Theorem leT_n_S : forall n m, leT n m -> leT (S n) (S m).
Proof. intros. induction H. apply leT_n. apply (leT_S IHleT). Qed.

Lemma leT_S_n' : forall sn sm, leT sn sm -> 
  forall n m, sn = S n -> sm = S m -> leT n m.
Proof. intros * ss. induction ss.
- intros. subst. inversion H0. apply leT_n.
- destruct m.
+ inversion ss. intros. inversion H0.
+ intros. subst.  specialize (IHss _ _ eq_refl eq_refl).
inversion H0.  exact (leT_S IHss). Qed.

(* forall n m, leT (S n) (S m) -> leT n m *)
Definition leT_S_n n m l := @leT_S_n' _ _ l n m eq_refl eq_refl.

Lemma leT_trans' l m n: leT m n -> leT l m -> leT l n.
Proof. intro. induction H ; intro. apply H. exact (leT_S (IHleT H0)). Qed.

Definition leT_trans l m n llm lmn := @leT_trans' l m n lmn llm.

Lemma leT_0_n n: leT 0 n. 
Proof. induction n. apply leT_n. apply (leT_S IHn). Qed.

Lemma leT_plus_r n m : leT m (n + m).
Proof. induction n ; simpl. apply leT_n. apply (leT_S IHn). Qed.

Lemma leT_plus_l n m : leT n (n + m).
Proof. induction n ; simpl. apply leT_0_n. apply (leT_n_S IHn). Qed.

Theorem eq_S_F n : S n = n -> False.
Proof. intro. induction n ; inversion H. tauto. Qed.

Theorem leT_S_F n : leT (S n) n -> False.
Proof. induction n ; intro. inversion H. apply leT_S_n in H. tauto. Qed.

Lemma leT_S_or_eq n m : leT n m -> leT (S n) m + (n = m).
Proof. intro. induction H.  tauto.  left. exact (leT_n_S H). Qed.

Lemma leT_or_gt n m : leT n m + leT (S m) n.
Proof. induction n. left. apply leT_0_n.
destruct IHn. apply leT_S_or_eq in l. destruct l. exact (inl l).
subst. exact (inr (leT_n _)).  exact (inr (leT_S l)). Qed.

Lemma leT_ex_plus k n : leT k n -> { m : nat & Nat.add m k = n }.
Proof. intro lkn. induction lkn. exists 0. simpl. reflexivity.
cD. subst. exists (S IHlkn). simpl. reflexivity. Qed.