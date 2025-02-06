Set Implicit Arguments.
Require Import List.
Import ListNotations.

Definition rsub U V f g := forall (u : U) (v : V), f u v -> g u v.

Lemma rsub_def: forall U V (f g : U -> V -> Type), 
  @rsub U V f g = forall (u : U) (v : V), f u v -> g u v.
Proof.  intros.  unfold rsub.  reflexivity. Qed.

Lemma rsub_trans U V (f g h : U -> V -> Type) :
  rsub f g -> rsub g h -> rsub f h.
Proof. unfold rsub. firstorder. Qed. 

Lemma rsub_id U V (f : U -> V -> Type) : rsub f f.
Proof. unfold rsub. firstorder. Qed. 

Definition req U V f g := prod (@rsub U V f g) (rsub g f).

Lemma req_refl U V f : @req U V f f.
Proof. unfold req. split ; apply rsub_id. Qed.

Lemma req_sym U V f g : @req U V f g -> @req U V g f.
Proof. unfold req. tauto. Qed.

Lemma req_trans U V f g h : @req U V f g -> @req U V g h -> @req U V f h.
Proof. unfold req. intros F B. destruct F. destruct B.
split ; eapply rsub_trans ; eassumption.  Qed.

Definition rls W := list W -> W -> Prop.

(* lemmas which shouldn't be necessary at all! *)

Lemma or_false: forall P : Prop, iff (or P False) P. Proof. tauto. Qed.
Lemma false_or: forall P : Prop, iff (or False P) P. Proof. tauto. Qed.
Lemma and_true: forall P : Prop, iff (and P True) P. Proof. tauto. Qed.
Lemma true_and: forall P : Prop, iff (and True P) P. Proof. tauto. Qed.

Lemma rappl: forall (A B : Prop), A -> (A -> B) -> B.
Proof.  tauto.  Qed.

Lemma appl: forall (A B : Prop), (A -> B) -> A -> B.
Proof.  tauto.  Qed.

Lemma gen_cong: forall T U f g, f = g -> 
  forall x y, x = y -> (f (x : U) : T) = g y.
Proof. intros. subst. reflexivity. Qed.

Lemma fun_cong: forall T U f g, f = g -> 
  forall x, (f (x : U) : T) = g x.
Proof. intros. subst. reflexivity. Qed.

(* similar to Coq.Init.Logic.f_equal *)
Lemma arg_cong: forall T U f x y, x = y -> (f (x : U) : T) = f y.
Proof. intros. subst. reflexivity. Qed.

Lemma arg_cong_imp: forall U f x y, x = y -> f (x : U) -> f y.
Proof. intros. subst. assumption. Qed.

(* similar to Coq.Init.Logic.eq_rect *)
Lemma arg_cong_imp': forall U f x y, f (x : U) -> x = y -> f y.
Proof. intros. subst. assumption. Qed.

Lemma arg1_cong_imp: forall U V f x y z, x = y -> f (x : U) (z : V) -> f y z.
Proof. intros. subst. assumption. Qed.

Lemma arg1_cong_imp': forall U V f x y z, f (x : U) (z : V) -> x = y -> f y z.
Proof. intros. subst. assumption. Qed.

(* iffD1, iffD2 for Type *)
Lemma iffD1: forall x y, (x = y) -> x -> y.
Proof. intros.  subst.  assumption. Qed.

Lemma iffD2: forall x y, (x = y) -> y -> x.
Proof. intros.  subst.  assumption. Qed.

(* PiffD1, PiffD2 for Prop *)
Lemma PiffD1: forall x y, (x <-> y) -> x -> y.
Proof. intros.  rewrite -> H in H0.  assumption. Qed.

Lemma PiffD2: forall x y, (x <-> y) -> y -> x.
Proof. intros.  rewrite <- H in H0.  assumption. Qed.

Lemma eq_TrueI: forall (P : Prop), (P -> (P <-> True)).
intros. unfold iff. apply conj ; intro.  apply I. assumption.
Qed.

Definition rsub_imp U V (f g : U -> V -> Type) := iffD1 (@rsub_def U V f g).
Definition rsubI U V f g := iffD2 (@rsub_def U V f g).
Definition rsubD U V f g := iffD1 (@rsub_def U V f g).

(* and do req_def, reqI, reqD as for rsub *)

(* see also eq_refl, eq_trans, eq_sym, eq_ind, eq_ind_r *)

Ltac refl_ni :=
  match goal with
    | [ |- ?P = ?P ] => reflexivity 
    end.

Lemma pair_eqI: forall T U (u v : T) (x y : U),
  u = v -> x = y -> (u,x) = (v,y).
Proof. intros. subst. reflexivity. Qed.

Ltac rename_last name :=
  match goal with
    | [ K : _ |- _ ] => rename K into name
    end.

Ltac clear_one :=
  match goal with
    | [ K : _ |- _ ] => clear K
    end.

Ltac cE :=
  repeat match goal with
    | [ H : _ /\ _ |- _ ] => inversion_clear H
    | [ H : ex _ |- _ ] => inversion_clear H
    | [ H : False |- _ ] => contradiction H
    end.

(* one step of cDv *)
Ltac cD' :=
  match goal with
    | [ H : _ /\ _ |- _ ] => destruct H as [?H ?H]
    | [ H : prod _ _ |- _ ] => destruct H as [?H ?H]
    | [ H : ex _ |- _ ] => destruct H as [?H ?H]
    | [ H : sig _ |- _ ] => destruct H as [?H ?H]
    | [ H : sigT _ |- _ ] => destruct H as [?H ?H]
    | [ H : ex2 _ _ |- _ ] => destruct H as [?H ?H ?H]
    | [ H : sig2 _ _ |- _ ] => destruct H as [?H ?H ?H]
    | [ H : sigT2 _ _ |- _ ] => destruct H as [?H ?H ?H]
    | [ H : False |- _ ] => contradiction H
    end.

Ltac cD := repeat cD'.

Ltac sE :=
  repeat match goal with
    | [ H : _ /\ _ |- _ ] => inversion_clear H
    | [ H : _ \/ _ |- _ ] => inversion_clear H
    | [ H : ex _ |- _ ] => inversion_clear H
    | [ H : False |- _ ] => contradiction H
    end.

Ltac sD' :=
  match goal with
    | [ H : _ /\ _ |- _ ] => destruct H as [?H ?H]
    | [ H : prod _ _ |- _ ] => destruct H as [?H ?H]
    | [ H : _ \/ _ |- _ ] => destruct H as [?H | ?H]
    | [ H : sumbool _ _ |- _ ] => destruct H as [?H | ?H]
    | [ H : sum _ _ |- _ ] => destruct H as [?H | ?H]
    | [ H : ex _ |- _ ] => destruct H as [?H ?H]
    | [ H : sig _ |- _ ] => destruct H as [?H ?H]
    | [ H : sigT _ |- _ ] => destruct H as [?H ?H]
    | [ H : False |- _ ] => contradiction H
    end.

(* extra stuff used in sD, not in cD *)
Ltac sDx :=
  match goal with
    | [ H : _ \/ _ |- _ ] => destruct H as [?H | ?H]
    | [ H : sumbool _ _ |- _ ] => destruct H as [?H | ?H]
    | [ H : sum _ _ |- _ ] => destruct H as [?H | ?H]
    end.

Ltac sD := repeat (cD' || sDx).

(* various solutions to dealing with hypothesis forall x, A x -> B x 
  see emails 8-9 Jan 
evar (z : list (rel (list (PropF V)) * dir)).
specialize (H1 z).
subst z. (* subst. alone doesn't work *)

match type of H1 with
| ?A -> _ =>
  assert (I : A); [| apply H1 in I ]
  end. 

apply (fun G2 G1 => G1 (H1 G2)). 

eassert _ as I%H1.

or 
eassert _ ; [ apply H1 | ].
eassert _ as I ; [ | apply H1 in I ].

all : cycle 1. Show. 
Undo. Show. 
*)

(* tactics from Lily Chung <ikdc@mit.edu> Tue, 8 Jan 2019
  https://gist.github.com/ichung/032b849da0c3c5e3987c83f835d111ee *) 

(* [require], when called on a hypothesis [H : P -> Q],
   asserts that P actually holds,
   and thus that H's type can be replaced with Q *)
Ltac require H :=
  match type of H with
  | forall _  : ?H1, _ =>
    let x := fresh in
    let y := x in
    assert H1 as x; [| specialize (H x); clear y]
  end.

(* [erequire H], when called on a hypothesis [H : forall x, Q x],
   specializes [H] to a new evar to be filled in later *)
Ltac erequire H :=
  match type of H with
  | forall _  : ?H1, _ =>
    let x := fresh in
    evar (x : H1); specialize (H x); subst x
end.

(* solution from  Marko Doko <mdoko@mpi-sws.org> Tue, 8 Jan 2019
  solves question for quantified implication, changed to use Ltac

Tactic Notation "specialize_full" ident(H) :=
  let foo := fresh in
  evar (foo : Prop); cut (foo); subst foo; cycle 1;
  [eapply H|try clear H; intro H].
*)

Ltac specialize_full H := 
  let foo := fresh in
  evar (foo : Prop); cut (foo); subst foo; cycle 1;
  [eapply H|try clear H; intro H].

Ltac prgt t :=
  match goal with
    | [ |- ?P ] => idtac t P
    end.

Lemma in_single: forall (A : Type) (a x : A), In a [x] <-> a = x.
Proof. intros. unfold iff. split ; intros.
  apply in_inv in H. sD.
  subst. reflexivity.
  apply in_nil in H. contradiction.
  subst.  apply in_eq. Qed.

Lemma Forall_cons_inv: forall A (P : A -> Prop) (x : A) (l : list A),
  Forall P (x :: l) -> P x /\ Forall P l.
Proof. intros. inversion H. tauto. Qed.

Lemma Forall_cons_iff: forall A (P : A -> Prop) (x : A) (l : list A),
  Forall P (x :: l) <-> P x /\ Forall P l.
Proof.  intros. unfold iff. apply conj ; intro. 
apply Forall_cons_inv. assumption.
inversion H.  apply Forall_cons ; assumption.
Qed.

Lemma Forall_append: forall X P (xs ys: list X),
  Forall P (xs ++ ys) <-> Forall P xs /\ Forall P ys.
Proof.
intros.  induction xs.  easy.
simpl.  rewrite !Forall_cons_iff.  rewrite IHxs.  tauto.
Qed.

Lemma Forall_single: forall (A : Type) P x, @Forall A P [x] <-> P x.
Proof. intros. unfold iff. rewrite Forall_forall. 
  split ; intros.
  apply H. rewrite in_single. reflexivity.
  inversion H0. subst. exact H.
  apply in_nil in H1. contradiction. Qed.
  
Lemma Forall_map_single: forall (A B : Type) P (f : A -> B) x, 
  Forall P (map f [x]) <-> P (f x).
Proof.  simpl. intros. apply Forall_single. Qed.

Lemma Forall_map_2: forall (A B : Type) P (f : A -> B) x y, 
  Forall P (map f [x; y]) <-> P (f x) /\ P (f y).
Proof.  intros. rewrite Forall_forall. unfold iff. split.
  intros. split. 
  pose (H (f x)). apply p. rewrite in_map_iff. exists x. simpl. tauto.
  pose (H (f y)). apply p. rewrite in_map_iff. exists y. simpl. tauto.
  intros. rewrite -> in_map_iff in H0. cD. simpl in H3.
  sD ; subst ; assumption.  Qed.

Lemma map_cons_ex T U (f : T -> U) ys x : forall ws,
  map f ws = x :: ys -> {u : T & x = f u &
    {vs : list _ & ys = map f vs & ws = u :: vs}}.
Proof. intro. destruct ws ; simpl ; intro.  discriminate.
injection H as . subst. exists t. reflexivity.
exists ws ; reflexivity. Qed.

Lemma map_cons_ex' T U (f : T -> U) ys x : forall ws,
  map f ws = x :: ys -> {u : T & x = f u &
    {vs : list _ & map f vs = ys & ws = u :: vs}}.
Proof. intros ws meq. apply map_cons_ex in meq. cD.
exists meq. assumption.  exists meq1. subst. reflexivity. assumption. Qed.

Lemma map_app_ex T U (f : T -> U) ys xs : forall ws,
  map f ws = xs ++ ys -> {us : _ & map f us = xs &
    {vs : _ & map f vs = ys & ws = us ++ vs}}.
Proof. induction xs ; simpl ; intros.
exists []. simpl. reflexivity.
simpl. exists ws. subst. reflexivity.  reflexivity.
apply map_cons_ex in H. destruct H. destruct s. subst.
apply eq_sym in e0. apply IHxs in e0. destruct e0.  destruct s. subst.
exists (x :: x1). simpl. reflexivity. exists x2. reflexivity.
simpl. reflexivity. Qed.

Lemma map_eq_nil T U (f : T -> U) xs : map f xs = [] -> xs = [].
Proof. intro mx. destruct xs. reflexivity.  simpl in mx. discriminate mx. Qed.

Ltac name_goal name := refine ?[name].

