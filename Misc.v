Set Implicit Arguments.
Require Export Setoid.
(** * Preliminaries *)
(** ** Definition of iterator [comp]
   [comp f u n x] is defined as $(f~(u~(n-1)).. (f (u~ 0)~x))$ *)

Fixpoint comp (A:Type) (f : A -> A -> A) (x : A) (u : nat -> A) (n:nat) {struct n}: A := 
   match n with O => x| (S p) => f (u p) (comp f x u p) end.
      
Lemma comp0 : forall (A:Type) (f : A -> A -> A) (x : A) (u : nat -> A), comp f x u 0 = x.
trivial.
Qed.

Lemma compS : forall (A:Type) (f : A -> A -> A) (x : A) (u : nat -> A) (n:nat),
              comp f x u (S n) = f (u n) (comp f x u n).
trivial.
Qed.

(** ** Reducing if constructs *)

Lemma if_then : forall (P:Prop) (b:{P}+{ ~P})(A:Type)(p q:A), P -> (if b then p else q) =p.
destruct b; simpl; intuition.
Qed.

Lemma if_else : forall (P:Prop) (b:{P}+{ ~P})(A:Type)(p q:A), ~P -> (if b then p else q) =q.
destruct b; simpl; intuition.
Qed.

(** ** Classical reasoning *)

Definition class (A:Prop) := ~ ~A -> A.

Lemma class_neg : forall A:Prop, class ( ~ A).
unfold class; intuition.
Qed.

Lemma class_false : class False.
unfold class; intuition.
Qed.
Hint Resolve class_neg class_false: core.

Definition orc (A B:Prop) := forall C:Prop, class C -> (A ->C) -> (B->C) -> C.

Lemma orc_left : forall A B:Prop, A -> orc A B.
red;intuition.
Qed.

Lemma orc_right : forall A B:Prop, B -> orc A B.
red;intuition.
Qed.

Hint Resolve orc_left orc_right: core.

Lemma class_orc : forall A B, class (orc A B).
repeat red; intros.
apply H0; red; intro.
apply H; red; intro. 
apply H3; apply H4; auto.
Qed.

Arguments class_orc : clear implicits.

Lemma orc_intro : forall A B, ( ~A -> ~B -> False) -> orc A B.
intros; apply class_orc; red; intros.
apply H; red; auto.
Qed.

Lemma class_and : forall A B, class A -> class B -> class (A /\ B).
unfold class; intuition.
Qed.

Lemma excluded_middle : forall A, orc A ( ~A).
red; intros.
apply H; red; intro.
intuition.
Qed.

Definition exc (A :Type)(P:A->Prop) := 
   forall C:Prop, class C -> (forall x:A, P x ->C) -> C.

Lemma exc_intro : forall (A :Type)(P:A->Prop) (x:A), P x -> exc P.
red;firstorder.
Qed.

Lemma class_exc : forall (A :Type)(P:A->Prop), class (exc P).
repeat red; intros.
apply H0; clear H0; red; intro.
apply H; clear H; red; intro H2. 
apply H2; intros; auto.
apply H0; apply (H1 x); auto.
Qed.

Lemma exc_intro_class : forall (A:Type) (P:A->Prop), ((forall x, ~P x) -> False) -> exc P.
intros; apply class_exc; red; intros.
apply H; red; intros; auto.
apply H0; apply exc_intro with (x:=x);auto.
Qed.

Lemma not_and_elim_left : forall A B, ~ (A /\ B) -> A -> ~B.
intuition.
Qed.

Lemma not_and_elim_right : forall A B, ~ (A /\ B) -> B -> ~A.
intuition.
Qed.

Hint Resolve class_orc class_and class_exc excluded_middle: core.

Lemma class_double_neg : forall P Q: Prop, class Q -> (P -> Q) -> ~~P -> Q.
intros.
apply (excluded_middle (A:=P)); auto.
Qed.

(** ** Extensional equality *)

Definition feq A B (f g : A -> B) := forall x, f x = g x.

Lemma feq_refl : forall A B (f:A->B), feq f f.
red; trivial.
Qed.

Lemma feq_sym : forall A B (f g : A -> B), feq f g -> feq g f.
unfold feq; auto.
Qed.

Lemma feq_trans : forall A B (f g h: A -> B), feq f g -> feq g h -> feq f h.
unfold feq; intros.
transitivity (g x); auto.
Qed.

Hint Resolve feq_refl: core.
Hint Immediate feq_sym: core.
Hint Unfold feq: core.

Add Parametric Relation (A B : Type) : (A -> B) (feq (A:=A) (B:=B)) 
  reflexivity proved by (feq_refl (A:=A) (B:=B))
  symmetry proved by (feq_sym (A:=A) (B:=B))
  transitivity proved by (feq_trans (A:=A) (B:=B))
as feq_rel.



