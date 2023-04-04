Require Export Bool List Equalities Orders Setoid Morphisms.
Import ListNotations.

(** * Languages are sets of words over some type of letters *)

Module Lang (Letter : Typ).

Definition word := list Letter.t.
Definition t := word -> Prop.

Declare Scope lang_scope.
Bind Scope lang_scope with t.
Delimit Scope lang_scope with lang.
Local Open Scope lang_scope.

Implicit Type a : Letter.t.
Implicit Type w x y z : word.
Implicit Type L : t.

Definition eq L L' := forall x, L x <-> L' x.

Definition void : t := fun _ => False.
Definition epsilon : t := fun w => w = [].
Definition singleton a : t := fun w => w = [a].

Definition cat L L' : t :=
  fun x => exists y z, x = y++z /\ L y /\ L' z.
  
Definition union L L' : t := fun w => L w \/ L' w.

Definition inter L L' : t := fun w => L w /\ L' w.

Fixpoint power L n : t :=
  match n with
  | 0 => epsilon
  | S n' => cat L (power L n')
  end.

(** Kleene's star *)

Definition star L : t := fun w => exists n, power L n w.

(** language complement *)

Definition comp L : t := fun w => ~(L w).

(** Languages : notations **)

Module Notations.
Infix "==" := Lang.eq (at level 70).
Notation "∅" := void : lang_scope. (* \emptyset *)
Notation "'ε'" := epsilon : lang_scope. (* \epsilon *)
Coercion singleton : Letter.t >-> Lang.t.
Infix "·" := cat (at level 35) : lang_scope. (* \cdot *)
Infix "∪" := union (at level 50) : lang_scope. (* \cup *)
Infix "∩" := inter (at level 40) : lang_scope. (* \cap *)
Infix "^" := power : lang_scope.
Notation "L ★" := (star L) (at level 30) : lang_scope. (* \bigstar *)
Notation "¬ L" := (comp L) (at level 65): lang_scope. (* \neg *)
End Notations.
Import Notations.

(** Technical stuff to be able to rewrite with respect to "==" *)

Global Instance : Equivalence eq.
Proof. firstorder. Qed.

Global Instance cat_eq : Proper (eq ==> eq ==> eq) cat.
Proof. firstorder. Qed.
Global Instance inter_eq : Proper (eq ==> eq ==> eq) inter.
Proof. firstorder. Qed.
Global Instance union_eq : Proper (eq ==> eq ==> eq) union.
Proof. firstorder. Qed.
Global Instance comp_eq : Proper (eq ==> eq) comp.
Proof. firstorder. Qed.
Global Instance power_eq : Proper (eq ==> Logic.eq ==> eq) power.
Proof.
 intros x x' Hx n n' <-. induction n; simpl; now rewrite ?IHn, ?Hx.
Qed.

Global Instance cat_eq' : Proper (eq ==> eq ==> Logic.eq ==> iff) cat.
Proof. intros x x' Hx y y' Hy w w' <-. now apply cat_eq. Qed.
Global Instance inter_eq' : Proper (eq ==> eq ==> Logic.eq ==> iff) inter.
Proof. intros x x' Hx y y' Hy w w' <-. now apply inter_eq. Qed.
Global Instance union_eq' : Proper (eq ==> eq ==> Logic.eq ==> iff) union.
Proof. intros x x' Hx y y' Hy w w' <-. now apply union_eq. Qed.
Global Instance comp_eq' : Proper (eq ==> Logic.eq ==> iff) comp.
Proof. intros x x' Hy w w' <-. now apply comp_eq. Qed.
Global Instance power_eq' : Proper (eq ==> Logic.eq ==> Logic.eq ==> iff) power.
Proof. intros x x' Hx n n' <- w w' <-. now apply power_eq. Qed.

Global Instance star_eq : Proper (eq ==> eq) star.
Proof.
 intros x x' Hx w. unfold star. now setoid_rewrite <- Hx.
Qed.

Global Instance star_eq' : Proper (eq ==> Logic.eq ==> iff) star.
Proof. intros x x' Hx w w' <-. now apply star_eq. Qed.

(** Languages : misc properties *)

Lemma cat_void_l L : ∅ · L == ∅.
Proof.
  firstorder.
Qed.

Lemma cat_void_r L :  L · ∅ == ∅.
Proof.
  firstorder.
Qed.

Lemma cat_eps_l L : ε · L == L.
Proof.
  intro. split.
    - intros. firstorder. rewrite H0 in H. rewrite H. firstorder.  
    - intros. unfold cat. exists [], x. firstorder.
Qed.

Search "++". 
Lemma cat_eps_r L : L · ε == L.
Proof.
  intro. split; intros; firstorder.
    + rewrite H1 in H. rewrite app_nil_r in H. rewrite H. assumption.
    + exists x,[]. firstorder. rewrite app_nil_r. reflexivity.      
Qed.

Lemma cat_assoc L1 L2 L3 : (L1 · L2) · L3 == L1 · (L2 · L3).
Proof.
  intro. split; intros; firstorder.
    - exists x2, (x3++x1). firstorder.
      rewrite H, H0. apply app_assoc_reverse.
    - exists (x0++x2), x3. firstorder.
      rewrite H, H1. apply app_assoc.
Qed.


Lemma star_eqn L : L★ == ε ∪ L · L ★.
Proof.
  intro. split; intros.
    - firstorder. induction x0; firstorder.
    -  unfold union in H. destruct H.
      + exists 0. firstorder.
      + firstorder.
Admitted.

Lemma star_void : ∅ ★ == ε.
Proof.
  intro. split.
   - intros. firstorder. induction x0; firstorder.
   - intros. unfold star. exists 0. firstorder.
Qed.

Lemma power_eps n : ε ^ n == ε.
Proof.
  intro. split; intros; firstorder.
    - induction n.  
      + firstorder.
      + firstorder. rewrite H0 in H. apply IHn. 
      rewrite app_nil_l in H. rewrite <- H in H1. assumption. 
    - induction n.
      + firstorder.
      + simpl. unfold cat. exists [],x . firstorder.
Qed.

Lemma star_eps : ε ★ == ε.
Proof.
  intro. split; intros; firstorder.
    - induction x0.
      + firstorder.
      + firstorder. apply IHx0. apply power_eps in H1. rewrite H0,H1 in H.
       rewrite H. apply power_eps. firstorder.
    - unfold star. exists 0. firstorder.      
Qed.

Lemma power_app n m y z L :
 (L^n) y -> (L^m) z -> (L^(n+m)) (y++z).
Proof.
  intros.     
Admitted.

Lemma star_star L : (L★)★ == L★.
Proof.
  intro. split; intros; firstorder.
    - admit.
    - exists 1. apply cat_eps_r. exists x0. assumption.     
Admitted.

Lemma cat_star L : (L★)·(L★) == L★.
Proof.
  intro. split; intros; firstorder.
    - admit.
    - unfold cat. exists []. exists x. firstorder. exists 0. firstorder. 
Admitted.

(** ** Derivative of a language : definition **)

Definition derivative L w : t := fun x => L (w++x).

Global Instance derivative_eq : Proper (eq ==> Logic.eq ==> eq) derivative.
Proof. intros L L' HL w w' <-. unfold derivative. intro. apply HL. Qed.

(** ** Derivative of a language : properties **)

Lemma derivative_app L w w' :
  derivative L (w++w') == derivative (derivative L w) w'.
Proof.
  intro. split; intros; firstorder.
    - unfold derivative in *. rewrite app_assoc_reverse in H. assumption.
    - unfold derivative in *. rewrite app_assoc_reverse. assumption.
Qed.

Lemma derivative_cat_null L L' a : L [] ->
  derivative (L · L') [a] == (derivative L [a] · L') ∪ derivative L' [a].
Proof.
  intro. split; intros; firstorder.
    -   unfold cat.  
Admitted.

Lemma derivative_cat_nonnull L L' a : ~L [] ->
  derivative (L · L') [a] == derivative L [a] · L'.
Proof.
  intro. split; intros.
    - firstorder.  unfold cat. unfold derivative in *.
Admitted.

Lemma derivative_star L a :
  derivative (L★) [a] == (derivative L [a]) · (L★).
Proof.
  intro. split; intros; firstorder.
    - unfold cat. unfold derivative. exists x,[].
    rewrite app_nil_r. split.
      + reflexivity.
      + split.
        * admit. (*apply H with (x0 := 1). rewrite H.*)
        * exists 0. firstorder.
    - rewrite H. apply derivative_app. apply derivative_app.   unfold star. 


Admitted.

End Lang.
