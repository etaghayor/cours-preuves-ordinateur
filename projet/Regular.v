Require Export Languages.
Import ListNotations.

Require Import Btauto.
(** * Regular expressions (regexps) on finite ordered letters *)

Module Type FiniteOrderedType.
 (* Ask for a type [t], an order [lt], a boolean test [eqb], etc *)
 Include UsualOrderedType' <+ HasEqBool.
 (* Moreover, [t] is finite. *)
 Parameter enumeration : list t.
 Parameter enumeration_spec : forall x:t, In x enumeration.
End FiniteOrderedType.

Module Regexps (Letter : FiniteOrderedType).

 (* For LetterB.eqb_spec, LetterB.eqb_neq, ... *)
 Module LetterB := BoolEqualityFacts(Letter).

 Definition word := list Letter.t.

 Implicit Types a : Letter.t.
 Implicit Types w : word.

 (** ** Regexps : definition *)

 Inductive re :=
  | Void : re
  | Epsilon : re
  | Letter : Letter.t -> re
  | Cat : re -> re -> re
  | Star : re -> re
  | Or : re -> re -> re
  | And : re -> re -> re
  | Not : re ->  re.

 (** ** Language of a regexp **)

 Module Lang := Languages.Lang(Letter).
 Import Lang.Notations.
 Open Scope lang_scope.

 Fixpoint lang r : Lang.t :=
  match r with
  | Void => ∅
  | Epsilon => ε
  | Letter a => a
  | Cat r s => lang r · lang s
  | Star r => (lang r)★
  | Or r s => lang r ∪ lang s
  | And r s => lang r ∩ lang s
  | Not r =>  ¬lang r
  end.

 (** ** Nullable regexp : definition **)

 Fixpoint is_nullable (r : re) : bool :=
  match r with
  | Epsilon | Star _ => true
  | Void | Letter _ => false
  | Cat r s | And r s => is_nullable r && is_nullable s
  | Or r s => is_nullable r || is_nullable s
  | Not r => negb (is_nullable r)
  end.

 Lemma nullable_ok r : is_nullable r = true <-> lang r [].
 Proof.
    split.
      - intros. induction r; firstorder.
        + discriminate.
        + discriminate. 
        + simpl in *. apply andb_prop in H. destruct H. rewrite H in IHr1.
        rewrite H0 in IHr2. firstorder.
        + simpl in *. exists 0. simpl. firstorder.
        + simpl in *. apply orb_prop in H. destruct H.
          * rewrite H in IHr1. firstorder.
          * rewrite H in IHr2. firstorder.
        + simpl in *. apply andb_prop in H. destruct H. rewrite H in IHr1.
        rewrite H0 in IHr2. firstorder.
        + simpl in *. apply andb_prop in H. destruct H. rewrite H in IHr1.
        rewrite H0 in IHr2. firstorder.
        + simpl in *. unfold negb in H. destruct (is_nullable r) eqn:H3.
          * discriminate.
          * unfold Lang.comp. apply neg_false. split.
            ** intros. admit.
            ** auto.
      - intros. induction r; auto.
        + inversion H.
        +  simpl in *. firstorder. symmetry in H.
           apply app_eq_nil in H. firstorder. subst. firstorder. 
        + simpl in *. firstorder.
          * rewrite H0. apply orb_true_l.
          * rewrite H0. apply orb_true_r.
        + simpl in *. firstorder.
        + simpl in *. unfold Lang.comp in H. unfold "~" in H.
        unfold negb. destruct (is_nullable r) eqn:H1; auto.
        exfalso. apply H. destruct r; try easy.
          * firstorder.  
        generalize diff_false_true. intros. unfold "<>" in H0.
        symmetry in H1. admit.  
 Admitted.

Lemma nullable_spec r : reflect (lang r []) (is_nullable r).
 Proof.
 apply iff_reflect. symmetry. apply nullable_ok.
 Qed.


 (** ** Derivative of a regular expression **)
 
 Declare Scope re_scope.
 Bind Scope re_scope with re.
 Delimit Scope re_scope with re.
 Open Scope re_scope.

 (** deriv1 : derivative by a letter *)

 Fixpoint deriv1 r a :=
  match r with
  | Void => Void
  | Epsilon => Void
  | Letter a' => if Letter.eqb a a' then Epsilon else Void
  | Cat r s =>
    Or (Cat (deriv1 r a) s) (if is_nullable r then deriv1 s a else Void)
  | Star r => Cat (deriv1 r a) (Star r)
  | Or r s => Or (deriv1 r a) (deriv1 s a)
  | And r s => And (deriv1 r a) (deriv1 s a)
  | Not r => Not (deriv1 r a)
  end.

 Infix "/" := deriv1 : re_scope.

 (** deriv : derivative by a word, ie many letters *)

 Fixpoint deriv r w :=
  match w with
  | [] => r
  | a::w' => deriv (r/a) w'
  end.

 Infix "//" := deriv (at level 40) : re_scope.

 Lemma deriv1_ok r a : lang (r/a) == Lang.derivative (lang r) [a].
 Proof. 
  intro. split.
    - intros. unfold Lang.derivative. 
    
    induction r; firstorder.
      + simpl in *. case (LetterB.eqb_spec a t) in H.
        * rewrite H. rewrite <- e. subst. admit.
        * simpl in *. firstorder.
      + simpl in *. unfold Lang.cat. exists (a::x), []. firstorder.
        * simpl. rewrite app_nil_r. reflexivity.
        * apply IHr1. subst.   admit.
        * admit.
      + admit.
      + admit.
      + admit.
    - intros. unfold Lang.derivative in H. simpl in *. induction r.
        
 Admitted.

 Lemma deriv_ok r w : lang (r//w) == Lang.derivative (lang r) w.
 Proof.
    intro. split.
      - intros. unfold Lang.derivative. induction r; firstorder.
        + simpl in *. unfold Lang.void.  
 Admitted.

 Lemma deriv1_ok' r a w : lang (r/a) w <-> lang r (a::w).
 Proof.
 Admitted.

 Lemma deriv_ok' r w w' : lang (r//w) w' <-> lang r (w++w').
 Proof.
  split.
    - intros. induction r; simpl in *.
      + unfold Lang.void.  
 Admitted.

(** ** Matching : is a word in the language of a regexp ? *)

 Definition matching r w := is_nullable (r//w).

 Lemma matching_ok r w : matching r w = true <-> lang r w.
 Proof.
  split; intros.
    - unfold matching in H.  induction w.
      + simpl in *. apply nullable_ok. assumption.
      + simpl in *. admit. 
    - unfold matching. apply nullable_ok. admit.
 Admitted.

 (** We can now prove that being in [lang r] is decidable *)

 Lemma lang_dec r w : { lang r w } + { ~lang r w }.
 Proof.
 destruct (matching r w) eqn:E; [left|right];
  rewrite <- matching_ok; auto.
 intros E'. now rewrite E' in E.
 Qed.

 (** Derivative of a regexp : properties **)

 Lemma deriv_void w : Void // w = Void.
 Proof.
  induction w; auto.
 Qed.

 Lemma deriv_epsilon w : In (Epsilon // w) [Void; Epsilon].
 Proof.
  induction w.
    - simpl. right. left. reflexivity.
    - simpl in *. left. rewrite deriv_void. reflexivity.
 Qed.

 Lemma deriv_letter a w :
  In (Letter a // w) [Void; Epsilon; Letter a].
 Proof.
  induction w.
    - simpl. right. right. left. reflexivity.
    - simpl. destruct (LetterB.eqb_spec a a0) as [Heq | Hneq].
      + simpl in *.   right. left. rewrite Heq. case LetterB.eqb_spec; intros.
        * admit. 
        * contradiction.
      + left. case LetterB.eqb_spec; intros.
       * symmetry in e. contradiction.
       * symmetry. apply deriv_void.
 Admitted.

 Lemma deriv_or r s w :
  (Or r s) // w = Or (r//w) (s//w).
 Proof.
    induction w.
      - firstorder.  
      - simpl in *.    

  
 Admitted.

 Lemma deriv_and r s w :
  (And r s) // w = And (r // w) (s // w).
 Proof.
    induction w.
      - firstorder.
      - simpl in *. 
 Admitted.

 Lemma deriv_not r w :
  (Not r) // w = Not (r // w).
 Proof.
 Admitted.

 Lemma deriv_app r w w' :
  r // (w++w') = r // w // w'.
 Proof.
 Admitted.

 (** ** Equivalence of regexps *)

 Definition equiv r s := lang r == lang s.

 Infix "===" := equiv (at level 70).

 (** A few technical declarations for being able to rewrite with === *)

 Global Instance : Equivalence equiv.
 Proof. firstorder. Qed.
 Global Instance : Proper (equiv ==> equiv ==> equiv) Or.
 Proof. firstorder. Qed.
 Global Instance : Proper (equiv ==> equiv ==> equiv) And.
 Proof. firstorder. Qed.
 Global Instance : Proper (equiv ==> equiv ==> equiv) Cat.
 Proof. firstorder. Qed.
 Global Instance : Proper (equiv ==> equiv) Not.
 Proof. firstorder. Qed.
 Global Instance : Proper (equiv ==> equiv) Star.
 Proof. intros r r' E. unfold "===" in *. simpl. now rewrite E. Qed.
 Global Instance : Proper (equiv ==> eq) is_nullable.
 Proof. intros r r' E. apply eq_true_iff_eq. rewrite !nullable_ok; auto. Qed.
 Global Instance : Proper (equiv ==> eq ==> equiv) deriv1.
 Proof. intros r r' E a a' <- w. rewrite !deriv1_ok'; auto. Qed.
 Global Instance : Proper (equiv ==> eq ==> equiv) deriv.
 Proof. intros r r' E w w' <- w2. rewrite !deriv_ok'; auto. Qed.
 Global Instance : Proper (equiv ==> eq ==> eq) matching.
 Proof. intros r r' E w w' <-. unfold matching. now rewrite E. Qed.

 Lemma or_comm r s : Or r s === Or s r.
 Proof.
  intro. split; intros; simpl in *; unfold Lang.union in *;
  destruct H; [right | left | right | left]; assumption.
 Qed.

 Lemma or_assoc r s t : Or (Or r s) t === Or r (Or s t).
 Proof.
  intro. split; intros.
    - simpl in *. unfold Lang.union in *. destruct H. destruct H.
      + left. assumption.
      + right. left. assumption.
      + right. right. assumption.
    - simpl in *. unfold Lang.union in *. destruct H. 
      + left. left. assumption.
      + destruct H.
        * left. right. assumption.
        * right. assumption.
 Qed.

 Lemma or_idem r : Or r r === r.
 Proof.
  intro. split; intros; simpl in *.
    - unfold Lang.union in H. destruct H; assumption.
    - unfold Lang.union. left. assumption.
 Qed.

 Lemma or_void_l r : Or Void r === r.
 Proof.
 intro. split; intros; simpl in *.
    - unfold Lang.union in H. destruct H; firstorder.
    - unfold Lang.union. right. assumption.
 Qed.

 Lemma or_void_r r : Or r Void === r.
 Proof.
 intro. split; intros; simpl in *.
  - unfold Lang.union in H. destruct H; firstorder.
  - unfold Lang.union. left. assumption.
 Qed.

 Lemma and_comm r s : And r s === And s r.
 Proof.
 intro. split; intros; simpl in *; 
 unfold Lang.inter in *; split; firstorder.
 Qed.

 Lemma and_assoc r s t : And (And r s) t === And r (And s t).
 Proof.
  intro. split; intros; simpl in *; firstorder.
 Qed.

 Lemma and_idem r : And r r === r.
 Proof.
 intro. split; intros; simpl in *; firstorder.
 Qed.

 Lemma cat_void_l r : Cat Void r === Void.
 Proof.
 intro. split; intros; simpl in *; firstorder.
 Qed.

 Lemma cat_void_r r : Cat r Void === Void.
 Proof.
 intro. split; intros; simpl in *; firstorder.
 Qed.

 Lemma cat_eps_l r : Cat Epsilon r === r.
 Proof.
 intro. split; intros; simpl in *; firstorder.
  - subst. rewrite H0. simpl. assumption.
  - unfold Lang.cat. exists [],x. firstorder.
 Qed.

 Lemma cat_eps_r r : Cat r Epsilon === r.
 Proof.
 intro. split; intros; simpl in *; firstorder.
 - subst. rewrite H1. rewrite app_nil_r. assumption.
 - unfold Lang.cat. exists x,[]. firstorder. rewrite app_nil_r. reflexivity.
 Qed.

 Lemma cat_assoc r s t : Cat (Cat r s ) t === Cat r (Cat s t).
 Proof.
 intro. split; intros; simpl in *; firstorder; unfold Lang.cat in *.
  - exists x2,(x3++x1). split.
    + subst. apply app_assoc_reverse.
    + split.
      * assumption.
      * exists x3,x1; firstorder. 
  - exists (x0++x2),x3. split.
    + subst. rewrite app_assoc_reverse. reflexivity.
    + split.
      * exists x0,x2; firstorder.
      * assumption.
 Qed.


 Lemma star_is_or r : Star r === Or Epsilon (Cat r (Star r)).
 Proof.
 intro. split; intros; simpl in *; firstorder.
  - unfold Lang.cat. unfold Lang.union. apply Lang.star_eqn. firstorder. 
  - exists 0. firstorder. 
  - apply Lang.star_eqn. unfold Lang.union. right. unfold Lang.cat. 
  exists x0,x1. split.
    + assumption.
    + split.
      * assumption.
      * exists x2. assumption.
Qed.

 Lemma star_void : Star Void === Epsilon.
 Proof.
 intro. split; intros; simpl in *. apply Lang.star_void in H.
  - assumption. 
  - apply Lang.star_void. assumption.    
 Qed.

 Lemma star_epsilon : Star Epsilon === Epsilon.
 Proof.
  intro. split; intros; simpl in *; firstorder.
    - apply Lang.power_eps in H. assumption.
    - exists 0. firstorder.  
 Qed.

 Lemma star_star r : Star (Star r) === Star r.
 Proof.
 intro. split; intros; simpl in *; firstorder.
  - apply Lang.star_star. exists x0. assumption.
  - apply Lang.star_star. exists x0. assumption.  
 Qed.

Lemma cat_star r : Cat (Star r) (Star r) === Star r.
Proof.
 intro. split; intros; simpl in *.
  -  firstorder.
    exists (x3+x2). rewrite H. apply Lang.power_app; assumption.
  - firstorder. unfold Lang.cat. exists [],x; firstorder. exists 0. firstorder.
Qed.

End Regexps.
