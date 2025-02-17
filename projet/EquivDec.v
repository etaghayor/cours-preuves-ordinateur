Require Export Explore.
Import ListNotations.

Module RegEquivDec (Letter : FiniteOrderedType).
Include RegExplore(Letter).

(** Testing whether a regexp has an empty language *)

Definition is_empty r :=
  negb (REs.exists_ is_nullable (exact_derivs r)).

Lemma is_empty_spec r :
  is_empty r = true <-> r === Void.
Proof.
  split; intros.
    - unfold is_empty in H. unfold exact_derivs in H.
Admitted.

(** Now, we can test regexp equivalence via double inclusion *)

Definition is_equiv r r' :=
  is_empty (Or (And r (Not r')) (And r' (Not r))).

Lemma is_equiv_spec r r' :
  is_equiv r r' = true <-> r === r'.
Proof.
  split; intros.
    - unfold is_equiv in H. apply is_empty_spec in H.
    admit.
    - unfold is_equiv. apply is_empty_spec. rewrite H. firstorder.
Admitted.

Lemma equiv_reflect r r' : reflect (r === r') (is_equiv r r').
Proof.
  apply iff_reflect. symmetry. apply is_equiv_spec.
Qed.

Lemma equiv_dec r r' : { r === r' } + { ~ r === r' }.
Proof.
  case (equiv_reflect r r'); [now left | now right].
Qed.

(** Exact list of derivatives up to "===" *)
(** Quadratic algorithm : [(derivs_sim_nb r)^2] calls to [is_equiv]. *)

Definition minimal_derivs r :=
  removedup is_equiv (REs.elements (exact_derivs r)).

Definition derivs_equiv_nb r := length (minimal_derivs r).

(** Of course, we have less derivatives up to [equiv] than
    up to [sim] (and less than the rough upper bound [derivs_bound]). *)

Lemma length_remove_dup {A : Type} f (l: list A) :
  length (removedup f l) <= length l.
Proof.
  induction l.
    - simpl. lia.
    - simpl. case (existsb (f a) (removedup f l)) .
      + apply Nat.le_le_succ_r. assumption.
      + simpl. apply le_n_S. assumption.
Qed.

Lemma derivs_nb_comparison r :
  derivs_equiv_nb r <= derivs_sim_nb r <= derivs_bound r.
Proof.
    unfold derivs_equiv_nb, derivs_sim_nb. 
    unfold minimal_derivs. Search removedup. split. rewrite REs.cardinal_spec.
      - apply length_remove_dup.
      - unfold exact_derivs. case (REs.is_empty (try_exact_derivs r 100)).
        + unfold slow_exact_derivs. unfold try_exact_derivs. simpl.
        Search REs.add. rewrite REsP.singleton_equal_add.
        Search REs.diff.
        
        
        apply REsP.empty_diff_2.
        rewrite <- RegEquivDec.a_set_equation.
  
Admitted.

(** [minimal_derivs] has no duplicates up to [equiv] *)

Lemma minimal_derivs_nodup r : NoDupA equiv (minimal_derivs r).
Proof.
  simpl.
Admitted.

(** [minimal_derivs] is an exact list of derivatives up to [equiv] *)

Lemma minimal_derivs_correct r r' :
 In r' (minimal_derivs r) -> exists w, r' === r//w.
Proof.
Admitted.

Lemma minimal_derivs_complete r :
 AllDerivsInMod equiv r (minimal_derivs r).
Proof.
Admitted.

(** [minimal_derivs] is indeed minimal *)

Lemma minimal_derivs_minimal r l :
 AllDerivsInMod equiv r l -> derivs_equiv_nb r <= length l.
Proof.
Admitted.

(** Note : it is possible to prove that [derivs_equiv_nb r] is the size
    of the smallest deterministic automata recognizing the language of
    [r] (with total transition function).
    And actually the sets of derivatives found above (either modulo
    [sim] or [equal]) could be used as the states of an automata
    (either the minimal one or a good approximate of it).
    The transition are r--a-->r' iff r' =~= r/a (or r' === r/a).
    But that's another story...
*)

(** Note : a simple and fast test of emptyness is possible
    as long as the regexp doesn't contain conjunction or complement.
    But for testing the emptyness of [Not r], we should
    study whether [r] is the full universe or not, and for [And r s]
    we should study whether the languages of [r] and [s] do
    intersect or not. Both questions are non-trivial.
    It has been proved that testing equivalence of regexps with
    [Not] and [And] is of non-elementary complexity.
*)

End RegEquivDec.
