
Require Import Coq.Classes.Equivalence.
Require Import Quotient.Set.function_util.
Open Scope equiv_scope.

Section Equalizer.

  Context {A : Set}.
  Context {B : Set}.

  Variable (f1 f2 : B -> A).

  Record isEqualizer {C : Set} (g : C -> B) :=
    {
      equalizer_equal : (f_comp f1 g) === (f_comp f2 g);

      equalizer_univ :
        forall {C' : Set} (g' : C' -> B),
          (f_comp f1 g') === (f_comp f2 g') ->
          { u : C' -> C | g' === (f_comp g u) /\ (forall u' : C' -> C, g' === (f_comp g u') -> u' === u) }
    }.
       
  Record equalizer :=
    {
      equalizer_set :> Set;
      equalizer_fun :> equalizer_set -> B;

      equalizer_isequalizer : isEqualizer equalizer_fun
    }.

  Lemma equalizer_mono : forall {C : Set} (g : C -> B), isEqualizer g -> mono g.
  Proof.
    intros C g isE.
    destruct isE as [eeq euniv].
    intros X h1 h2 eqgh.
    specialize (euniv X).
    assert(eqh1f : f_comp f1 (f_comp g h1) === f_comp f2 (f_comp g h1)).
    {
      rewrite <- f_comp_assoc.
      rewrite eeq.
      reflexivity.
    }
    assert(eqh2f : f_comp f1 (f_comp g h2) === f_comp f2 (f_comp g h2)).
    {
      rewrite <- f_comp_assoc.
      rewrite eeq.
      reflexivity.
    }
    destruct (euniv _ eqh1f) as [u1 [eqg1 g1unv]].
    destruct (euniv _ eqh2f) as [u2 [eqg2 g2unv]].
    cut (u1 === u2).
    {
      intro equ.
      transitivity u1.
      {
        apply g1unv.
        reflexivity.
      }
      rewrite equ.
      symmetry.
      apply g2unv.
      reflexivity.
    }
    apply g2unv.
    rewrite <- eqg1.
    symmetry.
    assumption.
  Qed.

End Equalizer.

Lemma isEqualizer_symmetry :
  forall {A B C : Set} (f1 f2 : B -> A) (g : C -> B),
    isEqualizer f1 f2 g -> isEqualizer f2 f1 g.
Proof.
  intros A B C f1 f2 g isH.
  destruct isH as [isHex isHunq].
  split.
  rewrite isHex.
  reflexivity.
  intros C' g' eqH.
  symmetry in eqH.
  apply (isHunq _ _ eqH).
Qed.

Definition equalizer_exists := forall (B A : Set) (f1 f2 : B -> A), equalizer f1 f2.
    