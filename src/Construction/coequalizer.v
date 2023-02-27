
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.Equivalence.

From Quotient Require Import function_util quotient.
Open Scope equiv_scope.

Section Coequalizer.

  Context {A : Type}.
  Context {B : Type}.

  Variable (f1 f2 : A -> B).

  Record isCoequalizer {C : Type} (g : B -> C) :=
    {
      coequalizer_equal : (f_comp g f1) === (f_comp g f2);

      coequalizer_univ :
        forall {C' : Type} (g' : B -> C'),
          (f_comp g' f1) === (f_comp g' f2) ->
          { u : C -> C' | g' === (f_comp u g) /\ (forall u' : C -> C', g' === (f_comp u' g) -> u' === u) }
    }.
       
  Record coequalizer :=
    {
      coequalizer_set :> Type;
      coequalizer_fun :> B -> coequalizer_set;

      coequalizer_iscoequalizer : isCoequalizer coequalizer_fun
    }.

  Lemma coequalizer_epi : forall {C : Type} (g : B -> C), isCoequalizer g -> epi g.
  Proof.
    intros C g isC.
    destruct isC as [ceq cuniv].
    intros X h1 h2 eqgf.
    specialize (cuniv X).
    assert(eqh1f : f_comp (f_comp h1 g) f1 === f_comp (f_comp h1 g) f2).
    {
      rewrite f_comp_assoc.
      rewrite ceq.
      reflexivity.
    }
    assert(eqh2f : f_comp (f_comp h2 g) f1 === f_comp (f_comp h2 g) f2).
    {
      rewrite f_comp_assoc.
      rewrite ceq.
      reflexivity.
    }
    destruct (cuniv _ eqh1f) as [u1 [eqg1 g1unv]].
    destruct (cuniv _ eqh2f) as [u2 [eqg2 g2unv]].
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

End Coequalizer.

Lemma isCoequalizer_symmetry :
  forall {A B C : Type} (f1 f2 : A -> B) (g : B -> C),
    isCoequalizer f1 f2 g -> isCoequalizer f2 f1 g.
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

Section SplitCoequalizer.


  Record isSplitCoequalizer {A B C : Type} (f g : A -> B) (h : B -> C) :=
    {
      split_coequalizer_s : B -> A;
      split_coequalizer_t : C -> B;

      split_coequalizer_cond1 : f_comp f split_coequalizer_s === id;
      split_coequalizer_cond2 : f_comp g split_coequalizer_s === f_comp split_coequalizer_t h;
      split_coequalizer_cond3 : f_comp h split_coequalizer_t === id;
      split_coequalizer_cond4 : f_comp h f === f_comp h g
                     
    }.

  Lemma splitcoequalizer_coequalizer : forall {A B C : Type} (f g : A -> B) (h : B -> C),
      isSplitCoequalizer f g h -> isCoequalizer f g h.
  Proof.
    intros A B C f g h isH.
    destruct isH as [s t cond1 cond2 cond3 cond4].
    split.
    assumption.
    intros D j eqjffg.
    exists (f_comp j t).
    split.
    {
      rewrite f_comp_assoc.
      rewrite <- cond2.
      rewrite <- f_comp_assoc.
      rewrite <- eqjffg.
      rewrite f_comp_assoc.
      rewrite cond1.
      rewrite f_comp_id_R.
      reflexivity.
    } {
      cut (epi h).
      {
        intros epih k' eqjuh.
        apply epih.
        rewrite eqjuh.
        rewrite f_comp_assoc.
        rewrite f_comp_assoc.
        rewrite <- cond2.
        rewrite <- (f_comp_assoc h g s).
        rewrite <- cond4.
        rewrite f_comp_assoc.
        rewrite cond1.
        rewrite f_comp_id_R.
        reflexivity.
      }
      intros D' k1 k2 eqk.
      cut (f_comp (f_comp k1 h) t === f_comp (f_comp k2 h) t).
      {
        rewrite f_comp_assoc.
        rewrite f_comp_assoc.
        rewrite cond3.
        rewrite f_comp_id_R.
        rewrite f_comp_id_R.
        tauto.
      }
      rewrite eqk.
      reflexivity.
    }
  Qed.
    
End SplitCoequalizer.


Definition coequalizer_exists := forall (A B : Type) (f1 f2 : A -> B), coequalizer f1 f2.

Lemma coequalizer_exists__quotient_exists : coequalizer_exists -> quotient_exists.
Proof.
  intros ce.
  intros A setoid.
  specialize (ce { p : A * A | (fst p) === (snd p)}).
  specialize (ce A).
  specialize (ce (f_comp fst (@proj1_sig _ _))).
  specialize (ce (f_comp snd (@proj1_sig _ _))).
  destruct ce as [X proj IsC].
  assert(epi_proj : epi proj).
  {
    generalize IsC.
    apply coequalizer_epi.
  }    
  destruct IsC as [ceq cuniv].
  unfold f_comp in ceq.
  unfold f_comp in cuniv.
  set (fun p => (fst p) === (snd p)) as P.
  exists X proj.
  {
    intros a1 a2 eqa.
    assert(eqa' : P (a1, a2)).
    {
      unfold P.
      simpl.
      apply eqa.
    }
    specialize (ceq (exist _ (a1, a2) eqa')).
    simpl in ceq.
    assumption.
  }
  assumption.
  {
    intros B f PH.
    specialize (cuniv _ f).
    destruct cuniv as [f' [eqf unvf]].
    {
      intro p.
      destruct p as [p1 p2].
      simpl.
      rewrite p2.
      reflexivity.
    }
    exists f'.
    rewrite eqf.
    unfold f_comp.
    reflexivity.
  }
Qed.
