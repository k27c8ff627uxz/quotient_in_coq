
Require Export Coq.Logic.ClassicalFacts.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Logic.EqdepFacts.

Require Import Quotient.Set.function_util.
Require Import Quotient.Set.Construction.equalizer.

Open Scope equiv_scope.

Class axiom_proof_irrelevance :=
  {
    proof_proof_irrelevance : proof_irrelevance
  }.

Section EqualizerExists.

  Context {instance_proof_irrelevance : axiom_proof_irrelevance}.
  
  Context {A : Set}.
  Context {B : Set}.

  Variable f1 f2 : B -> A.
  
  Definition CEqualizer : Set:=
    { b : B | f1 b = f2 b }.

  Definition CEqualizer_fun : CEqualizer -> B := fun c => proj1_sig c.

  Lemma CEqualizer_fun_eq : f_comp f1 CEqualizer_fun === f_comp f2 CEqualizer_fun.
  Proof.
    unfold CEqualizer_fun.
    unfold f_comp.
    intro c.
    destruct c as [b prf].
    simpl.
    apply prf.
  Qed.

  Lemma CEqualizer_fun_mono : mono CEqualizer_fun.
  Proof.
    assert(CEqualizer_dest : forall c : CEqualizer, c = exist _ (proj1_sig c) (proj2_sig c)).
    {
      apply sig_ind.
      simpl.
      reflexivity.
    }
    assert(eq_dep_eq_sig' : forall (U : Set) (P : U -> Prop) (p q : U) (x : P p) (y : P q),
              eq_dep U P p x q y -> exist P p x = exist P q y).
    {
      intros U P p q x y.
      apply (eq_dep_ind _ _ _ _ (fun (s : U) (z : P s) => exist P p x = exist P s z)).
      reflexivity.
    }
    intros X u1 u2 eqH x.
    generalize (eqH x).
    unfold CEqualizer_fun.
    unfold f_comp.
    intro pH.
    rewrite (CEqualizer_dest (u1 x)).
    rewrite (CEqualizer_dest (u2 x)).
    apply eq_dep_eq_sig'.
    apply eq_dep1_dep.
    symmetry in pH.
    apply (eq_dep1_intro _ _ _ _ _ _ pH).
    apply proof_proof_irrelevance.
  Qed.
  
  Section EqualizerExists_Unq.
    
    Context {C' : Set}.
    Variable (g' : C' -> B).
    Variable eqgf : f_comp f1 g' === f_comp f2 g'.
    
    Definition CEqualizer_factor : C' -> CEqualizer :=
      fun c' => exist _ (g' c') (eqgf c').
    
    Lemma CEqualizer_factor_eq : g' === f_comp CEqualizer_fun CEqualizer_factor.
    Proof.
      unfold CEqualizer_factor.
      unfold CEqualizer_fun.
      unfold f_comp.
      simpl.
      apply fequiv_eta.
    Qed.
    
    Lemma CEqualizer_factor_unq : forall u', g' === f_comp CEqualizer_fun u' -> u' === CEqualizer_factor.
    Proof.
      intros u eqH.
      apply CEqualizer_fun_mono.
      rewrite <- eqH.
      apply CEqualizer_factor_eq.
    Qed.

  End EqualizerExists_Unq.

  Theorem isEqualizer_CEqualizer : isEqualizer f1 f2 CEqualizer_fun.
  Proof.
    split.
    apply CEqualizer_fun_eq.
    intros C' g' eqH.
    exists (CEqualizer_factor g' eqH).
    split.
    apply CEqualizer_factor_eq.
    apply CEqualizer_factor_unq.
  Qed.

  Definition construct_equalizer : equalizer f1 f2 :=
    {|
      equalizer_set := CEqualizer;
      equalizer_fun := CEqualizer_fun;
      equalizer_isequalizer := isEqualizer_CEqualizer
    |}.
    
End EqualizerExists.

Lemma proof_irrelevance__equalizer_exists : proof_irrelevance -> equalizer_exists.
Proof.
  intro pi.
  intros B A f1 f2.
  apply (@construct_equalizer).
  split.
  apply pi.
Qed.  

  