Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.SetoidClass.
Require Import Coq.Classes.Equivalence.

From Quotient.Set Require Import function_util quotient.
From Quotient.Set.Construction Require Import equalizer coequalizer construction_of_equalizer power hyper_power co_equalizer_in_power construction_of_coequalizer.

Open Scope equiv_scope.

Require Import ChoiceFacts ClassicalFacts.

Definition weak_functional_extentionality
  := forall (A : Set) (f1 f2 : A -> bool), (forall a, f1 a = f2 a) -> f1 = f2.
                                                   
Section Conclution.

  Variable proof_weak_functional_extentionality : weak_functional_extentionality.
  Variable proof_ConstructiveDefiniteDescription : ConstructiveDefiniteDescription.
  Variable proof_excluded_middle : excluded_middle.

  Instance instance_power_exists : axiom_power_exists.
  Proof.
    split.
    unfold power_exists.
    intros.
    apply (@Build_quotient _ _ _ (A -> bool) id).
    split.
    intros f1 f2 eqf.
    apply proof_weak_functional_extentionality in eqf.
    unfold id.
    rewrite eqf.
    reflexivity.
    exact epi_id.
    intros B f PropperH.
    exists f.
    rewrite f_comp_id_R.
    reflexivity.
  Qed.
  
  Instance instance_proof_irrelevance : axiom_proof_irrelevance.
  Proof.
    split.
    unfold proof_irrelevance.
    apply proof_irrelevance_cci.
    exact proof_excluded_middle.
  Qed.

  Instance instance_preserve_reflexive_equalizer : axiom_preserve_reflexive_equalizer.
  Proof.
    split.
    apply HPEM_preserve_reflexive_equalizer; assumption.
  Qed.

  Instance instance_power_reflects_iso : axiom_power_reflects_iso.
  Proof.
    split.
    apply HPEM_power_reflects_iso; assumption.
  Qed.
  
  Instance instance_power_f_faithful : axiom_power_f_faithful.
  Proof.
    split.
    apply HPEM_power_f_faithful; assumption.
  Qed.

  Theorem ccc_coequalizer_exists : coequalizer_exists.
  Proof.
    apply (XX__coequalizer_exists
             instance_proof_irrelevance
             instance_power_exists
             instance_preserve_reflexive_equalizer
             instance_power_reflects_iso
             instance_power_f_faithful
          ).
  Qed.

  Theorem ccc_quotient_exists : quotient_exists.
  Proof.
    apply coequalizer_exists__quotient_exists.
    apply ccc_coequalizer_exists.
  Qed.

End Conclution.


Goal
  weak_functional_extentionality ->
  ConstructiveDefiniteDescription ->
  excluded_middle ->
  quotient_exists.
Proof.
  exact ccc_quotient_exists.
Qed.
