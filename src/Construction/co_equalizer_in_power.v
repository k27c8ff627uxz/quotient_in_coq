Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.SetoidClass.
Require Import Coq.Classes.Equivalence.

Require Import Quotient.quotient.
From Quotient.Construction Require Import function_util power equalizer coequalizer construction_of_equalizer.

Open Scope equiv_scope.

Section Co_Equalizer_in_Power.

  Context {instance_power_exists : axiom_power_exists}.
  Context {instance_proof_irrelevance : axiom_proof_irrelevance}.
  Context {instance_power_reflects_iso: axiom_power_reflects_iso}.    
  Context {instance_preserve_reflexive_equalizer : axiom_preserve_reflexive_equalizer}.

  Lemma isCoequalizer_power_epsilon : forall A,
      isCoequalizer
        (power_f (power_epsilon (power (power A))))
        (power_f (power_f (power_f (power_epsilon A))))
        (power_f (power_epsilon A))
  .
  Proof.
    intro A.
    apply splitcoequalizer_coequalizer.
    apply (
        Build_isSplitCoequalizer _ _ _ _ _ _
                                 (power_epsilon (power (power (power A))))
                                 (power_epsilon (power A))
      ).
    {
      rewrite power_epsilon_unit_counit.
      reflexivity.
    } {
      rewrite power2_epsilon_natural.
      reflexivity.
    } {
      rewrite power_epsilon_unit_counit.
      reflexivity.
    } {
      repeat rewrite <- power_f_comp_comm.
      rewrite power2_epsilon_natural.
      reflexivity.
    }
  Qed.

  Lemma epi_power_power_epsilon : forall A, epi (power_f (power_epsilon A)).
  Proof.
    intro A.
    apply (coequalizer_epi _ _ _ (isCoequalizer_power_epsilon A)).
  Qed.
    
  Section IsEqualizerPowerEpsilon.

    Variable A : Set.

    Lemma PEPaEa_eq_PPEaEa : f_comp (power_epsilon (power (power A))) (power_epsilon A) === f_comp (power_f (power_f (power_epsilon A))) (power_epsilon A).
    Proof.
      rewrite power2_epsilon_natural.
      reflexivity.
    Qed.    

    Definition Lkappa_equalizer :=
      construct_equalizer
        (power_epsilon (power (power A)))
        (power_f (power_f (power_epsilon A))).
    Definition L : Set :=
      equalizer_set _ _ Lkappa_equalizer.
    Definition kappa : L -> power (power A) :=
      equalizer_fun _ _ Lkappa_equalizer.
    Definition isEqualizer_PEPaPPEa : isEqualizer (power_epsilon (power (power A))) (power_f (power_f (power_epsilon A))) kappa :=
    equalizer_isequalizer _ _ Lkappa_equalizer.
    Definition PEPakappa_eq_PPEakappa : f_comp (power_epsilon (power (power A))) kappa === f_comp (power_f (power_f (power_epsilon A))) kappa :=
    equalizer_equal _ _ _ isEqualizer_PEPaPPEa.
    Definition Lkappa_equalizer_univ := @equalizer_univ _ _ _ _ _ _ isEqualizer_PEPaPPEa.
(*
    Lemma mono_kappa : mono kappa.
    Proof.
      apply (equalizer_mono _ _ _ isEqualizer_PEPaPPEa).
    Qed.
*)
    Lemma epi_Pkappa : epi (power_f kappa).
    Proof.
      apply (coequalizer_epi (power_f (power_epsilon (power (power A)))) (power_f (power_f (power_f (power_epsilon A))))).
      apply (proof_preserve_reflexive_equalizer _ _ _ _ _ _ (power_f (power_epsilon (power A))) isEqualizer_PEPaPPEa).
      split.
      {
        rewrite power_epsilon_unit_counit.
        reflexivity.
      } {
        rewrite <- power_f_comp_comm.
        rewrite power_epsilon_unit_counit.
        rewrite power_f_id.
        reflexivity.
      }
    Qed.
    
    Definition epsilon'_equalizer_univ := Lkappa_equalizer_univ _ _ PEPaEa_eq_PPEaEa.
    Definition epsilon' : A -> L := proj1_sig epsilon'_equalizer_univ.
    Lemma PEa_eq_kappaepsilon : (power_epsilon A) === f_comp kappa epsilon'.
    Proof.
      generalize (proj2_sig epsilon'_equalizer_univ); intro HH.
      destruct HH as [HH _].
      unfold epsilon'.
      apply HH.
    Qed.

    Lemma Power_PEPakappa_eq_PPEakappa : f_comp (power_f kappa) (power_f (power_epsilon (power (power A)))) === f_comp (power_f kappa) (power_f (power_f (power_f (power_epsilon A)))).
    Proof.
      repeat rewrite <- power_f_comp_comm.
      rewrite PEPakappa_eq_PPEakappa.
      reflexivity.
    Qed.

    Definition isCoequalizer_power_epsilon_univ := (@coequalizer_univ _ _ _ _ _ _ (isCoequalizer_power_epsilon A) _ _ Power_PEPakappa_eq_PPEakappa).

    Definition eta' : power A -> power L := proj1_sig isCoequalizer_power_epsilon_univ.
    Lemma Pkappa_eq_eta'PEa : power_f (kappa) === f_comp eta' (power_f (power_epsilon A)).
    Proof.
      generalize (proj2_sig isCoequalizer_power_epsilon_univ); intro HH.
      destruct HH as [HH _].
      unfold kappa.
      apply HH.
    Qed.

    Lemma PEa_eq_Pepsilon'Pkappa : power_f (power_epsilon A) === f_comp (power_f epsilon') (power_f kappa).
    Proof.
      rewrite <- power_f_comp_comm.
      rewrite PEa_eq_kappaepsilon.
      reflexivity.
    Qed.

    
    Lemma iso_Pe'_eta : isIsomorphism (power_f epsilon') eta'.
    Proof.
      split.
      {
        apply (epi_power_power_epsilon A).
        rewrite f_comp_assoc.
        rewrite <- Pkappa_eq_eta'PEa.
        rewrite <- PEa_eq_Pepsilon'Pkappa.
        rewrite f_comp_id_L.
        reflexivity.
      } {
        apply epi_Pkappa.
        rewrite f_comp_assoc.
        rewrite <- PEa_eq_Pepsilon'Pkappa.
        rewrite <- Pkappa_eq_eta'PEa.
        rewrite f_comp_id_L.
        reflexivity.
      }
    Qed.

    Lemma isEqualizer_power_epsilon :
      isEqualizer
        (power_epsilon (power (power A)))
        (power_f (power_f (power_epsilon A)))
        (power_epsilon A).
    Proof.
      assert(epsilon_iso : {eta'' | isIsomorphism epsilon' eta''}).
      {
        apply proof_power_reflects_iso.
        exists eta'.
        apply iso_Pe'_eta.
      }
      destruct epsilon_iso as [eta'' epsilon_eta_iso].
      destruct epsilon_eta_iso as [epsilon_eta_id eta_epsilon_id].
      destruct (isEqualizer_PEPaPPEa) as [Leq Lunq].
      split.
      now apply PEPaEa_eq_PPEaEa.
      intros C' g' eqf.
      specialize (Lunq _ _ eqf).
      destruct Lunq as [u [eqgku Lunq]].
      exists (f_comp eta'' u).
      split.
      {
        rewrite eqgku.
        rewrite PEa_eq_kappaepsilon.
        rewrite (f_comp_assoc kappa epsilon' _).
        rewrite <- (f_comp_assoc epsilon' eta'').
        rewrite epsilon_eta_id.
        rewrite f_comp_id_L.
        reflexivity.
      } {
        intros u' eqg'.
        cut (f_comp epsilon' u' === u).
        {
          intro equ.
          rewrite <- equ.
          rewrite <- f_comp_assoc.
          rewrite eta_epsilon_id.
          rewrite f_comp_id_L.
          reflexivity.
        }
        apply Lunq.
        rewrite <- f_comp_assoc.
        rewrite <- PEa_eq_kappaepsilon.
        rewrite eqg'.
        reflexivity.
      }
    Qed.

  End IsEqualizerPowerEpsilon.

  Lemma mono_power_epsilon : forall A, mono (power_epsilon A).
  Proof.
    intro A.
    apply (equalizer_mono _ _ _ (isEqualizer_power_epsilon A)).
  Qed.
    
End Co_Equalizer_in_Power.
