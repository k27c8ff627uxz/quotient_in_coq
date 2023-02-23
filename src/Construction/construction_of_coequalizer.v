Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.SetoidClass.
Require Import Coq.Classes.Equivalence.

Require Import Quotient.function_util.
From Quotient.Construction Require Import equalizer coequalizer construction_of_equalizer power co_equalizer_in_power.

Open Scope equiv_scope.

Section CoequalizerExists.

  Context {instance_proof_irrelevance : axiom_proof_irrelevance}.
  Context {instance_power_exists : axiom_power_exists}.
  Context {instance_preserve_reflexive_equalizer : axiom_preserve_reflexive_equalizer}.
  Context {instance_power_reflects_iso : axiom_power_reflects_iso}.    
  Context {instance_power_f_faithful : axiom_power_f_faithful}.

  Context {B : Type}.
  Context {A : Type}.
  Variable f g : B -> A.

  Definition Vtau_equalizer : equalizer (power_f f) (power_f g)
    := construct_equalizer _ _.
  Definition V : Type :=
    equalizer_set _ _ Vtau_equalizer.
  Definition tau : V -> power A :=
    equalizer_fun _ _ Vtau_equalizer.
  Definition isEqualizer_PfPg : isEqualizer (power_f f) (power_f g) tau :=
    equalizer_isequalizer _ _ Vtau_equalizer.
  Definition Pftau_eq_Pgtau : f_comp (power_f f) tau === f_comp (power_f g) tau :=
    equalizer_equal _ _ _ isEqualizer_PfPg.
  Definition Vtau_equalizer_univ := @equalizer_univ _ _ _ _ _ _ isEqualizer_PfPg.
  Lemma mono_tau : mono tau.
  Proof.
    apply (equalizer_mono _ _ _ isEqualizer_PfPg).
  Qed.
  
  Lemma P3fP2tau_eq_P3gP2tau : f_comp (power_f (power_f (power_f f))) (power_f (power_f tau)) === f_comp (power_f (power_f (power_f g))) (power_f (power_f tau)).
  Proof.
    rewrite <- power_f_comp_comm.
    rewrite <- power_f_comp_comm.
    rewrite <- power_f_comp_comm.
    rewrite <- power_f_comp_comm.
    rewrite Pftau_eq_Pgtau.
    reflexivity.
  Qed.

  Lemma PfPepsilonAP2tau_eq_PgPepsilonAP2tau : f_comp (power_f f) (f_comp (power_f (power_epsilon A)) (power_f (power_f tau))) === f_comp (power_f g) (f_comp (power_f (power_epsilon A)) (power_f (power_f tau))).
  Proof.
    rewrite <- f_comp_assoc.
    rewrite <- f_comp_assoc.
    rewrite (triangle_power_f _ _ _ _ (power2_epsilon_natural f)).
    rewrite (triangle_power_f _ _ _ _ (power2_epsilon_natural g)).
    rewrite f_comp_assoc.
    rewrite f_comp_assoc.
    rewrite P3fP2tau_eq_P3gP2tau.
    reflexivity.
  Qed.


  Definition h_equalizer_univ := Vtau_equalizer_univ _ _ PfPepsilonAP2tau_eq_PgPepsilonAP2tau.
  Definition h : (power (power V)) -> V := proj1_sig h_equalizer_univ.
  Lemma PepsilonAP2tau_eq_tauh : f_comp (power_f (power_epsilon A)) (power_f (power_f tau)) === f_comp tau h.
  Proof.
    generalize (proj2_sig h_equalizer_univ); intro HH.
    destruct HH as [HH _].
    unfold h.
    apply HH.
  Qed.





  Definition Cv_equalizer : equalizer (power_epsilon (power V)) (power_f h)
    := construct_equalizer _ _.
  Definition C : Type :=
    equalizer_set _ _ Cv_equalizer.
  Definition v : C -> power V :=
    equalizer_fun _ _ Cv_equalizer.
  Definition isEqualizer_Cv : isEqualizer (power_epsilon (power V)) (power_f h) v :=
    equalizer_isequalizer _ _ Cv_equalizer.
  Definition epsilonPVv_eq_Phv : f_comp (power_epsilon (power V)) v === f_comp (power_f h) v :=
    equalizer_equal _ _ _ isEqualizer_Cv.
  Definition Cv_equalizer_univ := @equalizer_univ _ _ _ _ _ _ isEqualizer_Cv.
  Lemma mono_v : mono v.
  Proof.
    apply (equalizer_mono _ _ _ isEqualizer_Cv).
  Qed.    
  
  Lemma epsilonPVPtauepsilonA_eq_PhPtauepsilonA : f_comp (power_epsilon (power V)) (f_comp (power_f tau) (power_epsilon A)) === f_comp (power_f h) (f_comp (power_f tau) (power_epsilon A)).
  Proof.
    rewrite <- f_comp_assoc.
    rewrite <- f_comp_assoc.
    rewrite power2_epsilon_natural.
    rewrite <- (triangle_power_f _ _ _ _ PepsilonAP2tau_eq_tauh).
    rewrite f_comp_assoc.
    rewrite f_comp_assoc.
    rewrite principle_equalizer_eq.
    reflexivity.
  Qed.

  
  Definition sigma_equalizer_univ := Cv_equalizer_univ _ _ epsilonPVPtauepsilonA_eq_PhPtauepsilonA.
  Definition sigma : A -> C := proj1_sig sigma_equalizer_univ.
  Lemma PtauepsilonA_eq_vsigma : f_comp (power_f tau) (power_epsilon A) === f_comp v sigma.
  Proof.
    generalize (proj2_sig sigma_equalizer_univ); intro HH.
    destruct HH as [HH _].
    unfold h.
    apply HH.
  Qed.

  Lemma sigmaf_eq_sigmag : f_comp sigma f === f_comp sigma g.
  Proof.
    apply mono_v.
    rewrite <- f_comp_assoc.
    rewrite <- f_comp_assoc.
    rewrite <- PtauepsilonA_eq_vsigma.
    rewrite f_comp_assoc.
    rewrite f_comp_assoc.
    rewrite power2_epsilon_natural.
    rewrite power2_epsilon_natural.
    rewrite <- f_comp_assoc.
    rewrite <- f_comp_assoc.
    rewrite <- power_f_comp_comm.
    rewrite <- power_f_comp_comm.
    rewrite Pftau_eq_Pgtau.
    reflexivity.
  Qed.


  (* Uniqueness *)
  Section Exists_Arrow.

    Variable D : Type.
    Variable r : A -> D.
    Variable rf_eq_rg : f_comp r f === f_comp r g.

    Lemma PfPr_eq_PgPr : f_comp (power_f f) (power_f r) === f_comp (power_f g) (power_f r).
    Proof.
      repeat rewrite <- power_f_comp_comm.
      rewrite rf_eq_rg.
      reflexivity.
    Qed.

    Definition s_univ := (Vtau_equalizer_univ _ _ PfPr_eq_PgPr).
    Definition s : (power D) -> V := proj1_sig s_univ.
    Lemma Pr_eq_taus : (power_f r) === f_comp tau s.
    Proof.
      generalize (proj2_sig s_univ); intro HH.
      destruct HH as [eqH _].
      unfold s.
      rewrite eqH.
      reflexivity.
    Qed.

    Lemma uniq_s : forall s', (power_f r) === f_comp tau s' -> s' === s.
      generalize (proj2_sig s_univ); intro HH.
      destruct HH as [_ unqH].
      unfold s.
      apply unqH.
    Qed.

    Lemma sPEd_eq_hPPs : f_comp s (power_f (power_epsilon D)) === f_comp h (power_f (power_f s)).
    Proof.
      apply mono_tau.
      rewrite <- (f_comp_assoc tau s _).
      rewrite <- Pr_eq_taus.
      rewrite <- power_f_comp_comm.
      rewrite <- (f_comp_assoc tau h _).            
      rewrite <- PepsilonAP2tau_eq_tauh.
      rewrite (f_comp_assoc (power_f (power_epsilon A))).
      rewrite <- power_f_comp_comm.
      rewrite <- power_f_comp_comm.
      rewrite <- power_f_comp_comm.
      rewrite <- Pr_eq_taus.
      apply power_f_Proper.
      rewrite power2_epsilon_natural.
      reflexivity.
    Qed.

    Lemma PPEdPs_eq_PPPsPh : f_comp (power_f (power_f (power_epsilon D))) (power_f s) === f_comp (power_f (power_f (power_f s))) (power_f h).
    Proof.
      repeat rewrite <- power_f_comp_comm.
      rewrite sPEd_eq_hPPs.
      reflexivity.
    Qed.

    Lemma EPPDPsv_eq_PPEdPsv : f_comp (power_epsilon (power (power D))) (f_comp (power_f s) v) === f_comp (power_f (power_f (power_epsilon D))) (f_comp (power_f s) v).
    Proof.
      rewrite <- (f_comp_assoc (power_epsilon _) (power_f s) v).
      rewrite power2_epsilon_natural.
      rewrite (f_comp_assoc (power_f _) (power_epsilon _) v).
      rewrite epsilonPVv_eq_Phv.
      rewrite <- (f_comp_assoc _ (power_f h) v).
      rewrite <- PPEdPs_eq_PPPsPh.
      rewrite (f_comp_assoc _ (power_f s) v).
      reflexivity.
    Qed.


    Definition isEqualizer_power_epsilon_D := isEqualizer_power_epsilon D.
    Definition u_univ := @equalizer_univ _ _ _ _ _ _ (isEqualizer_power_epsilon_D) _ _ EPPDPsv_eq_PPEdPsv.
    Definition u : C -> D := proj1_sig u_univ.
    Lemma Psv_eq_Edu : f_comp (power_f s) v === f_comp (power_epsilon D) u.
    Proof.
      generalize (proj2_sig u_univ); intro HH.
      destruct HH as [eqH _].
      unfold v.
      rewrite eqH.
      reflexivity.
    Qed.


    Lemma r_eq_usigma : r === f_comp u sigma.
    Proof.
      apply (mono_power_epsilon D).
      rewrite power2_epsilon_natural.
      rewrite Pr_eq_taus.
      rewrite power_f_comp_comm.
      rewrite f_comp_assoc.
      rewrite PtauepsilonA_eq_vsigma.
      rewrite <- (f_comp_assoc _ v sigma).
      rewrite Psv_eq_Edu.
      rewrite (f_comp_assoc _ u sigma).
      reflexivity.
    Qed.

    Section Uniqueness.

      Variable u1 u2 : C -> D.
      Variable u1sigma_eq_r : f_comp u1 sigma === r.
      Variable u2sigma_eq_r : f_comp u2 sigma === r.

      Lemma hEv_eq_id : f_comp h (power_epsilon V) === id.
      Proof.
        apply mono_tau.
        rewrite f_comp_id_R.
        rewrite <- f_comp_assoc.
        rewrite <- PepsilonAP2tau_eq_tauh.
        rewrite f_comp_assoc.
        rewrite <- power2_epsilon_natural.
        rewrite <- f_comp_assoc.
        rewrite power_epsilon_unit_counit.
        rewrite f_comp_id_L.
        reflexivity.
      Qed.

      Lemma hPPh_eq_hPEPv : f_comp h (power_f (power_f h)) === f_comp h (power_f (power_epsilon (power V))).
      Proof.
        apply mono_tau.
        transitivity (f_comp (f_comp (power_f (power_epsilon A)) (power_f (power_f tau))) (power_f (power_f h))).
        {
          rewrite <- f_comp_assoc at 1.
          rewrite <- PepsilonAP2tau_eq_tauh.
          reflexivity.
        }
        transitivity (f_comp (power_f (power_epsilon A)) (f_comp (power_f (power_f (power_f (power_epsilon A)))) (power_f (power_f (power_f (power_f tau)))))).
        {
          rewrite f_comp_assoc at 1.
          rewrite <- (power_f_comp_comm (power_f h) (power_f tau)).
          rewrite <- (power_f_comp_comm tau h).
          rewrite <- PepsilonAP2tau_eq_tauh.
          rewrite (power_f_comp_comm (power_f (power_epsilon A)) (power_f _)).
          rewrite power_f_comp_comm.
          reflexivity.
        }
        transitivity (f_comp (power_f (power_epsilon A)) (f_comp (power_f (power_epsilon (power (power A)))) (power_f (power_f (power_f (power_f tau)))))).
        {
          repeat rewrite <- f_comp_assoc.
          rewrite <- power_f_comp_comm.
          rewrite <- principle_equalizer_eq.
          rewrite power_f_comp_comm.
          reflexivity.
        }
        transitivity (f_comp (power_f (power_epsilon A)) (f_comp (power_f (power_f tau)) (power_f (power_epsilon (power V))))).
        {
          rewrite <- power_f_comp_comm at 1.
          rewrite <- power2_epsilon_natural.
          rewrite power_f_comp_comm at 1.
          reflexivity.
        }
        rewrite <- f_comp_assoc.
        rewrite PepsilonAP2tau_eq_tauh.
        rewrite f_comp_assoc.
        reflexivity.
      Qed.

      Lemma isCoequalizerPV : isCoequalizer (power_f (power_f h)) (power_f (power_epsilon (power V))) h.
      Proof.
        apply isCoequalizer_symmetry.
        apply splitcoequalizer_coequalizer.
        apply (Build_isSplitCoequalizer _ _ _ _ _ _ (power_epsilon (power (power V))) (power_epsilon V)).
        {
          rewrite power_epsilon_unit_counit.
          reflexivity.
        } {          
          rewrite power2_epsilon_natural.
          reflexivity.
        } {
          rewrite hEv_eq_id.
          reflexivity.
        } {
          rewrite hPPh_eq_hPEPv.
          reflexivity.
        }
      Qed.

      Lemma isCoequalizerPVC : isCoequalizer (power_f (power_f h)) (power_f (power_epsilon (power V))) (power_f v).
      Proof.
        apply isCoequalizer_symmetry.
        apply (proof_preserve_reflexive_equalizer _ _ _ _ _ _ (power_f (power_epsilon V)) isEqualizer_Cv).
        split.
        {
          rewrite power_epsilon_unit_counit.
          reflexivity.
        } {
          rewrite <- power_f_comp_comm.          
          rewrite hEv_eq_id.
          rewrite power_f_id.
          reflexivity.
        }
      Qed.

      Lemma epi_h : epi h.
      Proof.
        apply (coequalizer_epi _ _ _ isCoequalizerPV).
      Qed.

      Lemma epi_Pv : epi (power_f v).
        apply (coequalizer_epi _ _ _ isCoequalizerPVC).
      Qed.
      
      Lemma PvPEPV_eq_PvPPh : f_comp (power_f v) (power_f (power_f h)) === f_comp (power_f v) (power_f (power_epsilon (power V))).
      Proof.
        repeat rewrite <- power_f_comp_comm.
        rewrite epsilonPVv_eq_Phv.
        reflexivity.
      Qed.        

      Definition q_univ := @coequalizer_univ _ _ _ _ _ _ isCoequalizerPVC _ _ hPPh_eq_hPEPv.
      Definition qinv_univ := @coequalizer_univ _ _ _ _ _ _ isCoequalizerPV _ _ PvPEPV_eq_PvPPh.

      Definition q : power C -> V := proj1_sig q_univ.
      Lemma h_eq_qPv : h === f_comp q (power_f v).
        generalize (proj2_sig q_univ); intro HH.
        destruct HH as [HH _].
        unfold q.
        apply HH.
      Qed.

      Definition qinv : V -> power C := proj1_sig qinv_univ.
      Lemma Pv_eq_qinvh : power_f v === f_comp qinv h.
        generalize (proj2_sig qinv_univ); intro HH.
        destruct HH as [HH _].
        unfold qinv.
        apply HH.
      Qed.

      Lemma qqinv_eq_id : f_comp q qinv === id.
      Proof.
        apply epi_h.
        rewrite f_comp_id_L.
        rewrite f_comp_assoc.
        rewrite <- Pv_eq_qinvh.
        rewrite <- h_eq_qPv.
        reflexivity.
      Qed.        

      Lemma qinvq_eq_id : f_comp qinv q === id.
      Proof.
        apply epi_Pv.
        rewrite f_comp_id_L.
        rewrite f_comp_assoc.
        rewrite <- h_eq_qPv.
        rewrite <- Pv_eq_qinvh.
        reflexivity.
      Qed.
        
      Lemma tauq_eq_Psigma : f_comp tau q === power_f sigma.
      Proof.
        apply epi_Pv.
        rewrite (f_comp_assoc tau q).
        rewrite <- h_eq_qPv.
        rewrite <- PepsilonAP2tau_eq_tauh.
        rewrite <- power_f_comp_comm.
        rewrite PtauepsilonA_eq_vsigma.
        rewrite power_f_comp_comm.
        reflexivity.
      Qed.

      Lemma tau_eq_Psigmaqinv : tau === f_comp (power_f sigma) qinv.
      Proof.
        transitivity (f_comp (f_comp tau q) qinv).
        {
          rewrite f_comp_assoc.
          rewrite qqinv_eq_id.
          rewrite f_comp_id_R.
          reflexivity.
        }
        rewrite tauq_eq_Psigma.
        reflexivity.
      Qed.

      Lemma qPu1_eq_s : f_comp q (power_f u1) === s.
      Proof.
        apply uniq_s.
        rewrite <- f_comp_assoc.
        rewrite tauq_eq_Psigma.
        rewrite <- power_f_comp_comm.
        rewrite u1sigma_eq_r.
        reflexivity.
      Qed.

      Lemma qPu2_eq_s : f_comp q (power_f u2) === s.
      Proof.
        apply uniq_s.
        rewrite <- f_comp_assoc.
        rewrite tauq_eq_Psigma.
        rewrite <- power_f_comp_comm.
        rewrite u2sigma_eq_r.
        reflexivity.
      Qed.

      Lemma Pu1_eq_Pu2 : power_f u1 === power_f u2.
      Proof.
        transitivity (f_comp qinv (f_comp q (power_f u1))).
        {
          rewrite <- f_comp_assoc.
          rewrite qinvq_eq_id.
          rewrite f_comp_id_L.
          reflexivity.
        }
        rewrite qPu1_eq_s.
        rewrite <- qPu2_eq_s.
        rewrite <- f_comp_assoc.
        rewrite qinvq_eq_id.
        rewrite f_comp_id_L.
        reflexivity.
      Qed.

      Lemma u1_eq_u2 : u1 === u2.
        apply proof_power_f_faithful.
        exact Pu1_eq_Pu2.
      Qed.      
      
    End Uniqueness.

  End Exists_Arrow.

  Theorem isCoequalizerC : isCoequalizer f g sigma.
  Proof.
    split.
    exact sigmaf_eq_sigmag.
    intros D r eq_rf_rg.
    set (u D r eq_rf_rg) as u1.
    set (r_eq_usigma D r eq_rf_rg : r === f_comp u1 sigma) as eq_r_u1sigma.
    exists u1.
    split.
    exact (r_eq_usigma D r eq_rf_rg).
    intros u2 eq_r_u2sigma.
    apply (u1_eq_u2 D r eq_rf_rg).
    rewrite eq_r_u2sigma.
    reflexivity.
    rewrite eq_r_u1sigma.
    reflexivity.
  Qed.

  Definition construct_coequalizer : coequalizer f g :=
    {|
      coequalizer_set := C;
      coequalizer_fun := sigma;
      coequalizer_iscoequalizer := isCoequalizerC
    |}.
    
End CoequalizerExists.

Theorem XX__coequalizer_exists :
  axiom_proof_irrelevance ->
  forall instance_power_exists : axiom_power_exists,
    axiom_preserve_reflexive_equalizer ->
    axiom_power_reflects_iso ->
    axiom_power_f_faithful ->
    coequalizer_exists.
Proof.
  intros PEM APE APRE APRI APF.
  intros B A f1 f2.
  apply construct_coequalizer.
Qed.
    
