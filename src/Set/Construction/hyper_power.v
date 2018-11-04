Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.SetoidClass.
Require Import Coq.Classes.Equivalence.

Require Import ChoiceFacts ClassicalFacts.
From Quotient.Set Require Import function_util quotient.
From Quotient.Set.Construction Require Import equalizer coequalizer power.

Open Scope type_scope.

Section HyperPower.

  Variable proof_ConstructiveDefiniteDescription : ConstructiveDefiniteDescription.
  Variable proof_excluded_middle : excluded_middle.
  Context {instance_power_exists : axiom_power_exists}.
  
  Lemma proof_hyper_excluded_middle : forall (P : Prop), {P} + {~P}.
  Proof.
    apply constructive_definite_descr_excluded_middle; assumption.
  Qed.
  
  Definition Prop2bool (P : Prop) : bool := if (proof_hyper_excluded_middle P) then true else false.
  
  Lemma Prop2bool_true : forall P, Prop2bool P = true -> P.
  Proof.
    intro P.
    unfold Prop2bool.
    set (proof_hyper_excluded_middle P) as b.
    destruct b.
    intro.
    assumption.
    intro eqNH.
    discriminate.
  Qed.
    
  Lemma Prop2bool_true_inv : forall (P : Prop), P -> Prop2bool P = true.
  Proof.
    intros P p.
    unfold Prop2bool.
    set (proof_hyper_excluded_middle P) as PP.
    destruct PP.
    reflexivity.
    tauto.
  Qed.

  Section ClassicalFacts.
    
    Lemma PEM : forall P, P \/ ~P.
    Proof.
      intro P.
      remember (Prop2bool P) as b.
      destruct b.
      symmetry in Heqb.
      apply Prop2bool_true in Heqb.
      left.
      assumption.
      right.
      intro pH.
      symmetry in Heqb.
      apply Neqtrue_inv in Heqb.
      apply Heqb.
      apply Prop2bool_true_inv.
      assumption.
    Qed.      
      
    Lemma DNE : forall P, ~~P -> P.
    Proof.
      intro P.
      intro NPH.
      destruct (PEM P).
      assumption.
      tauto.
    Qed.
    
    Lemma de_morgan_foralln : forall {A} (P : A -> Prop), ~(forall x, ~P x) -> (exists x, P x).
    Proof.
      intros A P NF.
      apply DNE.
      intro NEP.
      apply NF.
      intro x.
      intro PxH.
      apply NEP.
      exists x.
      assumption.
    Qed.

  End ClassicalFacts.


  Definition singleton {A : Set} a : power A :=
    to_power (fun a' => Prop2bool (a' = a)).

  Lemma inSingleton : forall {A : Set} (a a' : A), of_power (singleton a) a' = true -> a' = a.
    intros A a a'.
    unfold singleton.
    rewrite of_to_power_eq.
    intro HH.
    apply Prop2bool_true in HH.
    assumption.
  Qed.

  Lemma inSingleton_inv : forall {A : Set} (a a' : A), a' = a -> of_power (singleton a) a' = true.
  Proof.
    intros A a a' eqa.
    unfold singleton.
    rewrite of_to_power_eq.
    apply Prop2bool_true_inv.
    assumption.
  Qed.
  
  Lemma singleton_true : forall {A : Set} (a : A), of_power (singleton a) a = true.
  Proof.
    intros A a.
    apply inSingleton_inv.
    reflexivity.
  Qed.    
  
  Definition power_image {A B : Set} (f : A -> B) : power A -> power B :=
    fun (S : power A) =>
      to_power (
          fun (b : B) => Prop2bool
                           (exists a, (of_power S a = true /\ f a = b))
               ).
  
  Lemma power_image_of_power : forall {A B : Set} (f : A -> B) (pa : power A),
      forall b, (of_power (power_image f pa) b = true) <-> (exists a, of_power pa a = true /\ f a = b).
  Proof.
    intros A B f S b.
    split.
    {
      unfold power_image.
      rewrite of_to_power_eq.
      intro HH.
      apply Prop2bool_true in HH.
      assumption.
    } {
      intros HH.
      destruct HH as [a [Insa eqfab]].
      unfold power_image.
      rewrite of_to_power_eq.
      apply Prop2bool_true_inv.
      exists a.
      split; assumption.
    }
  Qed.

  Section Proof_preserve_reflexive_equalizer.

    Lemma PfIf_eq_id : forall (A B : Set) (f : A -> B), mono f -> f_comp (power_f f) (power_image f) === id.
    Proof.
      intros A B f mono_f.
      intro pa.
      unfold f_comp.
      unfold id.
      apply power_extentionality.
      intro a.
      unfold power_f.
      rewrite of_to_power_eq.
      remember (of_power pa a) as b.
      destruct b.
      {
        apply power_image_of_power.
        exists a.
        split.
        rewrite Heqb.
        reflexivity.
        reflexivity.
      } {
        apply Neqtrue.
        intro opt.
        apply power_image_of_power in opt.
        destruct opt as [a' [eqot eqfa]].
        assert(eqa : a' = a).
        {
          generalize eqfa.
          apply mono_injection.
          assumption.
        }
        rewrite eqa in eqot.
        rewrite eqot in Heqb.
        discriminate.
      }
    Qed.
    
    
    Definition pullback {A B C D : Set} (g1 : A -> B) (f1 : B -> D) (g2 : A -> C) (f2 : C -> D) :=
      f_comp f1 g1 === f_comp f2 g2 /\ (
        forall (A' : Set) (g1' : A' -> B) (g2' : A' -> C),
          f_comp f1 g1' === f_comp f2 g2' ->
          exists u : A' -> A, g1' === f_comp g1 u /\ g2' === f_comp g2 u
      ).
    
    Definition CPullback {X1 X2 Y : Set} (f1 : X1 -> Y) (f2 : X2 -> Y) :=
      { p : X1 * X2 | f1 (fst p) = f2 (snd p) }.
    
    Lemma pullback_comm_in_image :
      forall (Y1 Y2 X1 X2 : Set)
             (f : X1 -> X2) (g : Y1 -> Y2) (j : Y1 -> X1) (i : Y2 -> X2),
        pullback j f g i -> mono i -> mono j ->
        f_comp (power_f f) (power_image i) === f_comp (power_image j) (power_f g).
    Proof.
      intros Y1 Y2 X1 X2 f g j i pullbackH mono_i mono_j.
      destruct pullbackH as [fj_eq_ih univ].
      set (CPullback i f) as A'.
      set ( fun (a : A') => snd (proj1_sig a) ) as g1'.
      set ( fun (a : A') => fst (proj1_sig a) ) as g2'.
      assert(fg1'_eq_fg2' : f_comp f g1' === f_comp i g2').
      {
        intro a.
        unfold g1'.
        unfold g2'.
        unfold f_comp.
        destruct a as [p eqp].
        destruct p as [y2 x1].
        simpl.
        simpl in eqp.
        rewrite eqp.
        reflexivity.
      }
      destruct (univ _ _ _ fg1'_eq_fg2') as [u [eqg1' eqg2']].
      intro s.
      unfold f_comp.
      apply power_extentionality.
      intro x.
      unfold power_f.
      rewrite of_to_power_eq.
      remember (of_power (power_image i s) (f x)) as b.
      destruct b.
      {
        symmetry in Heqb.
        apply power_image_of_power in Heqb.
        destruct Heqb as [y [Insa eqax]].
        symmetry.
        apply power_image_of_power.
        set (exist _ (pair y x) eqax : A') as a.
        exists (u a).
        split.
        {
          rewrite of_to_power_eq.
          specialize (eqg2' a).
          unfold f_comp in eqg2'.
          rewrite <- eqg2'.
          unfold g2'.
          unfold a.
          simpl.
          rewrite Insa.
          reflexivity.
        } {
          specialize (eqg1' a).
          unfold f_comp in eqg1'.
          rewrite <- eqg1'.
          unfold a.
          unfold g1'.
          simpl.
          reflexivity.
        }
      } {
        symmetry.
        apply Neqtrue.
        intro Heqb'.
        symmetry in Heqb.
        apply Neqtrue_inv in Heqb.
        apply Heqb.
        apply power_image_of_power.
        apply power_image_of_power in Heqb'.
        destruct Heqb' as [y [Heqb' jax]].
        rewrite of_to_power_eq in Heqb'.
        exists (g y).
        split.
        rewrite Heqb'.
        reflexivity.
        rewrite <- jax.
        unfold f_comp in fj_eq_ih.
        rewrite fj_eq_ih.
        reflexivity.
      }
    Qed.
    
    Theorem HPEM_preserve_reflexive_equalizer : preserve_reflexive_equalizer.
    Proof.
      intros A B C g f1 f2 d isE split_cond.
      assert(mono_g : mono g).
      {
        apply (equalizer_mono _ _ _ isE).
      }
      destruct isE as [f1g_eq_f2g isE_uniq].
      destruct split_cond as [eqdf1 eqdf2].
      apply splitcoequalizer_coequalizer.
      assert(mono_f1 : mono f1).
      {
        intros D u1 u2 equ.
        cut (f_comp (f_comp d f1) u1 === f_comp (f_comp d f1) u2).
        {
          repeat rewrite eqdf1.
          unfold f_comp.
          unfold id.
          auto.
        }
        repeat rewrite f_comp_assoc.
        rewrite equ.
        reflexivity.
      }
      apply (@Build_isSplitCoequalizer _ _ _ _ _ _ (power_image f1) (power_image g)).
      {
        apply PfIf_eq_id.
        assumption.
      } {
        generalize mono_f1 mono_g.
        apply pullback_comm_in_image.
        split.
        rewrite f1g_eq_f2g.
        reflexivity.
        intros A' g1' g2' f1g_eq_f2g'.
        assert(eqg : g2' === g1').
        {
          cut (f_comp (f_comp d f1) g2' === f_comp (f_comp d f2) g1').
          {
            rewrite eqdf1.
            rewrite eqdf2.
            repeat rewrite f_comp_id_L.
            auto.
          }
          repeat rewrite f_comp_assoc.
          rewrite f1g_eq_f2g'.
          reflexivity.
        }
        rewrite eqg in f1g_eq_f2g'.
        symmetry in f1g_eq_f2g'.
        specialize (isE_uniq _ _ f1g_eq_f2g').
        destruct isE_uniq as [u [Eqg1' Equ]].
        exists u.
        split.
        rewrite Eqg1'.
        reflexivity.
        rewrite eqg.
        rewrite Eqg1'.
        reflexivity.
      } {
        apply PfIf_eq_id.
        exact mono_g.
      } {
        repeat rewrite <- power_f_comp_comm.
        rewrite f1g_eq_f2g.
        reflexivity.
      }
    Qed.
      
  End Proof_preserve_reflexive_equalizer.

  Section Proof_power_f_faithful.

    Theorem HPEM_power_f_faithful : power_f_faithful.
    Proof.
      intros A B f1 f2 eqPf.
      intro a.
      unfold power_f in eqPf.
      specialize (eqPf (singleton (f1 a))).
      simpl in eqPf.
      generalize (power_extentionality_inv _ _ eqPf a); intro eqPf'.
      repeat rewrite of_to_power_eq in eqPf'.
      rewrite singleton_true in eqPf'.
      symmetry in eqPf'.
      apply inSingleton in eqPf'.
      rewrite eqPf'.
      reflexivity.
    Qed.

  End Proof_power_f_faithful.

  Section Proof_axiom_power_reflects_iso.

    Section Proof_axiom_power_reflects_is_Lemmas.

      Variable (A B : Set).
      Variable (f : A -> B).
      Variable (m : power A -> power B).
      Variable mPf_eq_id : f_comp m (power_f f) === id.
      Variable Pfm_eq_id : f_comp (power_f f) m === id.
      
      Lemma Pfm_dest :
        forall S : power A,
        forall a : A,
          of_power (m S) (f a) = of_power S a.
      Proof.
        intro S.
        generalize (Pfm_eq_id S).
        unfold f_comp.
        unfold id.
        intro HH.
        intro a.
        generalize (power_extentionality_inv _ _ HH a); intro HH'.
        unfold power_f in HH'.
        rewrite of_to_power_eq in HH'.
        rewrite HH'.
        reflexivity.
      Qed.      
      
      Lemma mPf_dest :
        forall T : power B,
        forall b : B,
          of_power (m (power_f f T)) b = of_power T b.
      Proof.
        intro T.
        generalize (mPf_eq_id T).
        unfold f_comp.
        unfold id.
        intro HH.
        intro b.
        generalize (power_extentionality_inv _ _ HH b); intro HH'.
        rewrite HH'.
        reflexivity.
      Qed.
      
      Definition U : power B :=
        to_power (fun b => Prop2bool (forall a, ~f a = b)).
      
      Lemma PfU_eq_empty : power_f f U = empty_power A.
      Proof.
        apply power_extentionality.
        intro a.
        unfold power_f.
        rewrite of_to_power_eq.
        unfold U.      
        rewrite of_to_power_eq.
        rewrite empty_power_false.
        apply Neqtrue.
        intro Pt.
        apply Prop2bool_true in Pt.
        apply (Pt a).
        reflexivity.
      Qed.      
      
      Lemma Pfempty_eq_empty : power_f f (empty_power B) = empty_power A.
      Proof.
        apply power_extentionality.
        intros a.
        rewrite power_f_empty_eq_empty.
        repeat rewrite empty_power_false.
        reflexivity.
      Qed.
      
      Lemma U_eq_empty : U = empty_power B.
      Proof.
        cut (f_comp m (power_f f) U = f_comp m (power_f f) (empty_power B)).
        {
          repeat rewrite mPf_eq_id.
          unfold id.
          tauto.
        }
        unfold f_comp.
        rewrite PfU_eq_empty.
        rewrite Pfempty_eq_empty.
        reflexivity.
      Qed.
      
      Lemma surjection_f : forall b, exists a, f a = b.
      Proof.
        intro b.
        apply de_morgan_foralln.
        intro Nfx.
        generalize U_eq_empty; intro U_eqH.
        generalize (power_extentionality_inv _ _ U_eqH b); intro HH.
        rewrite empty_power_false in HH.
        apply Neqtrue_inv in HH.
        apply HH.
        unfold U.
        rewrite of_to_power_eq.
        apply Prop2bool_true_inv.
        exact Nfx.
      Qed.
      
      Lemma injection_f : forall a1 a2, f a1 = f a2 -> a1 = a2.
      Proof.
        intros a1 a2 eqf1.
        apply inSingleton.
        rewrite <- (singleton_true a2).
        repeat rewrite <- Pfm_dest.
        rewrite eqf1.
        reflexivity.
      Qed.
      
      Lemma f_exs_unq : forall b, exists ! a, f a = b.
      Proof.
        intros b.
        destruct (surjection_f b) as [a eqfab].
        exists a.
        split.
        assumption.
        intros a' eqfa'b.
        apply injection_f.
        rewrite eqfab.
        rewrite eqfa'b.
        reflexivity.
      Qed.
      
      Definition g : B -> A :=
        fun b => proj1_sig (proof_ConstructiveDefiniteDescription _ _ (f_exs_unq b)).
      
      Lemma fg_id : f_comp f g === id.
      Proof.
        intro b.
        unfold f_comp.
        unfold id.
        generalize (proj2_sig (proof_ConstructiveDefiniteDescription _ _ (f_exs_unq b))); intro HH.
        unfold g.
        assumption.
      Qed.
      
      Lemma gf_id : f_comp g f === id.
      Proof.
        intro a.
        unfold f_comp.
        unfold id.
        apply injection_f.
        cut (f_comp (f_comp f g) f === f).
        {
          intro eqH.
          apply eqH.
        }
        rewrite fg_id.
        rewrite f_comp_id_L.
        reflexivity.
      Qed.
      
    End Proof_axiom_power_reflects_is_Lemmas.
    
    Theorem HPEM_power_reflects_iso : power_reflects_iso.
    Proof.
      intros A B f HH.
      destruct HH as [m [eq_Pfm eqm_Pf]].
      exists (g _ _ f m eqm_Pf eq_Pfm).
      split.
      rewrite fg_id.
      reflexivity.
      rewrite gf_id.
      reflexivity.
    Qed.
      
  End Proof_axiom_power_reflects_iso.
    
End HyperPower.
