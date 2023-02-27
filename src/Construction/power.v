Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.SetoidClass.
Require Import Coq.Classes.Equivalence.

From Quotient Require Import function_util quotient.
From Quotient.Construction Require Import equalizer coequalizer.

Open Scope equiv_scope.

Program Definition power_setoid {A: Type} : Setoid (A -> bool) := {| setoid_equiv := @pointwise_equivalence A _ eq _ |}.

Definition power_exists := forall (A : Type), quotient (A -> bool) power_setoid.
Class axiom_power_exists :=
  {
    proof_power_exists : power_exists
  }.

Section Power.

  Context {instance_power_exists : axiom_power_exists}.

  Definition power (A : Type) : Type := q_type _ _ (proof_power_exists A).
  Definition to_power {A : Type} : (A -> bool) -> power A := q_proj _ _ (proof_power_exists A).

  Lemma epi_to_power {A} : epi (@to_power A).
  Proof.
    apply quotient_proj_epi.
  Qed.

  Global Instance to_power_Proper {A} : Proper (Equivalence.equiv ==> eq) (@to_power A).
  Proof.
    intros f1 f2 eqf1f2.
    apply quotient_comp.
    assumption.
  Qed.
  
  Section Power_Univ.
    
    Variable A : Type.
    Variable T : Type.
    Variable F : (A -> bool) -> T.
    Variable F_proper : Proper (Equivalence.equiv ==> eq) F.
    
    Definition power_quotient_sig : {f : (power A) -> T | F === f_comp f to_power} :=
      (quotient_factor _ _ (proof_power_exists A))
        F F_proper.

    Definition power_quotient_f : (power A) -> T := proj1_sig power_quotient_sig.
    Definition power_quotient_f_eq : F === f_comp power_quotient_f to_power := proj2_sig power_quotient_sig.
      
  End Power_Univ.

  Section Power_of_power.
    
    Context {A : Type}.
    Definition app_bool_inv : A -> (A -> bool) -> bool := fun a f => f a.
    
    Lemma app_bool_inv_proper : forall a, Proper (Equivalence.equiv ==> eq) (app_bool_inv a).
    Proof.
      intro a.
      intros p1 p2 eqp.
      unfold app_bool_inv.
      apply eqp.
    Qed.
    
    Definition of_power (p : power A) : A -> bool := fun a => power_quotient_f _ _ _ (app_bool_inv_proper a) p.
    
    Lemma of_to_power_eq : forall p, of_power (to_power p) === p.
    Proof.
      intro p.
      unfold of_power.
      intro a.
      transitivity ((app_bool_inv a) p).
      rewrite (power_quotient_f_eq A bool (app_bool_inv a) (app_bool_inv_proper a) p).
      reflexivity.
      reflexivity.
    Qed.
    
    Lemma to_of_power_eq : forall p, to_power (of_power p) = p.
    Proof.
      apply epi_to_power.
      unfold f_comp.
      intro p.
      rewrite of_to_power_eq.
      reflexivity.
    Qed.
    
  End Power_of_power.
  
  Lemma power_extentionality : forall {A} (p1 p2 : power A), (forall a, of_power p1 a = of_power p2 a) -> p1 = p2.
  Proof.
    intros A p1 p2 ext.
    rewrite <- (to_of_power_eq p1).
    rewrite <- (to_of_power_eq p2).
    apply to_power_Proper.
    intro a.
    apply ext.
  Qed.

  Lemma power_extentionality_inv : forall {A} (p1 p2 : power A), p1 = p2 -> (forall a, of_power p1 a = of_power p2 a).
  Proof.
    intros A p1 p2 ext a.
    rewrite ext.
    reflexivity.
  Qed.
  
  Section Power_f.
    
    
    (* power f := S \subType B |-> { a \in A | f(a) \in S } *)
    Definition power_f {A B : Type} (f : A -> B) : (power B) -> (power A) :=
      fun pb => to_power (fun a => (of_power pb) (f a)).
    
    (* power_epsilon A := { S \subType A | a \in S } *)
    Definition power_epsilon (A : Type) : A -> power (power A) :=
      fun a => to_power (fun pa => (of_power pa) a).
    
    Global Instance power_f_Proper {A B : Type} : Proper ( Equivalence.equiv ==> Equivalence.equiv ) (@power_f A B).
    Proof.
      intros f1 f2 eqf.
      intro pb.
      apply power_extentionality.
      intro a.
      unfold power_f.
      rewrite of_to_power_eq.
      rewrite of_to_power_eq.
      rewrite eqf.
      reflexivity.
    Qed.      
    
    Lemma power_f_comp_comm :
      forall {A B C : Type} (f : B -> C) (g : A -> B),
        power_f (f_comp f g) === f_comp (power_f g) (power_f f).
    Proof.
      intros A B C f g.
      intro pc.      
      apply power_extentionality.
      apply f_equiv_eq.
      unfold power_f.
      unfold f_comp.
      intro a.
      rewrite of_to_power_eq.
      rewrite of_to_power_eq.
      rewrite of_to_power_eq.
      reflexivity.
    Qed.
    
    Lemma power_f_id :
      forall {A : Type},
        power_f (@id A) === id.
    Proof.
      intro A.
      unfold power_f.
      intro pa.
      unfold id.
      apply power_extentionality.
      intro a.
      rewrite of_to_power_eq.
      reflexivity.
    Qed.      
    
    Lemma power2_epsilon_natural :
      forall {A B : Type} (f : A -> B),
        f_comp (power_epsilon B) f === f_comp (power_f (power_f f)) (power_epsilon A).
    Proof.
      intros A B f.
      intro a.
      unfold f_comp.
      unfold power_epsilon.
      unfold power_f.
      apply power_extentionality.
      intro pb.
      rewrite of_to_power_eq.
      rewrite of_to_power_eq.
      rewrite of_to_power_eq.
      rewrite of_to_power_eq.
      reflexivity.
    Qed.
    
    Lemma triangle_power_f :
      forall {A B C D : Type} (f : A -> B) (g : B -> D) (h : A -> C) (i : C -> D),
        f_comp g f === f_comp i h -> f_comp (power_f f) (power_f g) === f_comp (power_f h) (power_f i).
    Proof.
      intros A B C D f g h i eqH.
      rewrite <- power_f_comp_comm.
      rewrite <- power_f_comp_comm.
      rewrite eqH.
      reflexivity.
    Qed.
    
    Lemma principle_equalizer_eq :
      forall {A : Type}, f_comp (power_epsilon (power (power A))) (power_epsilon A) === f_comp (power_f (power_f (power_epsilon A))) (power_epsilon A).
    Proof.
      intro A.
      apply power2_epsilon_natural.
    Qed.      
    
    Lemma power_epsilon_unit_counit :
      forall {A : Type},
        f_comp (power_f (power_epsilon A)) (power_epsilon (power A)) === id.
    Proof.
      intro A.
      intro pa.
      unfold f_comp.
      unfold id.
      apply power_extentionality.
      intro a.
      unfold power_f.
      rewrite of_to_power_eq.
      unfold power_epsilon.
      repeat rewrite of_to_power_eq.
      reflexivity.
    Qed.
      
  End Power_f.  

  (* empty *)
  Definition empty_power (A : Type) : power A := to_power (fun a => false).
  Lemma empty_power_false : forall A a, of_power (empty_power A) a = false.
  Proof.
    intros A a.
    unfold empty_power.
    rewrite of_to_power_eq.
    reflexivity.
  Qed.
  Lemma power_f_empty_eq_empty : forall {A B : Type} (f : A -> B), power_f f (empty_power B) === empty_power A.
  Proof.
    intros A B f.
    apply power_extentionality.
    intros a.
    unfold power_f.
    rewrite of_to_power_eq.
    repeat rewrite empty_power_false.
    reflexivity.
  Qed.    

  (* subset *)
  Definition subset {A : Type} (S1 S2 : power A) := forall a, of_power S1 a = true -> of_power S2 a = true.
  Lemma subset_antisym : forall A (S1 S2 : power A), subset S1 S2 -> subset S2 S1 -> S1 = S2.
  Proof.
    unfold subset.
    intros A S1 S2 subH1 subH2.
    apply power_extentionality.
    unfold subset.
    intro a.
    remember (of_power S1 a) as b1.
    destruct b1.
    symmetry.
    apply subH1.
    rewrite Heqb1.
    reflexivity.
    symmetry.
    apply Neqtrue.
    intro HH.
    symmetry in Heqb1.
    apply Neqtrue_inv in Heqb1.
    apply Heqb1.
    apply subH2.
    assumption.
  Qed.
    
  (* Some Axioms *)
  Definition power_reflects_iso :=
    forall (A B : Type) (f : A -> B),
      {Pg | isIsomorphism (power_f f) Pg} ->
      {g | isIsomorphism f g}.
  Definition power_f_faithful :=
    forall (A B : Type) (f1 f2 : A -> B),
      power_f f1 === power_f f2 -> f1 === f2.
  Definition preserve_reflexive_equalizer :=
    forall (A B C : Type) (g : A -> B) (f1 f2 : B -> C) (d : C -> B),
      isEqualizer f1 f2 g ->
      (f_comp d f1 === id /\ f_comp d f2 === id) ->
      isCoequalizer (power_f f1) (power_f f2) (power_f g).

  Class axiom_power_reflects_iso :=
    {
      proof_power_reflects_iso : power_reflects_iso
    }.
  Class axiom_power_f_faithful :=
    {
      proof_power_f_faithful : power_f_faithful
    }.
  Class axiom_preserve_reflexive_equalizer :=
    {
      proof_preserve_reflexive_equalizer : preserve_reflexive_equalizer
    }.

End Power.

