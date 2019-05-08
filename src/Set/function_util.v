
Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.SetoidClass.
Require Export Coq.Classes.Equivalence.

Open Scope equiv_scope.


Section Composition.

  Section Composition_def.
    Context {A B C : Set}.

    Definition f_comp (f : B -> C) (g : A -> B) : A -> C := fun a => f (g a).
  
    Global Instance f_comp_Proper : Proper ( equiv ==> equiv ==> equiv ) f_comp.
    Proof.
      intros f1 f2 eqf.
      intros g1 g2 eqg.
      intro a.
      unfold f_comp.
      rewrite (eqg _).
      rewrite (eqf _).
      reflexivity.
    Qed.

  End Composition_def.

  Context {A B C D : Set}.
  
  Lemma f_comp_assoc : forall (f : C -> D) (g : B -> C) (h : A -> B), f_comp (f_comp f g) h === f_comp f (f_comp g h).
  Proof.
    unfold f_comp.
    reflexivity.
  Qed.
  
  Definition mono (f : A -> B) := forall (X : Set) (u1 u2 : X -> A), f_comp f u1 === f_comp f u2 -> u1 === u2.
  Definition epi (f : A -> B) := forall (X : Set) (u1 u2 : B -> X), f_comp u1 f === f_comp u2 f -> u1 === u2.

  Lemma mono_injection : forall f, mono f -> forall a1 a2, f a1 = f a2 -> a1 = a2.
  Proof.
    intros f monof a1 a2 eqfa.
    cut ( (fun (i : True) => a1) === (fun (i : True) => a2)).
    {
      intro eH.
      apply (eH I).
    }
    apply monof.
    unfold f_comp.
    intro i.
    assumption.
  Qed.

  Lemma injection_mono : forall f, (forall a1 a2, f a1 = f a2 -> a1 = a2) -> mono f.
  Proof.
    intros f cond.
    intros X u1 u2 eqf.
    intro x.
    apply cond.
    apply eqf.
  Qed.
    
End Composition.

Lemma f_comp_id_R : forall {A B : Set} (f : A -> B), f_comp f id === f.
Proof.
  intros.
  unfold id.  
  unfold f_comp.
  intro a.
  reflexivity.
Qed.

Lemma f_comp_id_L : forall {A B : Set} (f : A -> B), f_comp id f === f.
Proof.
  intros.
  unfold id.  
  unfold f_comp.
  intro a.
  reflexivity.
Qed.

Lemma f_equiv_eq : forall {A B} (f1 f2 : A -> B), f1 === f2 -> (forall a, f1 a = f2 a).
Proof.
  auto.
Qed.

Lemma mono_id : forall {A : Set}, mono (@id A).
Proof.
  intro A.
  intros B u1 u2 eqH.
  unfold f_comp in eqH.
  unfold id in eqH.
  intro a.
  apply eqH.
Qed.

Lemma epi_id : forall {A : Set}, epi (@id A).
Proof.
  intro A.
  intros B u1 u2 eqH.
  unfold f_comp in eqH.
  unfold id in eqH.
  intro a.
  apply eqH.
Qed.

Definition isIsomorphism {A B : Set} (f1 : A -> B) (f2 : B -> A) :=
  (f_comp f1 f2 === id) /\ (f_comp f2 f1 === id).

Lemma de_morgan_nexists : forall {A} (P : A -> Prop), (~exists x, P x) -> forall x, ~P x.
Proof.
  intros A P NP.
  intros x Px.
  apply NP.
  exists x.
  assumption.
Qed.

Lemma Neqtrue : forall b, ~b = true -> b = false.
Proof.
  intros b neqbt.
  destruct b.
  elimtype False.
  apply neqbt.
  reflexivity.
  reflexivity.
Qed.

Lemma Neqtrue_inv : forall b, b = false -> ~b = true.
Proof.
  intros b eqbf.
  destruct b.
  discriminate.
  intro eqft.
  discriminate.
Qed.
