Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.SetoidClass.
Require Import Coq.Classes.Equivalence.

Require Import Quotient.Set.function_util.

Open Scope equiv_scope.

Section Quotient.

  Variable A : Set.
  Variable rel : relation A.
  Variable eqA : Equivalence rel.

  Record quotient :=
    {
      q_type :  Set;
      q_proj : A -> q_type;

      (* conditions *)
      quotient_comp : forall (x y : A), x === y -> q_proj x = q_proj y;
      quotient_proj_epi : epi q_proj;
      quotient_factor : forall {B : Set} (f : A -> B), Proper ( equiv ==> eq ) f -> { f' : q_type -> B | f === f_comp f' q_proj }

    }.
  
End Quotient.

Definition quotient_exists := forall (A : Set) (rel : relation A) (eqA : Equivalence rel), quotient A rel eqA.
