Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.SetoidClass.
Require Import Coq.Classes.Equivalence.

Require Import Quotient.Set.function_util.

Open Scope equiv_scope.

Section Quotient.

  Variable A : Set.
  Variable rel : relation A.
  Variable eqA : Equivalence rel.

  Record isQuotient (X : Set) (proj : A -> X) :=
    {
      quotient_comp : forall (x y : A), x === y -> proj x = proj y;

      quotient_proj_epi : epi proj;

      quotient_factor : forall {B : Set} (f : A -> B), Proper ( equiv ==> eq ) f -> { f' : X -> B | f === f_comp f' proj }
    }.

  Record quotient :=
    {
      quotient_type :>  Set;
      quotient_proj :> A -> quotient_type;

      quotient_isQuotient : isQuotient quotient_type quotient_proj
    }.
  
End Quotient.

Section QuotientUtil.

  Context {A : Set}.
  Context {rel : relation A}.
  Context {eqA : Equivalence rel}.
  Variable X : Set.
  Variable proj : A -> X.

  Variable isQT : isQuotient A rel eqA X proj.
    

End QuotientUtil.

Definition quotient_exists := forall (A : Set) (rel : relation A) (eqA : Equivalence rel), quotient A rel eqA.
