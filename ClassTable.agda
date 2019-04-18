open import Data.Nat

module ClassTable (n : ℕ) where

open import Data.Fin
open import Data.List hiding (lookup)
open import Data.Product
open import Data.Vec hiding (_++_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Sublist.Propositional hiding (lookup)

-- Featherweight Java Nominal Types

record Ty : Set where
  field
    class : Fin n

-- Class Signature Definition

record CSig : Set where
  field
    supers : List Ty -- Inheritance Hierarchy 
    flds   : List Ty
    signs  : List (List Ty × Ty)

-- Table with Class Signatures

CTSig : Set
CTSig = Vec CSig n

-- Auxiliary definitions

-- Obtaining fields from a given class

fields : CTSig → Ty → List Ty
fields ξ τ =
  concatMap (λ τ₁ → CSig.flds (lookup (Ty.class τ₁) ξ)) (CSig.supers (lookup (Ty.class τ) ξ)) ++ CSig.flds (lookup (Ty.class τ) ξ)

-- Obtaining method types form a class

signatures : CTSig → Ty → List (List Ty × Ty)
signatures ξ τ =
  concatMap (λ τ₁ → CSig.signs (lookup (Ty.class τ₁) ξ)) (CSig.supers (lookup (Ty.class τ) ξ)) ++ CSig.signs (lookup (Ty.class τ) ξ)

-- Well-formed class table definition

record WFCT : Set where
  field
    ξ : CTSig
    wf-fields :
      ∀ {τ₁ τ₂} → τ₂ ∈ CSig.supers (lookup (Ty.class τ₁) ξ)
                → (fields ξ τ₂) ⊆ (fields ξ τ₁)
    wf-inheritance :
      ∀ {τ₁ τ₂} → τ₂ ∈ CSig.supers (lookup (Ty.class τ₁) ξ)
                 → CSig.supers (lookup (Ty.class τ₂) ξ) ⊆
                    CSig.supers (lookup (Ty.class τ₁) ξ)
