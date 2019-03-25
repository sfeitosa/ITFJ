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

fields : CTSig → Ty → List Ty
fields Δ τ =
  concatMap (λ τ₁ → CSig.flds (c τ₁)) (CSig.supers (c τ)) ++ CSig.flds (c τ)
  where
    c : Ty → CSig
    c σ = lookup (Ty.class σ) Δ

signatures : CTSig → Ty → List (List Ty × Ty)
signatures Δ τ =
  concatMap (λ τ₁ → CSig.signs (c τ₁)) (CSig.supers (c τ)) ++ CSig.signs (c τ)
  where
    c : Ty → CSig
    c σ = lookup (Ty.class σ) Δ

-- CT definition

record WFCT : Set where
  field
    ξ : CTSig
    wf-fields :
      ∀ {c1 c2} → c2 ∈ CSig.supers (lookup (Ty.class c1) ξ)
                 → (fields ξ c2) ⊆ (fields ξ c1)
    wf-inheritance :
      ∀ {c1 c2} → c2 ∈ CSig.supers (lookup (Ty.class c1) ξ)
                 → CSig.supers (lookup (Ty.class c2) ξ) ⊆
                    CSig.supers (lookup (Ty.class c1) ξ)
