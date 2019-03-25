import ClassTable as CT

module Implementation {n} (Δ : CT.WFCT n) where

open import Data.Maybe hiding (All)
open import Data.Product
open import Data.List hiding (lookup)
open import Data.List.All using (All)
open import Data.List.All.Properties
open import Data.Vec.All renaming (All to AllV ; lookup to lookupV)
open import Data.Vec using (lookup)
open import Syntax Δ

open CT n
open Ty
open CSig
open WFCT

-- A class implementation fill the method bodies

record CImpl (τ : Ty) (c : CSig) : Set where
  field
    impls : All (λ s → Expr (proj₁ s) (just τ) (proj₂ s)) (signs c)

open CImpl

-- Associates the class implementation with its signatures

CTImpl : Ty → Set
CTImpl τ = AllV (CImpl τ) (ξ Δ)

-- Auxiliary function to concatenate implementation of superclasses

concatImpl : ∀ {τ} → CTImpl τ → (l : List Ty)
     → All (λ s → Expr (proj₁ s) (just τ) (proj₂ s)) (concatMap (λ s
     → signs (lookup (class s) (ξ Δ))) l)
concatImpl δ [] = All.[]
concatImpl δ (x ∷ xs) = ++⁺ (impls (lookupV (class x) δ)) (concatImpl δ xs)

-- Body method lookup

implementations : ∀ {τ} → CTImpl τ → (C : Ty)
  → All (λ s → Expr (proj₁ s) (just τ) (proj₂ s)) (signatures (ξ Δ) C)
implementations δ C = ++⁺ (concatImpl δ (supers (lookup (class C) (ξ Δ))))
                          (impls (lookupV (class C) δ))






