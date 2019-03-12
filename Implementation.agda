import ClassTable as CT

module Implementation {n} (Δ : CT.CTSig n) where

open import Data.Maybe hiding (All)
open import Data.Product
open import Data.List.All using (All)
open import Data.Vec.All renaming (All to AllV ; lookup to lookupV)
open import Data.Vec using (lookup)
open import Syntax Δ
open import Auxiliary Δ

open CT n
open Ty
open CSig

-- A class implementation fill the method bodies

record CImpl (τ : Ty) (c : CSig) : Set where
  field
    impls : All (λ s → Expr (proj₁ s) (just τ) (proj₂ s)) (signs c)

-- Associates the class implementation with its signatures

CTImpl : Ty → Set
CTImpl τ = AllV (CImpl τ) Δ

-- Body method lookup

postulate 
  implementations : ∀ {τ} → (C : Ty)
    → All (λ s → Expr (proj₁ s) (just τ) (proj₂ s)) (signatures C)

{-
implementations τ = {!!}
  where
    c : Ty → CSig
    c σ = lookup (class σ) Δ
-}
