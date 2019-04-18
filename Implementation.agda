import ClassTable as CT

module Implementation {n} (Δ : CT.WFCT n) where

open import Data.Nat
open import Data.Fin
open import Data.Maybe hiding (All ; zip)
open import Data.Product hiding (zip)
open import Data.List hiding (lookup ; allFin ; zip)
open import Data.List.All using (All) 
open import Data.List.All.Properties
open import Data.Vec.All renaming (All to AllV ; lookup to lookupV) hiding (zip)
open import Data.Vec 
open import Syntax Δ

open CT n
open Ty
open CSig
open WFCT

-- A class implementation fill the method bodies

record CImpl (τ : Ty) (c : CSig) : Set where
  field
    impls : All (λ s → Expr (proj₁ s) (just τ) (proj₂ s)) (signs c)
    -- over : All (Maybe ...) (signatures (super c)) -- something like that

open CImpl

-- Associates the class implementation with its signatures

CTImpl : Set
CTImpl = AllV (λ s → CImpl (record {class = (proj₁ s)}) (proj₂ s)) (zip (allFin n) (ξ Δ))

-- Auxiliary function to concatenate implementation of superclasses

{-
concatImpl : (τ : Ty) → CTImpl → (l : List Ty)
     → All (λ s → Expr (proj₁ s) (just τ) (proj₂ s))
            (concatMap (λ s → signs (lookup (class s) (ξ Δ))) l)
concatImpl C δ [] = All.[]
concatImpl C δ (x ∷ xs) = ++⁺ (impls (lookupV (class x) δ)) (concatImpl C δ xs)
-}

-- Dynamic dispatch
{-
chooseImpl : ∀ {τ}
          → All {!!} {!!}
          → All {!!} {!!}
          → All {!!} {!!}
chooseImpl b c = {!!}
-}   

-- Body method lookup

{-
implementations : (τ : Ty) → CTImpl
  → All (λ s → Expr (proj₁ s) (just τ) (proj₂ s)) (signatures (ξ Δ) τ)
implementations δ C = ++⁺ (concatImpl δ (supers (lookup (class C) (ξ Δ))))
                          (impls (lookupV (class C) δ))
-}

--postulate
--  implementations : (τ : Ty) → CTImpl
--                 → All (λ s → Expr (proj₁ s) (just τ) (proj₂ s)) (signs (lookup (class τ) (ξ Δ)))
--implementations C δ = impls (lookupV (class C) δ)

postulate
  implementations : (τ : Ty) → CTImpl
    → All (λ s → Expr (proj₁ s) (just τ) (proj₂ s)) (signatures (ξ Δ) τ)
