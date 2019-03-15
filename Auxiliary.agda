import ClassTable as CT

module Auxiliary {n} (Δ : CT.CTSig n) where

open import Data.Product
open import Data.List hiding (lookup)
open import Data.Vec hiding (_++_)
open import Data.Vec.All hiding (lookup)

open CT n
open Ty
open CSig

-- Subtyping definition

infix 3 _<:_

postulate 
  _<:_ : Ty → Ty → Set 
{-
  refl    : ∀ {τ} → τ <: τ
  trans   : ∀ {τ₁ τ₂ τ₃} → τ₁ <: τ₂ -> τ₂ <: τ₃ -> τ₁ <: τ₃
  extends : ∀ {τ} → τ <: super (lookup (class τ) Δ)
-}

postulate
  fields : Ty → List Ty
{-
fields τ =
  concatMap (λ τ₁ → flds (c τ₁)) (supers (c τ)) ++ flds (c τ)
  where
    c : Ty → CSig
    c σ = lookup (class σ) Δ
-}

{-
fields' : ∀ {τ₁ τ₂} → τ₁ <: τ₂ → List Ty
fields' {C} refl = flds (lookup (class C) Δ)
fields' (trans sub sub₁) = {!!}
fields' extends = {!!}
-}

postulate 
  signatures : Ty → List (List Ty × Ty)

{-
signatures τ =
  concatMap (λ τ₁ → signs (c τ₁)) (supers (c τ)) ++ signs (c τ)
  where
    c : Ty → CSig
    c σ = lookup (class σ) Δ
-}

