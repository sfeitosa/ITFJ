import ClassTable as CT

module Syntax {n} (Δ : CT.CTSig n) where

open import Data.List hiding (lookup)
open import Data.Vec 
open import Data.Maybe hiding (All)
open import Data.Product
open import Data.List.All hiding (lookup)
open import Data.List.Membership.Propositional

open CT n
open Ty
open CSig

-- Context definition

Ctx : Set
Ctx = List Ty

-- Subtyping

infix 3 _<:_

data _<:_ : Ty → Ty → Set where
  refl    : ∀ {τ} → τ <: τ
  trans   : ∀ {τ₁ τ₂ τ₃} → τ₁ <: τ₂ → τ₂ <: τ₃ → τ₁ <: τ₃
  extends : ∀ {τ₁} → τ₁ <: super (lookup (class τ₁) Δ)

-- List subtyping

infix 3 _<<:_

data _<<:_ : List Ty → List Ty → Set where
  ε    : [] <<: []
  _∷_ : ∀ {τ₁ τ₂ xs ys} → τ₁ <: τ₂ →  xs <<: ys
                          → τ₁ ∷ xs <<: τ₂ ∷ ys
  
-- Inherently Typed Expression Definition

data Expr (Γ : Ctx) : Maybe Ty → Ty → Set where
  This  : ∀ {c}     → Expr Γ (just c) c
  Var   : ∀ {x τ}   → x ∈ Γ → Expr Γ τ x
  Field : ∀ {c f τ} → Expr Γ τ c → f ∈ flds (lookup (class c) Δ) → Expr Γ τ f
  Invk  : ∀ {c m τ} → Expr Γ τ c → m ∈ signs (lookup (class c) Δ)
                     → All (Expr Γ τ) (proj₁ m) → Expr Γ τ (proj₂ m)
  New   : ∀ {τ} c   → All (Expr Γ τ) (flds (lookup (class c) Δ)) → Expr Γ τ c


-- Inherently Typed Values

data Val : Ty → Set where
  VNew : ∀ c → All Val (flds (lookup (class c) Δ)) → Val c

