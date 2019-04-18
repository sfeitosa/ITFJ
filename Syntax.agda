import ClassTable as CT

module Syntax {n} (Δ : CT.WFCT n) where

open import Agda.Primitive
open import Data.List hiding (lookup)
open import Data.List.Membership.Propositional
open import Data.Vec 
open import Data.Maybe hiding (All)
open import Data.Product
open import Data.List.All hiding (lookup)
open import Data.List.Relation.Sublist.Propositional renaming (lookup to ∈-lookup)
  
open CT n
open Ty
open CSig
open WFCT
    
-- Context definition
  
Ctx : Set
Ctx = List Ty
  
-- Subtyping definition
  
infix 3 _<:_
  
data _<:_ : Ty → Ty → Set where
  refl : ∀ {τ} → τ <: τ
  exts : ∀ {τ₁ τ₂} → τ₂ ∈ supers (lookup (class τ₁) (ξ Δ)) → τ₁ <: τ₂

-- Inherently Typed Expression Definition
  
data Expr (Γ : Ctx) : Maybe Ty → Ty → Set where
  This  : ∀ {c}     → Expr Γ (just c) c
  Var   : ∀ {x τ}   → x ∈ Γ → Expr Γ τ x
  Field : ∀ {c f τ} → Expr Γ τ c → f ∈ (fields (ξ Δ) c) → Expr Γ τ f
  Invk  : ∀ {c m τ} → Expr Γ τ c → m ∈ (signatures (ξ Δ) c)
                     → All (Expr Γ τ) (proj₁ m) → Expr Γ τ (proj₂ m)
  New   : ∀ {τ} c   → All (Expr Γ τ) (fields (ξ Δ) c) → Expr Γ τ c
  UCast : ∀ {τ C D} → C <: D → Expr Γ τ C → Expr Γ τ D
  
-- Inherently Typed Values
  
data Val : Ty → Set where
  VNew : ∀ {C D} → C <: D → All Val (fields (ξ Δ) C) → Val D
  
-- Used when evaluating fields
  
∈-lift : ∀ {C D f} → C <: D → All Val (fields (ξ Δ) C)
       → f ∈ (fields (ξ Δ) D) → f ∈ (fields (ξ Δ) C)
∈-lift refl l i = i
∈-lift {C} {D} (exts x) l i =
  ∈-lookup {lzero} {Ty} {fields (ξ Δ) D} {fields (ξ Δ) C}
            ((wf-fields Δ) {C} {D} x) i

-- Transitivity: used when evaluating casts

<:-trans : ∀ {τ₁ τ₂ τ₃} → τ₁ <: τ₂ → τ₂ <: τ₃ → τ₁ <: τ₃
<:-trans refl p = p
<:-trans (exts x) refl = exts x
<:-trans {τ₁} {τ₂} {τ₃} (exts x) (exts x') =
  exts (∈-lookup {lzero} {Ty} {supers (lookup (class τ₂) (ξ Δ))}
       {supers (lookup (class τ₁) (ξ Δ))}
       ((wf-inheritance Δ) {τ₁} {τ₂} x) x')
