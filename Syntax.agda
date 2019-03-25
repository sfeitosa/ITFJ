import ClassTable as CT

module _ where

open import Data.List hiding (lookup)
open import Data.List.Membership.Propositional
open import Data.Vec 
open import Auxiliary

open import Data.List.Relation.Sublist.Propositional renaming (lookup to lookup-in)

module Syntax {n} (Δ : CT.CTSig n)(wf : ∀{c1 c2} →  c2 ∈ CT.CSig.supers (lookup (CT.Ty.class c1) Δ) → (fields Δ c2) ⊆ (fields Δ c1)) where

  open import Data.Maybe hiding (All)
  open import Data.Product
  open import Data.List.All hiding (lookup)
  
  open CT n
  open Ty
  open CSig
    
  -- Context definition
  
  Ctx : Set
  Ctx = List Ty
  
  -- Subtyping definition
  
  infix 3 _<:_
  
  data _<:_ : Ty → Ty → Set where
    refl : ∀ {τ} → τ <: τ
    exts : ∀ {τ₁ τ₂} → τ₂ ∈ supers (lookup (class τ₁) Δ) → τ₁ <: τ₂
  
  -- Transitivity: used when evaluating casts
  
  postulate
    <:-trans : ∀ {τ₁ τ₂ τ₃} → τ₁ <: τ₂ → τ₂ <: τ₃ → τ₁ <: τ₃
  
  -- Inherently Typed Expression Definition
  
  data Expr (Γ : Ctx) : Maybe Ty → Ty → Set where
    This  : ∀ {c}       → Expr Γ (just c) c
    Var   : ∀ {x τ}     → x ∈ Γ → Expr Γ τ x
    Field : ∀ {c f τ}   → Expr Γ τ c → f ∈ (fields Δ c) → Expr Γ τ f
    Invk  : ∀ {c m τ}   → Expr Γ τ c → m ∈ (signatures Δ c)
      → All (Expr Γ τ) (proj₁ m) → Expr Γ τ (proj₂ m)
    New   : ∀ {τ} c     → All (Expr Γ τ) (fields Δ c) → Expr Γ τ c
    UCast : ∀ {τ C D}   → C <: D → Expr Γ τ C → Expr Γ τ D
  
  
  -- Inherently Typed Values
  
  data Val : Ty → Set where
    VNew : ∀ {C D} → C <: D → All Val (fields Δ C) → Val D
  
  
  -- Used when evaluating fields
  
  postulate 
    liftIdx : ∀ {C D f} → C <: D → All Val (fields Δ C)
      → f ∈ (fields Δ D) → f ∈ (fields Δ C)

  open import Agda.Primitive

  liftIdx' : ∀ {C D f} → C <: D → All Val (fields Δ C) → f ∈ (fields Δ D) → f ∈ (fields Δ C)
  liftIdx' refl l i = i
  liftIdx' {C} {D} (exts x) l i = lookup-in {lzero} {Ty} {fields Δ D} {fields Δ C} (wf {C} {D} x) i
