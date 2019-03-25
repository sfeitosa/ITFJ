open import Data.Nat

module ClassTable (n : ℕ) where

open import Data.Fin
open import Data.List hiding (lookup)
open import Data.Product
open import Data.Vec

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


