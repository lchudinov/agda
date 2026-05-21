-- Connectives: Conjunction, disjunction, and implication
module ConnectivesL where

-- Imports

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ) 
open import Function using (_∘_)
open import IsomorphismL using (_≃_; _≲_; extensionality; _⇔_)
open IsomorphismL.≃-Reasoning

-- Conjunction is product

record _×_ (A B : Set) : Set where
  constructor ⟨_,_⟩
  field
    proj₁ : A
    proj₂ : B
open _×_

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× w = refl

infixr 2 _×_



