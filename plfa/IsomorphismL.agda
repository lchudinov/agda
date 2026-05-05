-- Isomorphism: Isomorphism and Embedding

module IsomorphismL where

-- Imports

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

-- Lambda expressions

-- Function composition

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C) --\o
(g ∘ f) x = g (f x)

_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C) --\o
g ∘′ f = λ x → g (f x) -- \lambda

-- Extensionality

