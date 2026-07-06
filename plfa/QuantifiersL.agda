module QuantifiersL where

-- Quantifiers: Universals and existentials

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality; ∀-extensionality)
open import Function using (_∘_)

-- Universals

∀-elim : ∀ {A : Set} {B : A → Set}
  → (∀ (x : A) → B x)
  → (M : A)
    --------------------
  → B M
∀-elim L M = L M

-- Exercise ∀-distrib-× (recommended)

-- Show that universals distribute over conjunction:

∀-distrib-×-to : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) → (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-×-to L = ⟨ (λ x → proj₁ (L x)) , (λ x → proj₂ (L x)) ⟩

∀-distrib-×-from : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) × (∀ (x : A) → C x) → (∀ (x : A) → B x × C x)
∀-distrib-×-from w = λ W → ⟨ proj₁ w W , proj₂ w W ⟩

∀-distrib-×-from-to : ∀ {A : Set} {B C : A → Set} →
  (w : (∀ (x : A) → B x) × (∀ (x : A) → C x)) → ∀-distrib-×-to (∀-distrib-×-from w) ≡ w
∀-distrib-×-from-to w = refl

-- postulate
∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
  

∀-distrib-× =
   record
    { to = (λ L → ⟨ (λ x → proj₁ (L x)) , (λ x → proj₂ (L x)) ⟩)
    ; from = (λ w → λ W → ⟨ proj₁ w W , proj₂ w W ⟩)
    ; to∘from = (λ w → refl)
    ; from∘to = (λ w → refl)
    }