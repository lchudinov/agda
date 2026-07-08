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
    
-- Exercise ⊎∀-implies-∀⊎ (practice)
-- Show that a disjunction of universals implies a universal of disjunctions:

-- postulate
⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ w) x = inj₁ (w x)
⊎∀-implies-∀⊎ (inj₂ w) x = inj₂ (w x)

-- Exercise ∀-× (practice)
-- Consider the following type.

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
  
∀-×-to : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) → B aa × B bb × B cc
∀-×-to w = ⟨ w aa , ⟨ w bb , w cc ⟩ ⟩

∀-×-from : ∀ {B : Tri → Set} → B aa × B bb × B cc → (∀ (x : Tri) → B x)
∀-×-from ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ = λ { aa → Baa ; bb → Bbb ; cc → Bcc }

-- ∀-×-from : ∀ {B : Tri → Set} → B aa × B bb × B cc → (∀ (x : Tri) → B x)
-- ∀-×-from ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ = λ
--   { aa → Baa
--   ; bb → Bbb
--   ; cc → Bcc
--   }

∀-× : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-× = 
  record
    { to = (λ w → ⟨ w aa , ⟨ w bb , w cc ⟩ ⟩ )
    ; from = (λ { ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ → λ { aa → Baa ; bb → Bbb ; cc → Bcc } })
    ; to∘from = λ { w → refl }
    ; from∘to = λ w →
        ∀-extensionality λ
          { aa → refl
          ; bb → refl
          ; cc → refl
          }
    }      