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
    
-- Existentials

record Σ (A : Set) (B : A → Set) : Set where -- \Sigma
  constructor ⟨_,_⟩
  field
    proj₁ : A
    proj₂ : B proj₁

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → Bx) = Σ[ x ∈ A ] Bx

data Σ′ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩′ : (x : A) → B x → Σ′ A B
  
proj₁′ : ∀ {A : Set} {B : A → Set} → Σ′ A B → A
proj₁′ ⟨ x , y ⟩′ = x

proj₂′ : ∀ {A : Set} {B : A → Set} → ∀ (w : Σ′ A B) → B (proj₁′ w)
proj₂′ ⟨ x , y ⟩′ = y

_×′_ : Set → Set → Set
A ×′ B = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set -- \ex
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → refl }
    }
    
-- Exercise ∃-distrib-⊎ (recommended)
-- Show that existentials distribute over disjunction:
∃-distrib-⊎-from : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) → (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎-from ⟨ b , inj₁ x ⟩ = inj₁ ⟨ b , x ⟩
∃-distrib-⊎-from ⟨ b , inj₂ y ⟩ = inj₂ ⟨ b , y ⟩

∃-distrib-⊎-to : ∀ {A : Set} {B C : A → Set} →
  (∃[ x ] B x) ⊎ (∃[ x ] C x) → ∃[ x ] (B x ⊎ C x) 
∃-distrib-⊎-to (inj₁ x) = ⟨ x .Σ.proj₁ , inj₁ (x .Σ.proj₂) ⟩
∃-distrib-⊎-to (inj₂ y) = ⟨ y .Σ.proj₁ , inj₂ (y .Σ.proj₂) ⟩  

∃-distrib-⊎-from-to : ∀ {A : Set} {B C : A → Set} →
  (w : ∃[ x ] (B x ⊎ C x)) →  ∃-distrib-⊎-to (∃-distrib-⊎-from w) ≡ w
∃-distrib-⊎-from-to ⟨ a , inj₁ x ⟩ = refl
∃-distrib-⊎-from-to ⟨ a , inj₂ y ⟩ = refl

∃-distrib-⊎-to-from : ∀ {A : Set} {B C : A → Set} →
  (w : (∃[ x ] B x) ⊎ (∃[ x ] C x)) →  ∃-distrib-⊎-from (∃-distrib-⊎-to w) ≡ w
∃-distrib-⊎-to-from (inj₁ x) = refl
∃-distrib-⊎-to-from (inj₂ y) = refl



∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to      =  ∃-distrib-⊎-from
    ; from    =  ∃-distrib-⊎-to
    ; from∘to =  ∃-distrib-⊎-from-to
    ; to∘from =  ∃-distrib-⊎-to-from
    }