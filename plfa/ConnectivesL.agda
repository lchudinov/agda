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

data _×′_ (A B : Set) : Set where

  ⟨_,_⟩′ :
      A
    → B
      -----
    → A ×′ B
  
proj₁′ : ∀ {A B : Set}
  → A ×′ B
    ------
  → A
proj₁′ ⟨ x , y ⟩′ = x

proj₂′ : ∀ {A B : Set}
  → A ×′ B
    ------
  → B
proj₂′ ⟨ x , y ⟩′ = y

η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ ⟨ x , y ⟩′ = refl

data Bool : Set where
  true  : Bool
  false : Bool
  
data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
  
×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩ = 1
×-count ⟨ true  , bb ⟩ = 2
×-count ⟨ true  , cc ⟩ = 3
×-count ⟨ false , aa ⟩ = 4
×-count ⟨ false , bb ⟩ = 5
×-count ⟨ false , cc ⟩ = 6

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to      = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from    = λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to = λ{ w → refl }
    ; to∘from = λ{ w → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to        = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ } 
    ; from      = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ } 
    ; from∘to   = λ{ w → refl }
    ; to∘from   = λ{ w → refl }
    }
    
-- record _⇔_ (A B : Set) : Set where
--   field
--     to   : A → B
--     from : B → A
    
-- Exercise ⇔≃× (practice)
⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× = 
  record
    { to        = λ{ x → ⟨ (_⇔_.to x)  , (_⇔_.from x) ⟩ } 
    ; from      = λ p → record { to = proj₁ p; from = proj₂ p } 
    ; from∘to   = λ{ w → refl }
    ; to∘from   = λ{ w → refl }
    }
    
