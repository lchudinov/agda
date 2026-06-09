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

-- Truth is unit

record ⊤ : Set where -- \top
  constructor tt

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ w = refl

truth : ⊤
truth = _

data ⊤′ : Set where
  
  tt′ :
    --
    ⊤′

η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ tt′ = refl

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

-- I coudn't make this work
-- ⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
-- ⊤-identityʳ {A} =
--   ≃-begin
--     (A × ⊤)
--   ≃⟨ ×-comm ⟩
--     (⊤ × A)
--   ≃⟨ ⊤-identityˡ ⟩
--     A
--   ≃-∎
  
⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ =
  record
    { to      = λ{ ⟨ x , tt ⟩ → x }
    ; from    = λ{ x → ⟨ x , tt ⟩ }
    ; from∘to = λ{ ⟨ x , tt ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

-- Disjunction is sum

data _⊎_ (A B : Set) : Set where -- \u+
  
  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    ---------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) → 
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infixr 1 _⊎_

⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)   =  1
⊎-count (inj₁ false)  =  2
⊎-count (inj₂ aa)     =  3
⊎-count (inj₂ bb)     =  4
⊎-count (inj₂ cc)     =  5

-- Exercise ⊎-comm (recommended)
-- Show sum is commutative up to isomorphism.

to-prof : ∀ {A B : Set} → A ⊎ B → B ⊎ A
to-prof (inj₁ x) = inj₂ x
to-prof (inj₂ y) = inj₁ y

from-prof : ∀ {A B : Set} → B ⊎ A → A ⊎ B 
from-prof (inj₁ y) = inj₂ y
from-prof (inj₂ x) = inj₁ x

from-to-prof : ∀ {A B : Set} (w : A ⊎ B) → from-prof (to-prof w) ≡ w
from-to-prof (inj₁ x) = refl
from-to-prof (inj₂ x) = refl

to-from-prof : ∀ {A B : Set} (w : B ⊎ A) → to-prof (from-prof w) ≡ w
to-from-prof (inj₁ x) = refl
to-from-prof (inj₂ x) = refl

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = 
  record
    { to        = to-prof 
    ; from      = from-prof 
    ; from∘to   = from-to-prof 
    ; to∘from   = to-from-prof
    }

⊎-comm′ : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm′ =
  record
    { to      = λ { (inj₁ x) → inj₂ x
                  ; (inj₂ y) → inj₁ y }
    ; from    = λ { (inj₁ y) → inj₂ y
                  ; (inj₂ x) → inj₁ x }
    ; from∘to = λ { (inj₁ x) → refl
                  ; (inj₂ y) → refl }
    ; to∘from = λ { (inj₁ y) → refl
                  ; (inj₂ x) → refl }
    }

-- Exercise ⊎-assoc (practice)

to-prof-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C) 
to-prof-assoc (inj₁ (inj₁ x)) = inj₁ x
to-prof-assoc (inj₁ (inj₂ x)) = inj₂ (inj₁ x)
to-prof-assoc (inj₂ x) = inj₂ (inj₂ x) 

from-prof-assoc : ∀ {A B C : Set} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C 
from-prof-assoc (inj₁ x) = inj₁ (inj₁ x)
from-prof-assoc (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
from-prof-assoc (inj₂ (inj₂ x)) = inj₂ x

from-to-prof-assoc : ∀ {A B C : Set} (w : (A ⊎ B) ⊎ C) → from-prof-assoc (to-prof-assoc w) ≡ w
from-to-prof-assoc (inj₁ (inj₁ x)) = refl
from-to-prof-assoc (inj₁ (inj₂ x)) = refl
from-to-prof-assoc (inj₂ x) = refl

to-from-prof-assoc : ∀ {A B C : Set} (w : A ⊎ (B ⊎ C)) → to-prof-assoc (from-prof-assoc w) ≡ w
to-from-prof-assoc (inj₁ x) = refl
to-from-prof-assoc (inj₂ (inj₁ x)) = refl
to-from-prof-assoc (inj₂ (inj₂ x)) = refl

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to = to-prof-assoc
    ; from = from-prof-assoc
    ; from∘to = from-to-prof-assoc
    ; to∘from = to-from-prof-assoc
    }
