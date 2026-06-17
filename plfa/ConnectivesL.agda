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

-- False is empty

data ⊥ : Set where -- \bot
  -- no clauses!

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

-- Exercise ⊥-identityˡ (recommended)

⊥-to-prof-l : ∀ {A : Set} → ⊥ ⊎ A → A
⊥-to-prof-l (inj₂ x) = x

⊥-from-prof-l : ∀ {A : Set} → A → ⊥ ⊎ A
⊥-from-prof-l x = (inj₂ x)

⊥-from-to-prof-l : ∀ {A : Set} (w : ⊥ ⊎ A) → ⊥-from-prof-l (⊥-to-prof-l w) ≡ w
⊥-from-to-prof-l (inj₂ x) = refl 

⊥-to-from-prof-l : ∀ {A B : Set} (a : A) → ⊥-to-prof-l (⊥-from-prof-l a) ≡ a
⊥-to-from-prof-l a = refl

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { to      = ⊥-to-prof-l
    ; from    = ⊥-from-prof-l
    ; from∘to = ⊥-from-to-prof-l
    ; to∘from = ⊥-to-from-prof-l
    }
    
-- Exercise ⊥-identity (recommended)

⊥-to-prof-r : ∀ {A : Set} → A ⊎ ⊥ → A
⊥-to-prof-r (inj₁ x) = x

⊥-from-prof-r : ∀ {A : Set} → A → A ⊎ ⊥
⊥-from-prof-r x = (inj₁ x)

⊥-from-to-prof-r : ∀ {A : Set} (w : A ⊎ ⊥) → ⊥-from-prof-r (⊥-to-prof-r w) ≡ w
⊥-from-to-prof-r (inj₁ x) = refl 

⊥-to-from-prof-r : ∀ {A B : Set} (a : A) → ⊥-to-prof-r (⊥-from-prof-r a) ≡ a
⊥-to-from-prof-r a = refl

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ =
  record
    { to      = ⊥-to-prof-r
    ; from    = ⊥-from-prof-r
    ; from∘to = ⊥-from-to-prof-r
    ; to∘from = ⊥-to-from-prof-r
    }

-- Implication is function

→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...              | aa | aa = 1
...              | aa | bb = 2
...              | aa | cc = 3
...              | bb | aa = 4
...              | bb | bb = 5
...              | bb | cc = 6
...              | cc | aa = 7
...              | cc | bb = 8
...              | cc | cc = 9

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → refl }
    }
    
→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
    ; to∘from = λ{ _ → refl }
    }
    
→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
    ; from∘to = λ{ f → refl }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }
    
-- Distribution

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to      = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩)
                 ; ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)
                 }
    ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩ 
                 ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩ 
                 }
    ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
                 ; ⟨ inj₂ y , z ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl 
                 ; (inj₂ ⟨ y , z ⟩) → refl
                 }
    }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ ( inj₁ ⟨ x , y ⟩ ) → ⟨ inj₁ x , inj₁ y ⟩
                 ; ( inj₂ z ) → ⟨ inj₂ z , inj₂ z ⟩
                 }
    ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩) 
                 ; ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z)
                 ; ⟨ inj₂ z , _ ⟩ → (inj₂ z)
                 }
    ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
                 ; (inj₂ z)         → refl
                 }
    }

-- Exercise ⊎-weak-× (recommended)

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , z ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ x , z ⟩ = inj₂ ⟨ x , z ⟩

-- Exercise ⊎×-implies-×⊎ (practice)

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ x , y ⟩) = ⟨ inj₁ x , inj₁ y ⟩
⊎×-implies-×⊎ (inj₂ ⟨ z , k ⟩) = ⟨ inj₂ z , inj₂ k ⟩

-- Does the converse hold? If so, prove; if not, give a counterexample.

-- No, it doesn't hold

-- Standard library
-- Definitions similar to those in this chapter can be found in the standard library:

import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Data.Unit using (⊤; tt)
import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
import Data.Empty using (⊥; ⊥-elim)
import Function.Bundles using (_⇔_)