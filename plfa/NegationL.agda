module NegationL where

-- Imports
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Negation using (contradiction)
open import plfa.part1.Isomorphism using (_≃_; extensionality)

-- Negation

¬_ : Set → Set -- \neg
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x = λ{¬x → ¬x x}

¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
    --------------
  → ( ¬ B → ¬ A )
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢  y = ¬ (x ≡ y) 

_ : 1 ≢  2
_ = λ ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → contradiction x ¬x)

-- Exercise <-irreflexive (recommended)
open import Data.Nat using (z<s; s<s; _<_; _>_)

<-irreflexive : ∀ {n : ℕ} → n < n → ⊥
<-irreflexive (Data.Nat.s≤s n<n) = <-irreflexive n<n

-- Exercise trichotomy (practice)
-- Show that strict inequality satisfies trichotomy, that is, for any naturals m and n exactly one of the following holds:

-- m < n
-- m ≡ n
-- m > n
-- Here “exactly one” means that not only one of the three must hold, but that when one holds the negation of the other two must also hold.

data Trichotomy (m n : ℕ) : Set where
  
  less : 
      m < n
    → ¬ (m ≡ n)
    → ¬ (m > n)
      ---------
    → Trichotomy m n
  
  equal : 
      m ≡ n
    → ¬ (m < n)
    → ¬ (m > n)
      ---------
    → Trichotomy m n
  
  greater : 
      m > n
    → ¬ (m < n)
    → ¬ (m ≡ n)
      ---------
    → Trichotomy m n
    
trichotomy : (m n : ℕ) → Trichotomy m n
trichotomy zero zero = equal refl (λ ()) λ ()
trichotomy zero (suc n) = less (Data.Nat.s≤s Data.Nat.z≤n) (λ ()) λ ()
trichotomy (suc m) zero = greater (Data.Nat.s≤s Data.Nat.z≤n) (λ ()) λ ()
trichotomy (suc m) (suc n) with trichotomy m n
...                        | less  m<n ¬m≡n ¬m>n = less (Data.Nat.s≤s m<n) {!   !} {!   !}
...                        | equal m≡n ¬m<n ¬m>n = {!   !}
...                        | greater m>n ¬m<n ¬m≡n  = {!   !}

-- Exercise ⊎-dual-× (recommended)
-- Show that conjunction, disjunction, and negation are related by a version of De Morgan’s Law.

-- ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
-- This result is an easy consequence of something we’ve proved previously.

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = 
    record
    { to      = {!   !}
    ; from    = {!   !}
    ; from∘to = {!   !}
    ; to∘from = {!   !}
    }

-- Do we also have the following?

-- ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)
-- If so, prove; if not, can you give a relation weaker than isomorphism that relates the two sides?
