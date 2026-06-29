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
    { to      = λ ¬A⊎B → ⟨ (λ a → ¬A⊎B (inj₁ a)) , (λ b → ¬A⊎B (inj₂ b)) ⟩
    ; from    = λ
        { ⟨ ¬A , ¬B ⟩ →
            λ
              { (inj₁ a) → ¬A a
              ; (inj₂ b) → ¬B b
              }
        }
    ; from∘to = λ _ → refl
    ; to∘from = λ _ → refl
    }

-- Do we also have the following?

-- ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)
-- If so, prove; if not, can you give a relation weaker than isomorphism that relates the two sides?

×-dual-⊎ : ∀ {A B : Set} → (¬ A ⊎ ¬ B) → ¬ (A × B)
×-dual-⊎ (inj₁ ¬A) ⟨ a , b ⟩ = ¬A a
×-dual-⊎ (inj₂ ¬B) ⟨ a , b ⟩ = ¬B b

-- Excluded middle is irrefutable

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A
  
em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = k (inj₂ λ{ x → k (inj₁ x) })

-- Exercise Classical (stretch)
-- Consider the following principles:

-- Excluded Middle: A ⊎ ¬ A, for all A
-- Double Negation Elimination: ¬ ¬ A → A, for all A
-- Peirce’s Law: ((A → B) → A) → A, for all A and B.
-- Implication as disjunction: (A → B) → ¬ A ⊎ B, for all A and B.
-- De Morgan: ¬ (¬ A × ¬ B) → A ⊎ B, for all A and B.
-- Show that each of these implies all the others.

-- Your code goes here

-- Exercise Stable (stretch)
-- Say that a formula is stable if double negation elimination holds for it:

-- Stable : Set → Set
-- Stable A = ¬ ¬ A → A
-- Show that any negated formula is stable, and that the conjunction of two stable formulas is stable.

-- Your code goes here

-- Standard library
-- Definitions similar to those in this chapter can be found in the standard library:

import Relation.Nullary using (¬_)
import Relation.Nullary.Negation using (contradiction; contraposition)
-- The standard library uses contradiction, which combines our ¬-elim and ⊥-elim.

-- Unicode
-- This chapter uses the following unicode:

-- ¬  U+00AC  NOT SIGN (\neg)
-- ≢  U+2262  NOT IDENTICAL TO (\==n)