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