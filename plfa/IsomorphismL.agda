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

postulate 
  extensionality : ∀ {A B : Set} {f g : A → B}
   → (∀ (x : A) → f x ≡ g x)
     -----------------------
   → f ≡ g
  
_+′_ : ℕ → ℕ → ℕ
m +′ zero = m
m +′ suc n = suc (m +′ n)

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
  helper m zero = refl
  helper m (suc n) = cong suc (helper m n)

same : _+′_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))

postulate 
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
   → (∀ (x : A) → f x ≡ g x)
     -----------------------
   → f ≡ g

-- Isomorphism

infix 0 _≃_ -- \~-
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

data _≃′_ (A B : Set) : Set where
  mk-≃′ : ∀ (to : A → B) →
           ∀ (from : B → A) →
           ∀ (from∘to : ∀ (x : A) → from (to x) ≡ x) →
           ∀ (to∘from : ∀ (y : B) → to (from y) ≡ y) →
           A ≃′ B
           
to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (x : A) → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f 

to∘from′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g 

-- Isomorphism is an equivalence

-- Isomorphism is an equivalence, meaning that it is reflexive, symmetric, and transitive. 

≃-refl : ∀ {A : Set}
    ------
  → A ≃ A
≃-refl =
  record 
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    ; to∘from = λ{y → refl}
    }