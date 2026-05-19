-- Isomorphism: Isomorphism and Embedding

{-# OPTIONS -WnoUnknownNamesInFixityDecl #-}

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
    
≃-sym : ∀ {A B : Set}
  → A ≃ B
    -----
  → B ≃ A
≃-sym A≃B = 
  record
    { to      = from A≃B
    ; from    = to  A≃B
    ; to∘from = from∘to A≃B
    ; from∘to = to∘from A≃B
    }
    
≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
≃-trans A≃B B≃C =
  record
    { to = to B≃C ∘ to A≃B
    ; from = from A≃B ∘ from B≃C
        ; from∘to  = λ{x →
        begin
          (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x)
        ≡⟨⟩
          from A≃B (from B≃C (to B≃C (to A≃B x)))
        ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
          from A≃B (to A≃B x)
        ≡⟨ from∘to A≃B x ⟩
          x
        ∎}
    ; to∘from = λ{y →
        begin
          (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y)
        ≡⟨⟩
          to B≃C (to A≃B (from A≃B (from B≃C y)))
        ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
          to B≃C (from B≃C y)
        ≡⟨ to∘from B≃C y ⟩
          y
        ∎}
     }

-- Equational reasoning for isomorphism

module ≃-Reasoning where
  
  infix  1 ≃-begin_
  infixr 2 _≃<_>_
  infix  3 _≃-∎

≃-begin_ : ∀ {A B : Set}
  → A ≃ B
    -----
  → A ≃ B
≃-begin A≃B = A≃B

_≃<_>_ : ∀ (A : Set) {B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
A ≃< A≃B > B≃C = ≃-trans A≃B B≃C

_≃-∎ : ∀ (A : Set)
  --------
  → A ≃ A
A ≃-∎ = ≃-refl

open ≃-Reasoning

-- Embedding

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field 
    to : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { to = λ{x → x}
    ; from = λ{y → y}
    ; from∘to = λ{x → refl}
    }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C =
  record
    { to      = λ{x → to   B≲C (to   A≲B x)}
    ; from    = λ{y → from A≲B (from B≲C y)}
    ; from∘to = λ{x →
        begin
          from A≲B (from B≲C (to B≲C (to A≲B x)))
        ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
          from A≲B (to A≲B x)
        ≡⟨ from∘to A≲B x ⟩
          x
        ∎}
     }
     
≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
    -------------------
  → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to =
  record
    { to      = to A≲B
    ; from    = from A≲B
    ; from∘to = from∘to A≲B
    ; to∘from = λ{y →
        begin
          to A≲B (from A≲B y)
        ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
          to A≲B (to B≲A y)
        ≡⟨ cong-app to≡from (to B≲A y) ⟩
          from B≲A (to B≲A y)
        ≡⟨ from∘to B≲A y ⟩
          y
        ∎}
    }
    
-- Equational reasoning for embedding

module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    → A ≲ B
      -----
    → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≲ B
    → B ≲ C
      -----
    → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set)
      -----
    → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning

-- Exercise ≃-implies-≲ (practice)

≃-implies-≲ : ∀ {A B : Set}
  → A ≃ B
    -----
  → A ≲ B
≃-implies-≲ A≃B = 
  record
    { from    = from A≃B
    ; to      = to A≃B
    ; from∘to = from∘to A≃B
    }
      
-- Exercise _⇔_ (practice)

record _⇔_ (A B : Set) : Set where -- \<=>
  field 
    to   : A → B
    from : B → A

open _⇔_

⇔-refl : ∀ {A : Set} → A ⇔ A
⇔-refl =
  record
    { to = λ{x → x}
    ; from = λ{y → y}
    }
    
⇔-trans : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans A⇔B B⇔C =
  record
    { to      = λ{x → to   B⇔C (to   A⇔B x)}
    ; from    = λ{y → from A⇔B (from B⇔C y)}
    }
    
⇔-sym : ∀ {A B : Set}
  → A ⇔ B
    -----
  → B ⇔ A
⇔-sym A⇔B = 
  record
    { to      = from A⇔B
    ; from    = to  A⇔B
    }
    
-- Exercise Bin-embedding (stretch)

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc-bin : Bin → Bin
inc-bin ⟨⟩ = ⟨⟩ I
inc-bin (x O) = x I
inc-bin (x I) = (inc-bin x) O

to-bin : ℕ → Bin
to-bin zero = ⟨⟩ O
to-bin (suc x) = inc-bin (to-bin x)

from-bin : Bin → ℕ
from-bin ⟨⟩ = zero
from-bin (x O) = 2 * (from-bin x)
from-bin (x I) = 2 * (from-bin x) + 1

from-inc : ∀ (b : Bin) → from-bin (inc-bin b) ≡ suc (from-bin b)
from-inc ⟨⟩ = refl
from-inc (b O)
  rewrite
    +-identityʳ (from-bin b)
  | +-suc (from-bin b + from-bin b) zero
  | +-identityʳ (from-bin b + from-bin b)
  = refl
from-inc (b I)
  rewrite
    from-inc b
  | +-identityʳ (suc (from-bin b))
  | +-identityʳ (from-bin b)
  | +-suc (from-bin b) (from-bin b)
  | +-assoc (from-bin b) (from-bin b) 1
  | +-suc (from-bin b) zero
  | +-identityʳ (from-bin b)
  | +-suc (from-bin b) (from-bin b)
  = refl

from-to-bin : ∀ (n : ℕ) → from-bin (to-bin n) ≡ n
from-to-bin zero = refl
from-to-bin (suc n)
  rewrite
    from-inc (to-bin n)
  | from-to-bin n
  = refl

bin-embedding : ℕ ≲ Bin
bin-embedding =
  record
    { to      = to-bin
    ; from    = from-bin
    ; from∘to = from-to-bin
    }      
    
-- Standard library

-- import Function.Base using (_∘_)
-- import Function.Bundles using (_↔_; _↩_)

-- Unicode

-- ∘  U+2218  RING OPERATOR (\o, \circ, \comp)
-- λ  U+03BB  GREEK SMALL LETTER LAMBDA (\lambda, \Gl)
-- ≃  U+2243  ASYMPTOTICALLY EQUAL TO (\~-)
-- ≲  U+2272  LESS-THAN OR EQUIVALENT TO (\<~)
-- ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)