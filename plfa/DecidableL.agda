-- Decidable: Booleans and decision procedures

module DecidableL where

-- Imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Negation using (¬_)
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.part1.Relations using (_<_; z<s; s<s)
open import plfa.part1.Isomorphism using (_⇔_)

-- Evidence vs Computation

infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where
  
  z≤n : ∀ {n : ℕ}
      -------
    → zero ≤ n
  
  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      --------
    → suc m ≤ suc n

2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))

data Bool : Set where
  true  : Bool
  false : Bool

infix 4 _≤ᵇ_  -- \^b

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n = true
suc m ≤ᵇ zero = false
suc m ≤ᵇ suc n = m ≤ᵇ n

_ : (2 ≤ᵇ 4) ≡ true
_ = 
  begin
    2 ≤ᵇ 4
  ≡⟨⟩
    1 ≤ᵇ 3
  ≡⟨⟩
    0 ≤ᵇ 2
  ≡⟨⟩
    true
  ∎
  
_ : (4 ≤ᵇ 2) ≡ false
_ = 
  begin
    4 ≤ᵇ 2
  ≡⟨⟩
    3 ≤ᵇ 1
  ≡⟨⟩
    2 ≤ᵇ 0
  ≡⟨⟩
    false
  ∎

-- Relating evidence and computation

T : Bool → Set
T true = ⊤
T false = ⊥

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt = refl
T→≡ false ()

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl = tt

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero n tt = z≤n
≤ᵇ→≤ (suc m) (suc n) m≤ᵇn = s≤s (≤ᵇ→≤ m n m≤ᵇn)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n = tt
≤→≤ᵇ (s≤s m≤n) = ≤→≤ᵇ m≤n

-- The best of both worlds

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A
  
¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤? n     = yes z≤n
suc m ≤? zero = no ¬s≤z
suc m ≤? suc n with m ≤? n
...               | yes m≤n  = yes (s≤s m≤n)
...               | no  ¬m≤n  = no (¬s≤s ¬m≤n)

_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_  = refl

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_  = refl

-- Exercise _<?_ (recommended)
-- Analogous to the function above, define a function to decide strict inequality:

-- postulate
-- _<?_ : ∀ (m n : ℕ) → Dec (m < n)

¬z<z : ∀ {m : ℕ} → ¬ (zero < zero)
¬z<z ()

¬s<z : ∀ {m : ℕ} → ¬ (suc m < zero)
¬s<z ()

¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero <? zero     = no ¬z<z
zero <? suc n     = yes z<s
suc m <? zero = no ¬s<z
suc m <? suc n with m <? n
...               | yes m<n  = yes (s<s m<n)
...               | no  ¬m<n  = no (¬s<s ¬m<n)

-- Exercise _≡ℕ?_ (practice)
-- Define a function to decide whether two naturals are equal:

postulate
  _≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)