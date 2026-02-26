module RelationsL where
  
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)  -- \^r tab tab tab

-- Defining relations

data _≤_ : ℕ → ℕ → Set where -- \<=

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n
  
  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      --------
    → suc m ≤ suc n
    
_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

_ : 1 ≤ 2
_ = s≤s z≤n

_ : 1 ≤ 1
_ = s≤s z≤n

-- _ : 1 ≤ 0
-- _ = s≤s z≤n


-- Implicit arguments

-- the argument declarations surrounded by curly braces are implicit and need not be written explicitly

-- if we wish, it's possible to provide implicit arguments explicitly by writing the arguments inside curly braces. 
_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

-- One may also identify implicit arguments by name
_ : 2 ≤ 4
_ = s≤s {n = 3} (s≤s {n = 2} (z≤n))

+-identityʳ′ : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _  -- we use _ to ask Agda to infer the value of the explicit argument from the context.

-- Precedence

infix 4 _≤_

-- The ≤ binds less tightly than _+_, which is at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
-- `infix` means that the operator does not associate to either the left or right, as as it makes no sense to parse
-- `1 ≤ 2 ≤ 3` as either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)` 

-- Decidability

-- Inversion

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤s : ∀ {m : ℕ}
  → m ≤ zero
    --------
  → m ≡ zero
inv-z≤s z≤n = refl

-- Properties of ordering relations

-- Reflexive. For all n, n ≤ n holds.
-- Transitive. For all m, n, and p, if m ≤ n and n ≤ p hold, then m ≤ p holds.
-- Anti-symmetric. For all m and n, if both m ≤ n and n ≤ m hold, then m ≡ n holds.
-- Total. For all m and n, either m ≤ n or n ≤ m holds.

-- The relation _≤_ satisfies all four of these properties.

-- Preorder. Any relation that is reflexive and transitive.
-- Partial order. Any preorder that is also anti-symmetric.
-- Total order. Any partial order that is also total.

-- Exercise orderings (practice)

-- Give an example of a preorder that is not a partial order.
-- Divisibility on integers ignoring sign

-- Give an example of a partial order that is not a total order.
-- Divisibility on natural numbers

-- Reflexivity

≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

-- Transitivity

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n n≤p = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-trans' : ∀ (m n p : ℕ)
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans' zero n p m≤n n≤p = z≤n
≤-trans' (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans' m n p m≤n n≤p)

-- Anti-symmetry

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

-- Exercise ≤-antisym-cases (practice)

≤-antisym' : ∀ (m n : ℕ)
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym' zero zero m≤n n≤m = refl
≤-antisym' (suc m) (suc n) (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym' m n m≤n n≤m)

