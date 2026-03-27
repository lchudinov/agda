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

-- Total

data Total (m n : ℕ) : Set where
  
  forward :
      m ≤ n
      ---------
    → Total m n
    
  flipped :
      n ≤ m
      ---------
    → Total m n

data Total' : ℕ → ℕ → Set where
  
  forward' : ∀ {m n : ℕ}
      m ≤ n
      ---------
    → Total' m n
    
  flipped' : ∀ {m n : ℕ}
      n ≤ m
      ---------
    → Total' m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n = forward (s≤s m≤n)
...                        | flipped n≤m = flipped (s≤s n≤m)

≤-total' : ∀ (m n : ℕ) → Total m n
≤-total' zero n = forward z≤n
≤-total' (suc m) zero = flipped z≤n
≤-total' (suc m) (suc n) = helper (≤-total m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n) = forward (s≤s m≤n)
  helper (flipped n≤m) = flipped (s≤s n≤m)
  
≤-total'' : ∀ (m n : ℕ) → Total m n
≤-total'' m zero = flipped z≤n
≤-total'' zero (suc n) = forward z≤n
≤-total'' (suc m) (suc n) with ≤-total'' m n 
...                          | forward m≤n = forward (s≤s m≤n)
...                          | flipped n≤m = flipped (s≤s n≤m)

-- Monotonicity

+-monoʳ-≤ : ∀ (n p q : ℕ) -- \^r tab tab tab
  → p ≤ q
    ------------------
  → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n 

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

-- Exercise *-mono-≤ (stretch)

*-monoʳ-≤ : ∀ (n p q : ℕ) -- \^r tab tab tab
  → p ≤ q
    ------------------
  → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ) -- \^l tab tab tab
  → m ≤ n
    ------------------
  → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n
  
*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    --------------
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

-- Strict inequality

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  
  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n
  
  s<s : ∀ {m n : ℕ}
    → m < n
      ------------
    → suc m < suc n 

-- Exercise <-trans (recommended)

<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p
<-trans {m} {n} {p} z<s (s<s n<p) = z<s
<-trans {m} {n} {p} (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

-- Exercise trichotomy (practice)

infix 4 _>_

_>_ : ℕ → ℕ → Set
m > n = n < m 
    
data Trichotomy (m n : ℕ) : Set where
  
  less : 
      m < n
      ---------
    → Trichotomy m n
  
  equal : 
      m ≡ n
      ---------
    → Trichotomy m n
  
  greater : 
      m > n
      ---------
    → Trichotomy m n

trichotomy : (m n : ℕ) → Trichotomy m n
trichotomy zero zero = equal refl
trichotomy zero (suc n) = less z<s
trichotomy (suc m) zero = greater z<s
trichotomy (suc m) (suc n) with trichotomy m n
...                        | less  m<n = less (s<s m<n)
...                        | equal m≡n = equal (cong suc m≡n)
...                        | greater m>n = greater (s<s m>n)

-- Exercise +-mono-< (practice)

+-monoʳ-< : ∀ (n p q : ℕ) -- \^r tab tab tab
  → p < q
    ------------------
  → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ)
  → m < n
    -------------
  → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n 

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
    -------------
  → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

-- Exercise ≤→<, <→≤ (recommended)

≤→< : ∀ (m n : ℕ)
  → suc m ≤ n
    ------------
  → m < n
≤→< zero (suc n) sm≤n = z<s
≤→< (suc m) (suc n) (s≤s sm≤n) = s<s (≤→< m n sm≤n)



<→≤ : ∀ (m n : ℕ)
  → m < n
    ------------
  → suc m ≤ n
<→≤ zero (suc n) m<n = s≤s z≤n
<→≤ (suc m) (suc n) (s<s m<n) = s≤s (<→≤ m n m<n)

-- Exercise <-trans-revisited (practice)

<-suc : ∀ (m n : ℕ)
  → m < n
    ------------
  → m < suc n
<-suc zero (suc n) z<s = z<s
<-suc (suc m) (suc n) (s<s m<n) = s<s (<-suc m n m<n)

<-trans-revisited : ∀ {m n p : ℕ}
  → m < n
  → n < p
  -----
  → m < p
<-trans-revisited {m} {n} {p} m<n n<p = ≤→< m p (≤-trans (<→≤ m n m<n) (inv-s≤s (<→≤ n (suc p) (<-suc n p n<p))))

-- Even and odd

data even : ℕ → Set
data odd  : ℕ → Set
  
data even where

  zero :
    --------
    even zero
  
  suc : ∀ {n : ℕ}
    → odd n
    → even (suc n)

data odd where
  
  suc : ∀ {n : ℕ}
    → even n
    ------------
    → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)
  
o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)
  
e+e≡e zero en = en
e+e≡e (suc om) en = suc (o+e≡o om en)

o+e≡o (suc em) en = suc (e+e≡e em en)

-- Exercise o+o≡e (stretch)

o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
    ------------
  → even (m + n)
o+o≡e om on = o+o≡e om on

-- Exercise Bin-predicates (stretch)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc x) = inc (to x)

from : Bin → ℕ
from ⟨⟩ = zero
from (x O) = 2 * (from x)
from (x I) = 2 * (from x) + 1

data One : Bin → Set where
  one :
    ----
    One (⟨⟩ I)

  one_o : ∀ {b : Bin}
    → One b
      -------
    → One (b O)

  one_i : ∀ {b : Bin}
    → One b
      -------
    → One (b I)

data Can : Bin → Set where
  zero : 
    -----
    Can ⟨⟩
  
  one : ∀ {b : Bin}
    → One b
      --------
    → Can b

