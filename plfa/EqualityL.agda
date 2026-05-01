-- Equality: Equality and equational reasoning

module EqualityL where
-- Equality

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
  
infix 4 _≡_

{-# BUILTIN EQUALITY _≡_ #-}

-- Equality is an equivalence relation

sym : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
-- sym e = {!   !} --  if in the hole we type `C-c C-c e` then Agda will instantiate `e` to all possible constructors, with one equation for each.
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl refl = refl

-- Congruence and substitution

cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
    ----------
  → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
    ----------
  → f u v ≡ f x y
cong₂ f refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ------------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ----------
  → P x → P y
subst P refl px = px

module ≡-Reasoning {A : Set} where
  infix  1 begin_
  infixr 2 step-≡-| step-≡-⟩
  infix  3 _∎
  
  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y
  
  step-≡-| : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
  step-≡-| x x≡y = x≡y 
  
  step-≡-⟩ : ∀ (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
  step-≡-⟩ x y≡z x≡y = trans x≡y y≡z
  
  syntax step-≡-| x x≡y = x ≡⟨⟩ x≡y
  syntax step-≡-⟩ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎ = refl

open ≡-Reasoning

trans′ : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎

trans′′ : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans′′ {A} {x} {y} {z} x≡y y≡z = begin x ≡⟨ x≡y ⟩ y ≡⟨ y≡z ⟩ z ∎

-- Exercise trans and ≡-Reasoning (practice)
-- skipped the Exercise

-- Chains of equations, another example

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
  
_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

-- Exercise ≤-Reasoning (stretch)

module ≤-Reasoning {A : Set} where
  data _≤_ : ℕ → ℕ → Set where -- \<=

    z≤n : ∀ {n : ℕ}
        --------
      → zero ≤ n
    
    s≤s : ∀ {m n : ℕ}
      → m ≤ n
      --------
      → suc m ≤ suc n
  
  infix 4 _≤_
      
  ≤-trans : ∀ {m n p : ℕ}
    → m ≤ n
    → n ≤ p
      -----
    → m ≤ p
  ≤-trans z≤n n≤p = z≤n
  ≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)
  
  ≤-refl : ∀ {n : ℕ}
      -----
    → n ≤ n
  ≤-refl {zero} = z≤n
  ≤-refl {suc n} = s≤s ≤-refl

  infix  1 begin≤_
  infixr 2 step-≤-| step-≤-⟩
  infix  3 _∎≤
  
  begin≤_ : ∀ {x y : ℕ} → x ≤ y → x ≤ y
  begin≤ x≤y = x≤y
  
  step-≤-| : ∀ (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y
  step-≤-| x x≤y = x≤y 
  
  step-≤-⟩ : ∀ {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  step-≤-⟩ x≤y y≤z = ≤-trans x≤y y≤z
  
  syntax step-≤-| x x≤y = x ≤⟨⟩ x≤y
  syntax step-≤-⟩ x y≤z x≤y = x ≤⟨ x≤y ⟩ y≤z

  _∎≤ : ∀ (x : ℕ) → x ≤ x
  x ∎≤ = ≤-refl
  
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
  

-- Rewriting

data even : ℕ → Set
data odd : ℕ → Set
  
data even where 
  
  even-zero : even zero
  
  even-suc : ∀ {n : ℕ}
    → odd n
      ---------------
    → even (suc n)

data odd where
  
  odd-suc : ∀ {n : ℕ}
    → even n
      ---------
    → odd (suc n)
    
even-comm : ∀ (m n : ℕ)
  → even (m + n)
    ---------------
  → even (n + m)
even-comm m n ev rewrite +-comm m n = ev -- C-c C-a an automated search

-- Multiple rewrites

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero n rewrite +-identity n = refl
+-comm′ (suc m) n rewrite +-suc n m | +-comm′ n m = refl
    
-- Rewriting expanded

even-comm′ : ∀ (m n : ℕ)
  → even (m + n)
    ----------------
  → even (n + m)
even-comm′ m n ev with   m + n  | +-comm m n
...                  | .(n + m) | refl       = ev

even-comm″ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm″ m n  =  subst even (+-comm m n)

-- Leibniz equality

_≐_ : ∀ {A : Set} (x y : A) → Set₁ -- \.=
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A}
  → x ≐ x
refl-≐ P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
    -----
  → x ≐ z
-- trans-≐ x≐y y≐z P Px = {!   !}
-- trans-≐ x≐y y≐z P Px = y≐z {!   !} {!   !}
-- trans-≐ x≐y y≐z P Px = y≐z {!   !} {!   !}
-- trans-≐ x≐y y≐z P Px = y≐z P {!   !}
-- trans-≐ x≐y y≐z P Px = y≐z P {! x≐y  !}
-- trans-≐ x≐y y≐z P Px = y≐z P (x≐y {!   !} {!   !})
-- trans-≐ x≐y y≐z P Px = y≐z P (x≐y P {!   !})
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

sim-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → y ≐ x
sim-≐ {A} {x} {y} x≐y P = Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx

≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → x ≐ y
≡-implies-≐ x≡y P = subst P x≡y

≐-implies-≡ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = Qy
  where
    Q : A → Set
    Q z = x ≡ z
    Qx : Q x
    Qx = refl
    Qy : Q y
    Qy = x≐y Q Qx
    
-- Universe polymorphism

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc) -- \lub

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where -- \ell
  refl′ : x ≡′ x

sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A}
  → x ≡′ y
    ------
  → y ≡′ x
sym′ refl′ = refl′

_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘ f) x  =  g (f x)

-- Standard library

-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
