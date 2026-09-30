-- Lists: Lists and higher-order functions

module ListsL where
  
-- Imports

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_)

-- Lists

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A  -- \∷

infixr 5 _∷_

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []
--  0 ∷ (1 ∷ (2 ∷ []))

data List′ : Set → Set₁ where
  []′ : ∀ {A : Set} → List′ A
  _∷_′ : ∀ {A : Set} A → List′ A → List′ A
  
_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))

{-# BUILTIN LIST List #-}

-- List syntax

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

-- Append

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ = 
  begin
    0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
  ≡⟨⟩
    0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ∎

-- Reasoning about append
++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs 
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin 
    [] ++ xs 
  ≡⟨⟩
    xs
  ∎

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs 
  ∎
  
-- Length

length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

_ : length [ 0 , 1 , 2 ] ≡ 3
_ =
  begin
    length ( 0 ∷ 1 ∷ 2 ∷ [] )
  ≡⟨⟩
    suc (length ( 1 ∷ 2 ∷ [] ))
  ≡⟨⟩
    suc (suc (length ( 2 ∷ [] )))
  ≡⟨⟩
    suc (suc (suc (length {ℕ} [] )))
  ≡⟨⟩
    suc (suc (suc zero))
  ∎
  
-- Reasoning about length

length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎

-- Reverse

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    reverse (1 ∷ 2 ∷ []) ++ [ 0 ]
  ≡⟨⟩
    (reverse (2 ∷ []) ++ [ 1 ] ) ++ [ 0 ]
  ≡⟨⟩
    ((reverse [] ++ [ 2 ]) ++ [ 1 ] ) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ] ) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ 2 ∷ []) ++ 1 ∷ [] ) ++ 0 ∷ []
  ≡⟨⟩
    ( 2 ∷ [] ++ 1 ∷ [] ) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ ([] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ (1 ∷ [] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ ([] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ≡⟨⟩
    [ 2 , 1 , 0 ]
  ∎

-- Exercise reverse-++-distrib (recommended)

reverse-++-distrib : ∀ {A : Set} (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys rewrite ++-identityʳ (reverse ys) = refl
reverse-++-distrib (x ∷ xs) ys rewrite reverse-++-distrib xs ys | ++-assoc (reverse ys) (reverse xs) [ x ]  = refl

-- Exercise reverse-involutive (recommended)
reverse-involutive : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) rewrite reverse-++-distrib (reverse xs) [ x ] | reverse-involutive xs = refl

-- Faster reverse

shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
     shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎
  
-- shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

  
_ : reverse′ [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse′ (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    shunt (0 ∷ 1 ∷ 2 ∷ []) []
  ≡⟨⟩
    shunt (1 ∷ 2 ∷ []) (0 ∷ [])
  ≡⟨⟩
    shunt (2 ∷ []) (1 ∷ 0 ∷ [])
  ≡⟨⟩
    shunt [] (2 ∷ 1 ∷ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ∎

-- Map

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ = 
  begin
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
      suc 0 ∷ map suc [ 1 , 2 ]
  ≡⟨⟩
      suc 0 ∷ suc 1 ∷ map suc [ 2 ]
  ≡⟨⟩
      suc 0 ∷ suc 1 ∷ suc 2 ∷ map suc []
  ≡⟨⟩
      suc 0 ∷ suc 1 ∷ suc 2 ∷ []
  ≡⟨⟩
      1 ∷ 2 ∷ 3 ∷ []
  ∎ 

sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    sucs [ 0 , 1 , 2 ]
  ≡⟨⟩
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
    [ 1 , 2 , 3 ]
  ∎
  
-- Exercise map-compose (practice)

map-compose : ∀ {A B C : Set} → (f : A → B) → (g : B → C) → (xs : List A) → map (g ∘ f) xs ≡ (map g ∘ map f) xs
map-compose f g [] = refl
map-compose f g (x ∷ xs) = cong (_∷_ (g (f x))) (map-compose f g xs)

-- Exercise map-++-distribute (practice)

map-++-distribute : ∀ {A B : Set} → (xs ys : List A) → (f : A → B) → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute [] ys f = refl
map-++-distribute (x ∷ xs) ys f = cong (f x ∷_) (map-++-distribute xs ys f)

-- Exercise map-Tree (practice)
-- Define a type of trees with leaves of type A and internal nodes of type B:

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B
-- Define a suitable map operator over trees:

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node tree1 x tree2) = node (map-Tree f g tree1) (g x) (map-Tree f g tree2)

-- Fold

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e [] = e -- \otimes
foldr _⊗_ e (x ∷ xs) = x ⊗ foldr _⊗_ e xs

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 ( 1 ∷ 2 ∷ 3 ∷ 4 ∷ [] )
  ≡⟨⟩
    1 + foldr _+_ 0 ( 2 ∷ 3 ∷ 4 ∷ [] )
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 ( 3 ∷ 4 ∷ [] ))
  ≡⟨⟩
    1 + (2 + (3 + (foldr _+_ 0 ( 4 ∷ [] ))))
  ≡⟨⟩
    1 + (2 + (3 + (4 + (foldr _+_ 0 [] ))))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎
  
sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    sum [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ∎

-- Exercise product (recommended)

product : List ℕ → ℕ
product = foldr _*_ 1

-- Exercise foldr-++ (recommended)
-- Show that fold and append are related as follows:

-- postulate
foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
  foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys = cong (_⊗_ x) (foldr-++ _⊗_ e xs ys)

-- Exercise foldr-∷ (practice)
-- Show

-- foldr _∷_ [] xs ≡ xs

foldr-cons : ∀ {A : Set} → (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-cons [] = refl
foldr-cons (x ∷ xs) = cong (_∷_ x) (foldr-cons xs)

-- Show as a consequence of foldr-++ above that

foldr-cons2 : ∀ {A : Set} → (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
foldr-cons2 [] ys = refl
foldr-cons2 (x ∷ xs) ys = cong (_∷_ x) (foldr-cons2 xs ys)

-- Exercise map-is-foldr (practice)
-- Show that map can be defined using fold:

-- map f ≡ foldr (λ x xs → f x ∷ xs) []
-- The proof requires extensionality.

map-is-foldr : ∀ {A B : Set} (f : A → B) (x : B) (xs : List A) → map f xs ≡ foldr (λ x xs → f x ∷ xs) [] xs
map-is-foldr f x [] = refl
map-is-foldr f x (x1 ∷ xs) = cong (_∷_ (f x1)) (map-is-foldr f x xs)

-- Exercise fold-Tree (practice)
-- Define a suitable fold function for the type of trees given earlier:

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf x) = f x
fold-Tree f g (node left x right) = g (fold-Tree f g left) x (fold-Tree f g right)

-- Exercise map-is-fold-Tree (practice)
-- Demonstrate an analogue of map-is-foldr for the type of trees.
