-- Lambda: Introduction to Lambda Calculus

module LambdaL where
  
-- Imports

open import Data.Bool.Base using (Bool; true; false; T; not)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Data.Unit.Base using (tt)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Nullary.Decidable using (Dec; yes; no; False; toWitnessFalse; ¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- Syntax of terms

Id : Set
Id = String

infix  5 ƛ_⇒_ -- \Gl-
infix  5 μ_⇒_
infixl 7 _·_ -- \cdot
infix  8 `suc_
infix  9 `_

data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                    :  Id → Term → Term

-- Example terms

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
  case ` "m"
    [zero⇒ ` "n"
    |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

-- Exercise mul (recommended)
mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
  case ` "m"
    [zero⇒ `zero
    |suc "m" ⇒ ` "+" · ` "n" · (` "*" · ` "m" · ` "n") ]
    
-- Exercise mulᶜ (practice)

mulᶜ : Term 
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "m" · (` "n" · ` "s") · ` "z"

-- Exercise primed (stretch)

var? : (t : Term) → Bool
var? (` _)  =  true
var? _      =  false

ƛ′_⇒_ : (t : Term) → {_ : T (var? t)} → Term → Term
ƛ′_⇒_ (` x) N = ƛ x ⇒ N

case′_[zero⇒_|suc_⇒_] : Term → Term → (t : Term) → {_ : T (var? t)} → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]

μ′_⇒_ : (t : Term) → {_ : T (var? t)} → Term → Term
μ′ (` x) ⇒ N  =  μ x ⇒ N

_ : Term
_ = ƛ′ two ⇒ two

plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
  where
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"
  
mul′ : Term
mul′ = μ′ * ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ `zero
            |suc m ⇒ + · n · ( * · m · n) ]
  where
  +  =  ` "+"
  *  =  ` "*"
  m  =  ` "m"
  n  =  ` "n"
  
-- Formal vs informal

-- Bound and free variables

-- Values

data Value : Term → Set where
  V-ƛ : ∀ {x N}
      ---------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------
      Value `zero

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)
  
-- Substitution

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y -- \?=
... | yes _ = V
... | no _ = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = ƛ x ⇒ N
... | no _ = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ] = L [ y := V ] · M [ y := V ]
(`zero) [ y := V ] = `zero
(`suc M) [ y := V ] = `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _ = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no _ =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _         = μ x ⇒ N
... | no  _         = μ x ⇒ N [ y := V ]

--- Examples

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ]
      ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl

-- Quiz

-- What is the result of the following substitution?

_ : (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ] ≡ (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x"))
_ = refl

-- Exercise _[_:=_]′ (stretch)
-- The definition of substitution above has three clauses (ƛ, case, and μ) that invoke a with clause to deal with bound variables. Rewrite the definition to factor the common part of these three clauses into a single function, defined by mutual recursion with substitution.

-- I skipped te Exercise

--- Reduction

infix 4 _—→_ -- \ -->

data _—→_ : Term → Term → Set where

  ξ—·₁ : ∀ {L L′ M} -- \Gx \em \cdot
    → L —→ L′
      -----------
    → L · M —→ L′ · M

  ξ—·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------
    → V · M —→ V · M′
  
  β—ƛ : ∀ {x N V}
    → Value V
      ---------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]
    
  ξ—suc : ∀ {M M′}
    → M —→ M′
      -----------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      -----------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]
    
  β-zero : ∀ {x M N}
      ----------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
      ---------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]
    
  β-μ : ∀ {x M}
      ------------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]
    
-- Quiz

-- _ : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→ 