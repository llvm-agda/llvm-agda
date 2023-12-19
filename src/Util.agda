module Util where

open import Agda.Builtin.String

open import Data.List using (List; _∷_ ; [])
open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any
open import Data.Product using (_×_; _,_)

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

data Ident : Set where
  ident : String → Ident

infix 1 _∈_
_∈_ : {A : Set} → (e : A) → List A → Set
e ∈ xs = Any (e ≡_) xs

infix 1 _∉_
_∉_ : {A : Set} (id : Ident) → List (Ident × A) → Set
id ∉ xs = All (λ (id' , _) → id ≢ id') xs
