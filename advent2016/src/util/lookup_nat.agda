
module util.lookup_nat where


import Data.Tree.AVL

open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Data.List using (List ; _∷_ ; [] ; applyUpTo)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Maybe using (Maybe ; just ; nothing)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Relation.Binary.PropositionalEquality.Core using (_≡_ ; refl)

open Data.Tree.AVL <-strictTotalOrder renaming (Tree to NatTree)

LookupNatTree : Set → Set
LookupNatTree A = NatTree (MkValue (λ {q → A}) (subst  (λ {q → A}))) 

build-nat-tree : {A : Set} → List (Nat × A) → LookupNatTree A
build-nat-tree db = fromList (Data.List.map (λ {(x , y) → (x , y)}) db)

read-val : {A : Set} → Nat → LookupNatTree A → Maybe A
read-val k t = lookup k t

set-val : {A : Set} → Nat → A → LookupNatTree A → LookupNatTree A
set-val k v t = insert k v t

has-val : {A : Set} → Nat → LookupNatTree A → Bool
has-val k t with (read-val k t)
... | nothing = false
... | _ = true

rem-val : {A : Set} → Nat → LookupNatTree A → LookupNatTree A
rem-val k t = delete k t

all-kv : {A : Set} → LookupNatTree A → List (Nat × A)
all-kv t = Data.List.map (λ {(x , y) → x , y}) (toList t)

test-read : read-val 2 (build-nat-tree ((1 , "a") ∷ (2 , "b") ∷ (3 , "c") ∷ [])) ≡ just "b"
test-read = refl

test-set : read-val 2 (set-val 2 "f" (build-nat-tree ((1 , "a") ∷ (2 , "b") ∷ (3 , "c") ∷ []))) ≡ just "f"
test-set = refl

test-rem : read-val 2 (rem-val 2 (build-nat-tree ((1 , "a") ∷ (2 , "b") ∷ (3 , "c") ∷ []))) ≡ nothing
test-rem = refl

test-bigger : read-val 42 (build-nat-tree (applyUpTo (λ {q → q , q}) 1000)) ≡ just 42
test-bigger = refl

