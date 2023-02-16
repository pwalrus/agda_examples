module util.lookup where

open import util.list_stuff using (filterᵇ)
open import Data.Tree.Binary using (Tree ; leaf ; node)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Bool using (Bool ; false ; true)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _==_)
open import Agda.Builtin.List using (List; _∷_ ; [])
open import Data.List.Base using (length)
open import Agda.Builtin.Maybe using (Maybe ; just ; nothing)
open import Relation.Binary.PropositionalEquality.Core using (_≡_ ; refl)

record LTPair (A B : Set) : Set where
  field
    Eq : A → A → Bool
    Lt : A → A → Bool
    key : A
    val : B

LookupTree : Set → Set → Set
LookupTree A B = Tree (LTPair A B) Bool

mk_pair : {A B : Set} → (A → A → Bool) → (A → A → Bool) → (A × B) → LTPair A B
mk_pair eq lt (k , v) = record {Eq = eq ; Lt = lt ; key = k; val = v}

lp : {A B : Set} → (A × B) → A
lp (x , _) = x

build_tree_help : {A B : Set} → Nat → (A → A → Bool) → (A → A → Bool) → List (A × B) → LookupTree A B
build_tree_help _ eq lt [] = leaf false
build_tree_help 0 eq lt _ = leaf false
build_tree_help (suc l) eq lt ((x , y) ∷ xs) = node
  (build_tree_help l eq lt (filterᵇ (λ { q → lt x (lp q) }) xs ))
  (mk_pair eq lt (x , y))
  (build_tree_help l eq lt (filterᵇ (λ { q → lt (lp q) x }) xs ))

build_tree : {A B : Set} → (A → A → Bool) → (A → A → Bool) → List (A × B) → LookupTree A B
build_tree eq lt db = build_tree_help (length db) eq lt db

read_val : {A B : Set} → A → LookupTree A B → Maybe B
read_val key (leaf _) = nothing
read_val key (node lhs v rhs) with ((LTPair.Eq v) key (LTPair.key v))
read_val key (node lhs v rhs) | true = (just (LTPair.val v))
read_val key (node lhs v rhs) | false with ((LTPair.Lt v) (LTPair.key v) key)
read_val key (node lhs v rhs) | false | true = read_val key lhs
read_val key (node lhs v rhs) | false | false = read_val key rhs

test_read_vala : read_val 3 (build_tree _==_ _<_ ((4 , 7) ∷ (5 , 2) ∷ (3 , 4) ∷ [])) ≡ (just 4)
test_read_vala = refl

test_read_valb : read_val 5 (build_tree _==_ _<_ ((4 , 7) ∷ (5 , 2) ∷ (3 , 4) ∷ [])) ≡ (just 2)
test_read_valb = refl

