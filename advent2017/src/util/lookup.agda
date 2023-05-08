module util.lookup where

open import util.list_stuff using (filterᵇ)
open import Data.Tree.Binary using (Tree ; leaf ; node)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (intersperse)
open import Data.String.Properties using (_<?_) renaming (_==_ to str-eq)
open import Agda.Builtin.Bool using (Bool ; false ; true)
open import Data.Bool using (not)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _==_)
open import Agda.Builtin.List using (List; _∷_ ; [])
open import Data.List.Base using (length ; _++_ ; concat ; map ; head ; tail)
open import Agda.Builtin.Maybe using (Maybe ; just ; nothing)
open import Relation.Binary.PropositionalEquality.Core using (_≡_ ; refl)
open import Relation.Nullary.Decidable using (isYes)

record LTPair (A B : Set) : Set where
  field
    Eq : A → A → Bool
    Lt : A → A → Bool
    key : A
    val : B

LookupTree : Set → Set → Set
LookupTree A B = Tree (LTPair A B) Bool

LookupStrTree : Set → Set
LookupStrTree A = Tree (LTPair String A) Bool

LookupNatTree : Set → Set
LookupNatTree A = Tree (LTPair Nat A) Bool

mk-pair : {A B : Set} → (A → A → Bool) → (A → A → Bool) → (A × B) → LTPair A B
mk-pair eq lt (k , v) = record {Eq = eq ; Lt = lt ; key = k; val = v}

lp : {A B : Set} → (A × B) → A
lp (x , _) = x

build-tree-help : {A B : Set} → Nat → (A → A → Bool) → (A → A → Bool) → List (A × B) → LookupTree A B
build-tree-help _ eq lt [] = leaf false
build-tree-help 0 eq lt _ = leaf false
build-tree-help (suc l) eq lt ((x , y) ∷ xs) = node
  (build-tree-help l eq lt (filterᵇ (λ { q → lt x (lp q) }) xs ))
  (mk-pair eq lt (x , y))
  (build-tree-help l eq lt (filterᵇ (λ { q → lt (lp q) x }) xs ))

build-tree : {A B : Set} → (A → A → Bool) → (A → A → Bool) → List (A × B) → LookupTree A B
build-tree eq lt db = build-tree-help (length db) eq lt db

str-lt : String → String → Bool
str-lt a b = isYes (a <? b)

build-str-tree : {A : Set} → List (String × A) → LookupStrTree A
build-str-tree db = build-tree str-eq str-lt db

build-nat-tree : {A : Set} → List (Nat × A) → LookupNatTree A
build-nat-tree db = build-tree _==_ _<_ db

read-val : {A B : Set} → A → LookupTree A B → Maybe B
read-val key (leaf _) = nothing
read-val key (node lhs v rhs) with ((LTPair.Eq v) key (LTPair.key v))
read-val key (node lhs v rhs) | true = (just (LTPair.val v))
read-val key (node lhs v rhs) | false with ((LTPair.Lt v) (LTPair.key v) key)
read-val key (node lhs v rhs) | false | true = read-val key lhs
read-val key (node lhs v rhs) | false | false = read-val key rhs

has-val : {A B : Set} → A → LookupTree A B → Bool
has-val key tree with (read-val key tree)
... | nothing = false
... | _ = true

set-val-op : {A B : Set} → (A → A → Bool) → (A → A → Bool) → A → B → LookupTree A B → LookupTree A B
set-val-op eq lt key nv (leaf _) = node (leaf false) (mk-pair eq lt (key , nv)) (leaf false)
set-val-op eq lt key nv (node lhs v rhs) with ((LTPair.Eq v) key (LTPair.key v))
set-val-op eq lt key nv (node lhs v rhs) | true = (node lhs (mk-pair eq lt (key , nv)) rhs)
set-val-op eq lt key nv (node lhs v rhs) | false with ((LTPair.Lt v) (LTPair.key v) key)
set-val-op eq lt key nv (node lhs v rhs) | false | true = node (set-val-op eq lt key nv lhs) v rhs
set-val-op eq lt key nv (node lhs v rhs) | false | false = node lhs v (set-val-op eq lt key nv rhs)

set-val : {A B : Set} → A → B → LookupTree A B → LookupTree A B
set-val _ _ (leaf _) = leaf false
set-val key nv (node lhs v rhs) = set-val-op (LTPair.Eq v) (LTPair.Lt v) key nv (node lhs v rhs)

all-values : {A B : Set} → LookupTree A B → List B
all-values (leaf _) = []
all-values (node lhs v rhs) = (all-values lhs) ++ ((LTPair.val v) ∷ []) ++ (all-values rhs)

all-kv : {A B : Set} → LookupTree A B → List (A × B)
all-kv (leaf _) = []
all-kv (node lhs v rhs) = (all-kv lhs) ++ ((LTPair.key v , LTPair.val v) ∷ []) ++ (all-kv rhs)

all-keys : {A B : Set} → LookupTree A B → List A
all-keys (leaf _) = []
all-keys (node lhs v rhs) = (all-keys lhs) ++ ((LTPair.key v) ∷ []) ++ (all-keys rhs)

quick-sort-h : {A : Set} → Nat → (A → A → Bool) → List A → List A
quick-sort-h 0 _ _ = []
quick-sort-h _ _ [] = []
quick-sort-h (suc l) lt (x ∷ xs) = concat ((quick-sort-h l lt (filterᵇ (λ {q → not (lt x q)}) xs)) ∷ (x ∷ []) ∷ (quick-sort-h l lt (filterᵇ (λ {q → lt x q}) xs)) ∷ [])

quick-sort : {A : Set} → (A → A → Bool) → List A → List A
quick-sort lt inp = quick-sort-h (length inp) lt inp

counter-h : {A : Set} → LookupTree A Nat → List A → LookupTree A Nat
counter-h tree [] = tree
counter-h tree (x ∷ xs) with (read-val x tree)
counter-h tree (x ∷ xs) | nothing = counter-h (set-val x 1 tree) xs
counter-h tree (x ∷ xs) | (just c) = counter-h (set-val x (suc c) tree) xs

pair-orders : {A : Set} → (A → A → Bool) → (A × Nat) → (A × Nat) → Bool
pair-orders lt (ls , ln) (rs , rn) with (ln < rn)
pair-orders lt (ls , ln) (rs , rn) | true = false
pair-orders lt (ls , ln) (rs , rn) | false with (rn < ln)
pair-orders lt (ls , ln) (rs , rn) | false | true = true
pair-orders lt (ls , ln) (rs , rn) | false | false = lt ls rs

counter : {A : Set} → (A → A → Bool) → (A → A → Bool) → List A → List (A × Nat)
counter {A} eq lt lst = quick-sort (pair-orders lt) counts
  where
    counts : List (A × Nat)
    counts with (head lst)
    counts | (just h) with (tail lst)
    counts | (just h) | (just t) = all-kv (counter-h (build-tree eq lt ((h , 1) ∷ [])) t)
    counts | (just h) | _ = []
    counts | _ = []


counter-nat : List Nat → List (Nat × Nat)
counter-nat = counter _==_ _<_

test_read-vala : read-val 3 (build-tree _==_ _<_ ((4 , 7) ∷ (5 , 2) ∷ (3 , 4) ∷ [])) ≡ (just 4)
test_read-vala = refl

test_read-valb : read-val 5 (build-tree _==_ _<_ ((4 , 7) ∷ (5 , 2) ∷ (3 , 4) ∷ [])) ≡ (just 2)
test_read-valb = refl

test_has-val : has-val 5 (build-tree _==_ _<_ ((4 , 7) ∷ (5 , 2) ∷ (3 , 4) ∷ [])) ≡ true
test_has-val = refl

test_has-val_f : has-val 8 (build-tree _==_ _<_ ((4 , 7) ∷ (5 , 2) ∷ (3 , 4) ∷ [])) ≡ false
test_has-val_f = refl

test_set-val : set-val 8 1 (build-tree _==_ _<_ ((4 , 7) ∷ (5 , 2) ∷ (3 , 4) ∷ [])) ≡ (build-tree _==_ _<_ ((4 , 7) ∷ (5 , 2) ∷ (3 , 4) ∷ (8 , 1) ∷ []))
test_set-val = refl

test_all-val : all-values (build-tree _==_ _<_ ((4 , 7) ∷ (5 , 2) ∷ (3 , 4) ∷ [])) ≡ 2 ∷ 7 ∷ 4 ∷ []
test_all-val = refl

test-quick-sort : quick-sort _<_ (3 ∷ 2 ∷ 5 ∷ 1 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ 5 ∷ []
test-quick-sort = refl

test-counter : counter-nat (1 ∷ 2 ∷ 2 ∷ 3 ∷ []) ≡ (2 , 2) ∷ (1 , 1) ∷ (3 , 1) ∷ []
test-counter = refl
