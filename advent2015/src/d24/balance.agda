module d24.balance where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; each-one ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; LookupNatTree ; build-str-tree ; build-nat-tree ; has_val ; all_values ; all-keys ; all-kv ; LTPair) renaming (set_val to set-tree ; read_val to read-tree)
open import util.json using (readIntMaybe)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using (_==_ ; _<?_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using () renaming (_+_ to _+z_)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip)
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties renaming (_==_ to _==c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Function.Base using (_∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


div-nat : Nat → Nat → Nat
div-nat x y = div-helper 0 (pred y) x (pred y)

rem-from-target : Nat → Nat → List (Nat × List Nat) → List (Nat × Nat × List Nat)
rem-from-target last target [] = []
rem-from-target last target ((first , free) ∷ xs) with ((first < (suc target)) ∧ (last < first))
rem-from-target last target ((first , free) ∷ xs) | false = rem-from-target last target xs
rem-from-target last target ((first , free) ∷ xs) | true = ((target - first) , first , free) ∷ (rem-from-target last target xs)

add-front-each : {A : Set} → A → List (List A × List A) → List (List A × List A)
add-front-each _ [] = []
add-front-each fst ((xs , ys) ∷ zs) = ((fst ∷ xs) , ys) ∷ (add-front-each fst zs)

flatten-trip : {A : Set} → List A × List (List A × List A) → List (List A × List A × List A)
flatten-trip (_ , []) = []
flatten-trip (lhs , (mid , rhs) ∷ xs) = (lhs , mid , rhs) ∷ (flatten-trip (lhs , xs))

is-asc : List Nat → Bool
is-asc [] = true
is-asc (_ ∷ []) = true
is-asc (x ∷ y ∷ xs) = (x < y) ∧ is-asc (y ∷ xs)

first-sect-sum-h : Nat → Nat → List Nat → Nat → List (List Nat × List Nat)
first-sect-sum-h _ _ [] _ = []
first-sect-sum-h _ 0 _ _ = []
first-sect-sum-h _ (suc l) xs 0 = ([] , xs) ∷ []
first-sect-sum-h last (suc l) xs target = concat (complete ∷ (map (λ {(fst , tail) → add-front-each {Nat} fst tail}) next-layer))
  where
    new-targets : List (Nat × Nat × List Nat)
    new-targets = rem-from-target last target (each-one xs)
    complete : List (List Nat × List Nat)
    complete = map (λ {(_ , (a , b)) → (a ∷ []) , b}) (filterᵇ (λ {(nt , _) → nt ==n 0}) new-targets)
    inprogress : List (Nat × Nat × List Nat)
    inprogress = filterᵇ (λ {(nt , _) → 0 < nt}) new-targets
    next-layer : List (Nat × List (List Nat × List Nat))
    next-layer = map (λ {(nt , (fst , free)) → fst , (first-sect-sum-h fst l free nt)}) inprogress

first-sect-sum : List Nat → Nat → List (List Nat × List Nat)
first-sect-sum inp target = filterᵇ (λ {(l , r) → is-asc r ∧ (length l < suc (length r)) }) pairs
  where
    pairs : List (List Nat × List Nat)
    pairs = first-sect-sum-h 0 (div-nat (length inp) 2) inp target

three-sections : List Nat → Nat → List (List Nat × List Nat × List Nat)
three-sections inp target = concat (map flatten-trip triples)
  where
    pairs : List (List Nat × List Nat)
    pairs = first-sect-sum inp target
    triples : List (List Nat × List (List Nat × List Nat))
    triples = map (λ {(lhs , rhs) → lhs , (first-sect-sum rhs target)}) pairs

rank-triple : List Nat × List Nat × List Nat → Nat × Nat
rank-triple (lhs , _ , _) = (length lhs) , foldr _*_ 1 lhs

rank-cmp : (Nat × Nat) → (Nat × Nat) → Bool
rank-cmp (x , y) (a , b) = (x < a) ∨ ((x ==n a) ∧ (y < b))

one-valid : List Nat → Nat → Bool
one-valid _ 0 = true
one-valid [] _ = false
one-valid (x ∷ xs) target with (x ==n target)
one-valid (x ∷ xs) target | true = true
one-valid (x ∷ xs) target | false with (x < target)
one-valid (x ∷ xs) target | false | true = (one-valid xs (target - x)) ∨ (one-valid xs target)
one-valid (x ∷ xs) target | false | false = false

three-sections-bound : (Nat × Nat) → List (List Nat × List Nat) → Nat → (Nat × Nat)
three-sections-bound best [] target = best
three-sections-bound best ((lhs , rhs) ∷ xs) target = next-search
  where
    new-score : (Nat × Nat)
    new-score = rank-triple (lhs , [] , [])
    next-search : (Nat × Nat)
    next-search with (rank-cmp best new-score)
    next-search | true = three-sections-bound best xs target
    next-search | false = three-sections-bound new-score xs target
--    next-search | false with (one-valid rhs target)
--    next-search | false | false = three-sections-bound best xs target
--    next-search | false | true = three-sections-bound new-score xs target

show-list-pair : List Nat × List Nat → String
show-list-pair (lhs , rhs) = left ++ ":" ++ right
  where
    left : String
    left = intersperse "," (map show lhs)
    right : String
    right = intersperse "," (map show rhs)

show-list-trip : List Nat × List Nat × List Nat → String
show-list-trip (lhs , mhs , rhs) = left ++ ":" ++ mid ++ ":" ++ right
  where
    left : String
    left = intersperse "," (map show lhs)
    mid : String
    mid = intersperse "," (map show mhs)
    right : String
    right = intersperse "," (map show rhs)

find-min-rank : List Nat → Nat → (Nat × Nat)
find-min-rank inp divisions = three-sections-bound (length inp , (foldr _*_ 1 inp)) pairs target
  where
    total : Nat
    total = foldr _+_ 0 inp
    target : Nat
    target = (div-nat total divisions)
    pairs : List (List Nat × List Nat)
    pairs = first-sect-sum inp target

min-quantum : String → String
min-quantum x = output ++ "\n"
  where
    inp : List Nat
    inp = (unmaybe ∘ (map (readMaybe 10)) ∘ lines) x
    min-rank :(Nat × Nat)
    min-rank = find-min-rank inp 4
    output : String
    output with min-rank
    output | (c , q) = show c ++ ", " ++ show q

test-rem-from-target : rem-from-target 0 2 (each-one (1 ∷ 2 ∷ 3 ∷ [])) ≡ (1 , 1 , 2 ∷ 3 ∷ []) ∷ (0 , 2 , 1 ∷ 3 ∷ []) ∷ []
test-rem-from-target = refl

test-first-sect-sum : (unlines ∘ (map show-list-pair)) (first-sect-sum (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) 3) ≡
  "3:1,2,4\n1,2:3,4"
test-first-sect-sum = refl

test-one-valid-a : one-valid (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) 5 ≡ true
test-one-valid-a = refl

test-one-valid-b : one-valid (2 ∷ 3 ∷ []) 4 ≡ false
test-one-valid-b = refl

test-rank-cmp : rank-cmp (3 , 4) (4 , 1) ≡ true
test-rank-cmp = refl

test-rank-cmp-b : rank-cmp (3 , 4) (3 , 1) ≡ false
test-rank-cmp-b = refl

test-three-sections : (unlines ∘ (map show-list-trip)) (three-sections (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) 5) ≡
  "5:1,4:2,3\n5:2,3:1,4\n1,4:5:2,3\n2,3:5:1,4"
test-three-sections = refl

test-find-min-rank : find-min-rank (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) 3 ≡ (1 , 5)
test-find-min-rank = refl

test-find-min-rank-b : find-min-rank (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ []) 3 ≡ (2 , 99)
test-find-min-rank-b = refl
