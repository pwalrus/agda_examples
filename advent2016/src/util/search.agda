
module util.search where

open import util.list_stuff using (filterᵇ)
open import util.lookup using (LookupStrTree ; build-str-tree ; has-val ; set-val ; all-kv)
open import Agda.Builtin.List using (List ; _∷_ ; [])
open import Data.List using (concat ; foldr ; cartesianProductWith ; map)
open import Agda.Builtin.Bool using (Bool ; false ; true)
open import Agda.Builtin.Nat using (Nat ; suc ; _+_ ; _<_ ; _==_)
open import Agda.Builtin.Maybe using (Maybe ; just ; nothing)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Agda.Builtin.String using (String)
open import Data.String using (intersperse)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Function.Base using (_∘_)

search-rec-depth : {A : Set} → Nat → (A → Bool) → (A → List A) → List A → Maybe (A)
search-rec-depth 0 _ _ _ = nothing
search-rec-depth (suc lm) done-cond mk-child currents with (currents)
search-rec-depth (suc lm) done-cond mk-child currents | [] = nothing
search-rec-depth (suc lm) done-cond mk-child currents | (current ∷ rest) with (done-cond current)
search-rec-depth (suc lm) done-cond mk-child currents | (current ∷ rest) | true = just current
search-rec-depth (suc lm) done-cond mk-child currents | (current ∷ rest) | false with (mk-child current)
search-rec-depth (suc lm) done-cond mk-child currents | (current ∷ rest) | false | deeper = search-rec-depth lm done-cond mk-child (concat (deeper ∷ rest ∷ []))


search-rec-breadth : {A : Set} → Nat → (A → Bool) → (A → List A) → List A → Maybe (A)
search-rec-breadth 0 _ _ _ = nothing
search-rec-breadth (suc lm) done-cond mk-child currents with (currents)
search-rec-breadth (suc lm) done-cond mk-child currents | [] = nothing
search-rec-breadth (suc lm) done-cond mk-child currents | (current ∷ rest) with (done-cond current)
search-rec-breadth (suc lm) done-cond mk-child currents | (current ∷ rest) | true = just current
search-rec-breadth (suc lm) done-cond mk-child currents | (current ∷ rest) | false with (mk-child current)
search-rec-breadth (suc lm) done-cond mk-child currents | (current ∷ rest) | false | deeper = search-rec-breadth lm done-cond mk-child (concat (rest ∷ deeper ∷ []))

search-rec-all : {A : Set} → Nat → (A → Bool) → (A → List A) → List A → List A
search-rec-all 0 _ _ _ = []
search-rec-all (suc lm) done-cond mk-child currents with (currents)
search-rec-all (suc lm) done-cond mk-child currents | [] = []
search-rec-all (suc lm) done-cond mk-child currents | (current ∷ rest) with (done-cond current)
search-rec-all (suc lm) done-cond mk-child currents | (current ∷ rest) | true with (mk-child current)
search-rec-all (suc lm) done-cond mk-child currents | (current ∷ rest) | true | deeper = current ∷ (search-rec-all lm done-cond mk-child (concat (rest ∷ [])))
search-rec-all (suc lm) done-cond mk-child currents | (current ∷ rest) | false with (mk-child current)
search-rec-all (suc lm) done-cond mk-child currents | (current ∷ rest) | false | deeper = search-rec-all lm done-cond mk-child (concat (rest ∷ deeper ∷ []))


search-rec-breadth-dedup-h : {A : Set} → Nat → (A → String) → LookupStrTree Bool → (A → Bool) → (A → List A) → List A → (Maybe (A) × LookupStrTree Bool)
search-rec-breadth-dedup-h 0 _ known _ _ _ = nothing , known
search-rec-breadth-dedup-h (suc lm) dedup known done-cond mk-child currents with (currents)
search-rec-breadth-dedup-h (suc lm) dedup known done-cond mk-child currents | [] = nothing , known
search-rec-breadth-dedup-h (suc lm) dedup known done-cond mk-child currents | (current ∷ rest) with (done-cond current)
search-rec-breadth-dedup-h (suc lm) dedup known done-cond mk-child currents | (current ∷ rest) | true = just current , known
search-rec-breadth-dedup-h (suc lm) dedup known done-cond mk-child currents | (current ∷ rest) | false with (has-val (dedup current) known)
search-rec-breadth-dedup-h (suc lm) dedup known done-cond mk-child currents | (current ∷ rest) | false | false with (mk-child current)
search-rec-breadth-dedup-h (suc lm) dedup known done-cond mk-child currents | (current ∷ rest) | false | false | deeper = search-rec-breadth-dedup-h lm dedup (set-val (dedup current) true known) done-cond mk-child (concat (rest ∷ deeper ∷ []))
search-rec-breadth-dedup-h (suc lm) dedup known done-cond mk-child currents | (current ∷ rest) | false | true = search-rec-breadth-dedup-h lm dedup known done-cond mk-child rest


search-rec-breadth-dedup : {A : Set} → Nat → (A → String) → (A → Bool) → (A → List A) → List A → Maybe (A) × LookupStrTree Bool
search-rec-breadth-dedup lm dedup done-cond mk-child currents = search-rec-breadth-dedup-h lm dedup (build-str-tree (("" , false) ∷ [])) done-cond mk-child currents

private
  add-coin : List Nat → List (List Nat)
  add-coin xs = (25 ∷ xs) ∷ (10 ∷ xs) ∷ (5 ∷ xs) ∷ (1 ∷ xs) ∷ []

  valid-change : Nat → List Nat → Bool
  valid-change lim xs = (foldr _+_ 0 xs) < suc lim

  add-valid-coins : Nat → List Nat → List (List Nat)
  add-valid-coins lim xs = filterᵇ (valid-change lim) (add-coin xs)

  valid-sol : Nat → List Nat → Bool
  valid-sol lim xs = lim == foldr _+_ 0 xs

test-make-change : search-rec-depth 10 (valid-sol 73) (add-valid-coins 73) ([] ∷ []) ≡ just (1 ∷ 1 ∷ 1 ∷ 10 ∷ 10 ∷ 25 ∷ 25 ∷ [])
test-make-change = refl


private

  sample-graph : String → List String
  sample-graph "A" = "B" ∷ "C" ∷ []
  sample-graph "B" = "D" ∷ []
  sample-graph "C" = "E" ∷ []
  sample-graph "D" = "E" ∷ []
  sample-graph _ = []

  graph-end : List String → Bool
  graph-end ("E" ∷ _) = true
  graph-end _ = false

  next-steps : List String → List (List String)
  next-steps [] = ("A" ∷ []) ∷ []
  next-steps (x ∷ xs) = map (λ {q → q ∷ x ∷ xs}) (sample-graph x)

  show-loc : List String → String
  show-loc [] = "[]"
  show-loc (x ∷ _) = x

test-find-shortest : search-rec-breadth 10 graph-end next-steps ([] ∷ []) ≡ just ("E" ∷ "C" ∷ "A" ∷ [])
test-find-shortest = refl


test-find-shortest-dedup-l : proj₁ (search-rec-breadth-dedup 10 show-loc graph-end next-steps ([] ∷ [])) ≡ just ("E" ∷ "C" ∷ "A" ∷ [])
test-find-shortest-dedup-l = refl

test-find-shortest-dedup-r : (intersperse "," ∘ map proj₁ ∘ all-kv ∘ proj₂) (search-rec-breadth-dedup 10 show-loc graph-end next-steps ([] ∷ [])) ≡ "[],D,C,B,A,"
test-find-shortest-dedup-r = refl

test-find-all : search-rec-all 100 graph-end next-steps ([] ∷ []) ≡ ("E" ∷ "C" ∷ "A" ∷ []) ∷ ("E" ∷ "D" ∷ "B" ∷ "A" ∷ []) ∷ []
test-find-all = refl


