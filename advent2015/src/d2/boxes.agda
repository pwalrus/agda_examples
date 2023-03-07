
module d2.boxes where

open import util.list_stuff using (trim)
open import Data.Bool.Base using (if_then_else_)
open import Agda.Builtin.String using (String ; primStringToList ; primStringFromList)
open import Data.String using (_++_)

open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Agda.Builtin.Nat using (Nat ; _<_)
open import Data.Nat.Base using (_+_ ; _*_)
open import Data.Nat.Show using (show ; readMaybe)

open import Agda.Builtin.List using (List; _∷_ ; [])
open import Data.List.Base using (map ; foldr ; concat)
open import Agda.Builtin.Char using (Char ; primCharToNat)
open import Agda.Builtin.Maybe using (Maybe ; just ; nothing)
open import Data.Char.Properties using (_==_)
open import Agda.Builtin.Equality using (refl ; _≡_)


add-char : List (List Char) → Char → List (List Char)
add-char [] ch = (ch ∷ []) ∷ []
add-char (x ∷ xs) ch with x 
add-char (x ∷ xs) ch    | [] = (ch ∷ []) ∷ xs
add-char (x ∷ xs) ch    | (y ∷ ys) = (ch ∷ y ∷ ys) ∷ xs

parse-nat : List Char → Nat
parse-nat x with (readMaybe 10 (primStringFromList x))
parse-nat x | nothing = 0
parse-nat x | (just y) = y

find-parts : Char → List Char → List (List Char)
find-parts delim [] = []
find-parts delim (x ∷ xs) = if x == delim then [] ∷ (find-parts delim xs) else add-char (find-parts delim xs) x

nat-parts : List (List Char) → List Nat
nat-parts [] = []
nat-parts (x ∷ xs) = (parse-nat x) ∷ nat-parts xs

mult-pair-products : Nat → List Nat → List Nat
mult-pair-products a [] = []
mult-pair-products a (x ∷ xs) = (a * x) ∷ (mult-pair-products a xs)

all-pair-products : List Nat → List Nat
all-pair-products [] = []
all-pair-products (x ∷ xs) = concat ( (mult-pair-products x xs) ∷ (all-pair-products xs) ∷ [] )

min-of-list : Nat → List Nat → Nat
min-of-list m [] = m
min-of-list m (x ∷ xs) = if x < m then min-of-list x xs else min-of-list m xs

combine-parts : List Nat → Nat
combine-parts parts = (foldr _+_ 0 (all-pair-products parts) * 2) + min-of-list 10000 (all-pair-products parts)

parse-and-calc : List Char -> Nat
parse-and-calc x = combine-parts ( nat-parts ( find-parts 'x' x)) 

parse-and-calc-all : String -> Nat
parse-and-calc-all inp = foldr _+_ 0 (map parse-and-calc (find-parts '\n' (primStringToList inp)))

calc-size-box : String → String
calc-size-box x = show ( parse-and-calc-all x ) ++ "\n"

test-calc-size-box-a : parse-and-calc (primStringToList "2x3x4") ≡ 58
test-calc-size-box-a = refl

test-calc-size-box-b : parse-and-calc (primStringToList "1x1x10") ≡ 43
test-calc-size-box-b = refl
