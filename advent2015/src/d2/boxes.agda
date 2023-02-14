
module d2.boxes where

open import Data.Bool.Base using (if_then_else_)
open import Agda.Builtin.String using (String ; primStringToList )
open import Data.String using (_++_)

open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Agda.Builtin.Nat using (Nat ; _<_)
open import Data.Nat.Base using (_+_ ; _*_)
open import Data.Nat.Show using (show)

open import Agda.Builtin.List using (List; _∷_ ; [])
open import Data.List.Base using (map ; foldr ; concat)
open import Agda.Builtin.Char using (Char ; primCharToNat)
open import Data.Char.Properties using (_==_)

add_char : List (List Char) → Char → List (List Char)
add_char [] ch = (ch ∷ []) ∷ []
add_char (x ∷ xs) ch with x 
add_char (x ∷ xs) ch    | [] = (ch ∷ []) ∷ xs
add_char (x ∷ xs) ch    | (y ∷ ys) = (ch ∷ y ∷ ys) ∷ xs

is_digit : Char → Bool
is_digit '0' = true
is_digit '1' = true
is_digit '2' = true
is_digit '3' = true
is_digit '4' = true
is_digit '5' = true
is_digit '6' = true
is_digit '7' = true
is_digit '8' = true
is_digit '9' = true
is_digit _ = false

parse_digit : Char → Nat
parse_digit '0' = 0
parse_digit '1' = 1
parse_digit '2' = 2
parse_digit '3' = 3
parse_digit '4' = 4
parse_digit '5' = 5
parse_digit '6' = 6
parse_digit '7' = 7
parse_digit '8' = 8
parse_digit '9' = 9
parse_digit _ = 0

parse_nat : Nat -> List Char → Nat
parse_nat start [] = start
parse_nat start (x ∷ xs) = if (is_digit x)
   then (parse_nat (10 * start + (parse_digit x)) xs)
   else (parse_nat start xs)

find_parts : Char → List Char → List (List Char)
find_parts delim [] = []
find_parts delim (x ∷ xs) = if x == delim then [] ∷ (find_parts delim xs) else add_char (find_parts delim xs) x

nat_parts : List (List Char) → List Nat
nat_parts [] = []
nat_parts (x ∷ xs) = (parse_nat 0 x) ∷ nat_parts xs

mult_pair_products : Nat → List Nat → List Nat
mult_pair_products a [] = []
mult_pair_products a (x ∷ xs) = (a * x) ∷ (mult_pair_products a xs)

all_pair_products : List Nat → List Nat
all_pair_products [] = []
all_pair_products (x ∷ xs) = concat ( (mult_pair_products x xs) ∷ (all_pair_products xs) ∷ [] )

min_of_list : Nat → List Nat → Nat
min_of_list m [] = m
min_of_list m (x ∷ xs) = if x < m then min_of_list x xs else min_of_list m xs

combine_parts : List Nat → Nat
combine_parts parts = (foldr _+_ 0 (all_pair_products parts) * 2) + min_of_list 10000 (all_pair_products parts)

parse_and_calc : List Char -> Nat
parse_and_calc x = combine_parts ( nat_parts ( find_parts 'x' x)) 

parse_and_calc_all : String -> Nat
parse_and_calc_all inp = foldr _+_ 0 (map parse_and_calc (find_parts '\n' (primStringToList inp)))

calc_size : String → String
calc_size x = show ( parse_and_calc_all x ) ++ "\n"
