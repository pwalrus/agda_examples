
module d8.escape where

open import util.list_stuff using (words ; lines ; parse_nat)
open import Agda.Builtin.Char using (Char ; primNatToChar )
open import Agda.Builtin.Nat using (Nat ; suc ; _+_ ; _-_)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.List using (List ; _∷_ ; [])
open import Data.List.Base using (length; map; foldr; _++_)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Agda.Builtin.Maybe using (Maybe ; just ; nothing)
open import Function.Base using (_∘_)

rem_lst_q : List Char → List Char
rem_lst_q [] = []
rem_lst_q ('"' ∷ []) = []
rem_lst_q (x ∷ xs) = x ∷ (rem_lst_q xs)

rem_fst_q : List Char → List Char
rem_fst_q ('"' ∷ xs) = xs
rem_fst_q x = x

remove_quotes : List Char → List Char
remove_quotes = rem_fst_q ∘ rem_lst_q

requote : List Char → List Char
requote x = ('"' ∷ x) ++ ('"' ∷ [])

unescape : List Char → List Char
unescape [] = []
unescape ('\\' ∷ '"' ∷ xs) = '"' ∷ (unescape xs)
unescape ('\\' ∷ '\\' ∷ xs) = '\\' ∷ (unescape xs)
unescape ('\\' ∷ 'x' ∷ a ∷ b ∷ xs) with (readMaybe 16 (fromList (a ∷ b ∷ [])))
unescape ('\\' ∷ 'x' ∷ a ∷ b ∷ xs) | nothing = a ∷ b ∷ (unescape xs)
unescape ('\\' ∷ 'x' ∷ a ∷ b ∷ xs) | (just x) = (primNatToChar x) ∷ (unescape xs)
unescape (x ∷ xs) = x ∷ (unescape xs)

escape : List Char → List Char
escape [] = []
escape ('"' ∷ xs) = '\\' ∷ '"' ∷ (escape xs)
escape ('\\' ∷ xs) = '\\' ∷ '\\' ∷ (escape xs)
escape (x ∷ xs) = x ∷ (escape xs)

single_rel_size : List Char -> Nat
single_rel_size inp = (length inp) - ((length ∘ remove_quotes ∘ unescape) inp)

single_rel_size_rev : List Char -> Nat
single_rel_size_rev inp = ((length ∘ requote ∘ escape) inp) - (length inp)

rel_size : String → String
rel_size x = show (foldr _+_ 0 (map (single_rel_size ∘ toList) (lines x)))

rel_size_rev : String → String
rel_size_rev x = show (foldr _+_ 0 (map (single_rel_size_rev ∘ toList) (lines x)))

test_rem_q : (fromList ∘ remove_quotes ∘ toList) "\"c\"" ≡ "c"
test_rem_q = refl

test_rel_size : rel_size "\"\"\n\"abc\"\n\"aaa\\\"aaa\"\n\"\\x27\"" ≡ "12"
test_rel_size = refl

test_rel_size_rev : rel_size_rev "\"\"\n\"abc\"\n\"aaa\\\"aaa\"\n\"\\x27\"" ≡ "19"
test_rel_size_rev = refl
