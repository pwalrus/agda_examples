
module d8.escape where

open import util.list_stuff using (words ; lines ; parse-nat)
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

rem-lst-q : List Char → List Char
rem-lst-q [] = []
rem-lst-q ('"' ∷ []) = []
rem-lst-q (x ∷ xs) = x ∷ (rem-lst-q xs)

rem-fst-q : List Char → List Char
rem-fst-q ('"' ∷ xs) = xs
rem-fst-q x = x

remove-quotes : List Char → List Char
remove-quotes = rem-fst-q ∘ rem-lst-q

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

single-rel-size : List Char -> Nat
single-rel-size inp = (length inp) - ((length ∘ remove-quotes ∘ unescape) inp)

single-rel-size-rev : List Char -> Nat
single-rel-size-rev inp = ((length ∘ requote ∘ escape) inp) - (length inp)

rel-size : String → String
rel-size x = show (foldr _+_ 0 (map (single-rel-size ∘ toList) (lines x)))

rel-size-rev : String → String
rel-size-rev x = show (foldr _+_ 0 (map (single-rel-size-rev ∘ toList) (lines x)))

test-rem-q : (fromList ∘ remove-quotes ∘ toList) "\"c\"" ≡ "c"
test-rem-q = refl

test-rel-size : rel-size "\"\"\n\"abc\"\n\"aaa\\\"aaa\"\n\"\\x27\"" ≡ "12"
test-rel-size = refl

test-rel-size-rev : rel-size-rev "\"\"\n\"abc\"\n\"aaa\\\"aaa\"\n\"\\x27\"" ≡ "19"
test-rel-size-rev = refl
