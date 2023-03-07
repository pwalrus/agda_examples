
module d1.floors where

open import Data.Bool.Base using (if_then_else_)
open import Agda.Builtin.String using (String ; primStringToList )
open import Data.String using (_++_)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using (_+_ ; _-_)
open import Data.Integer.Show using (show)
open import Agda.Builtin.List using (List; _∷_ ; [])
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties using (_==_)
open import Agda.Builtin.Equality using (refl ; _≡_)


count-moves-ch : List Char -> Int
count-moves-ch [] = pos 0
count-moves-ch ( x ∷ xs ) =
  if x == '(' then (count-moves-ch xs) + pos 1
  else (if x == ')' then (count-moves-ch xs) - pos 1
  else count-moves-ch xs)


count-moves : String → String
count-moves x = show (count-moves-ch (primStringToList x)) ++ "\n"

test-count-moves-a : count-moves "(())" ≡ "0\n"
test-count-moves-a = refl

test-count-moves-b : count-moves "(()(()(" ≡ "3\n"
test-count-moves-b = refl

test-count-moves-c : count-moves ")())())" ≡ "-3\n"
test-count-moves-c = refl
