
module d1.enter where

open import Data.Bool.Base using (if_then_else_)
open import Agda.Builtin.String using (String ; primStringToList )
open import Data.String using (_++_)
open import Agda.Builtin.Nat using (Nat ; suc)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)

open import Data.Integer.Base using (_+_ ; _-_)
open import Data.Integer.Properties using (_≟_)

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Show using (show)
open import Agda.Builtin.List using (List; _∷_ ; [])
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties using (_==_)
open import Relation.Nullary.Decidable.Core using (isYes)
open import Agda.Builtin.Equality using (refl ; _≡_)


is-neg-one : Int -> Nat -> Nat -> Nat
is-neg-one i y n = if isYes ((negsuc 0) ≟ i) then y else n

find-enter-ch : List Char -> Int -> Nat -> Nat
find-enter-ch [] start idx = is-neg-one start idx 0 
find-enter-ch ( x ∷ xs ) start idx = is-neg-one start idx (
  if x == '(' then find-enter-ch xs (start + pos 1) (suc idx)
  else (if x == ')' then find-enter-ch xs (start - pos 1) (suc idx)
  else find-enter-ch xs start (suc idx)))

count-enters : String → String
count-enters x = show (find-enter-ch (primStringToList x) (pos 0) 0) ++ "\n"

test-count-enters : count-enters "()())" ≡ "5\n"
test-count-enters = refl
