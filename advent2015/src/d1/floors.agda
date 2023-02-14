
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

count_moves_ch : List Char -> Int
count_moves_ch [] = pos 0
count_moves_ch ( x ∷ xs ) =
  if x == '(' then (count_moves_ch xs) + pos 1
  else (if x == ')' then (count_moves_ch xs) - pos 1
  else count_moves_ch xs)


count_moves : String → String
count_moves x = show (count_moves_ch (primStringToList x)) ++ "\n"

