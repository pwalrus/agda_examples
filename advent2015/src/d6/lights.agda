module d6.lights where

open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Agda.Builtin.Nat using (Nat ; suc)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.String using (String ; primStringToList; primStringFromList)

populate_empty_row : Nat → List Bool
populate_empty_row 0 = []
populate_empty_row (suc n) = false ∷ (populate_empty_row n)

populate_empty : Nat → Nat → List (List Bool)
populate_empty 0 width = []
populate_empty (suc n) width = (populate_empty_row width) ∷ (populate_empty n width)


lights_on : String → String
lights_on x = x
