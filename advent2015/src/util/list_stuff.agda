
module util.list_stuff where

open import Agda.Builtin.String using (String)
open import Data.String.Base using (fromList ; toList)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Char.Base as Char using (Char)
open import Data.List.Base as List using (List; [_]; _∷_; [] ; reverse)
open import Data.List.NonEmpty.Base as NE using (List⁺)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe′)
open import Data.Nat.Base using (ℕ; _∸_; ⌊_/2⌋; ⌈_/2⌉)
open import Data.Nat.Show using (readMaybe)
open import Function.Base using (_on_; _∘′_; _∘_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)


trim-leading : List Char → List Char
trim-leading [] = []
trim-leading (' ' ∷ xs) = trim-leading xs
trim-leading (x ∷ xs) = x ∷ xs

trim-trailing : List Char → List Char
trim-trailing [] = []
trim-trailing (x ∷ xs) with (trim-trailing xs)
trim-trailing (x ∷ xs) | [] = x ∷ []
trim-trailing (x ∷ xs) | (' ' ∷ []) = x ∷ []
trim-trailing (x ∷ xs) | (y ∷ ys) = x ∷ y ∷ ys

trim : List Char → List Char
trim = trim-trailing ∘ trim-leading


-- Almost completed copied from std-lib. Its in the online version, but not the installed version?


filterᵇ : {A : Set} → (A → Bool) → List A → List A
filterᵇ p []       = []
filterᵇ p (x ∷ xs) = if p x then x ∷ filterᵇ p xs else filterᵇ p xs

parse_nat : String → ℕ
parse_nat x = def_zero (readMaybe 10 x)
  where
    def_zero : Maybe ℕ → ℕ
    def_zero (just q) = q
    def_zero _ = 0

ListlinesByᵇ : {A : Set} → (A → Bool) → List A → List (List A)
ListlinesByᵇ {A = A} p = go nothing
  where
  go : Maybe (List A) → List A → List (List A)
  go acc []       = maybe′ ([_] ∘′ reverse) [] acc
  go acc (c ∷ cs) with p c
  ... | true  = reverse (Maybe.fromMaybe [] acc) ∷ go nothing cs
  ... | false = go (just (c ∷ Maybe.fromMaybe [] acc)) cs

ListwordsByᵇ : {A : Set} → (A → Bool) → List A → List (List A)
ListwordsByᵇ {A = A} p = go []
  where
  cons : List A → List (List A) → List (List A)
  cons [] ass = ass
  cons as ass = reverse as ∷ ass

  go : List A → List A → List (List A)
  go acc []       = cons acc []
  go acc (c ∷ cs) with p c
  ... | true  = cons acc (go [] cs)
  ... | false = go (c ∷ acc) cs

wordsByᵇ : (Char → Bool) → String → List String
wordsByᵇ p = List.map fromList ∘ ListwordsByᵇ p ∘ toList

words : String → List String
words = wordsByᵇ Char.isSpace

-- `words` ignores contiguous whitespace
_ : words " abc  b   " ≡ "abc" ∷ "b" ∷ []
_ = refl

linesByᵇ : (Char → Bool) → String → List String
linesByᵇ p = List.map fromList ∘ ListlinesByᵇ p ∘ toList

lines : String → List String
lines = linesByᵇ ('\n' Char.≈ᵇ_)

unmaybe : {A : Set} → List (Maybe A) → List A
unmaybe [] = []
unmaybe ((just x) ∷ xs) = x ∷ (unmaybe xs)
unmaybe (nothing ∷ xs) = unmaybe xs

test-trim : (fromList ∘ trim ∘ toList) "    abc d   " ≡ "abc d"
test-trim = refl
