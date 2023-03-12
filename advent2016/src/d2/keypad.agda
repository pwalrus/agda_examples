module d2.keypad where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; each-one ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; split) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; LookupNatTree ; build-str-tree ; build-nat-tree ; has-val ; all-values ; all-keys ; all-kv ; LTPair) renaming (set-val to set-tree ; read-val to read-tree)
open import util.json using (readIntMaybe ; rem-lst-c)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using (_==_ ; _<?_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using (_≤ᵇ_) renaming (_+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Properties using (_≟_)
open import Data.Integer.Show using () renaming (show to showz)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip)
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties renaming (_==_ to _==c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Function.Base using (_∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


data Direction : Set where
  U : Direction
  L : Direction
  R : Direction
  D : Direction

move : Nat → Direction → Nat
move 1 R = 2
move 1 D = 4
move 2 L = 1
move 2 R = 3
move 2 D = 5
move 3 D = 6
move 3 L = 2
move 4 U = 1
move 4 R = 5
move 4 D = 7
move 5 U = 2
move 5 L = 4
move 5 R = 6
move 5 D = 8
move 6 U = 3
move 6 L = 5
move 6 D = 9
move 7 U = 4
move 7 R = 8
move 8 L = 7
move 8 U = 5
move 8 R = 9
move 9 L = 8
move 9 U = 6
move x _ = x

move2 : Char → Direction → Char
move2 '1' D = '3'
move2 '2' R = '3'
move2 '2' D = '6'
move2 '3' U = '1'
move2 '3' L = '2'
move2 '3' R = '4'
move2 '3' D = '7'
move2 '4' L = '3'
move2 '4' D = '8'
move2 '5' R = '6'
move2 '6' U = '2'
move2 '6' L = '5'
move2 '6' R = '7'
move2 '6' D = 'A'
move2 '7' U = '3'
move2 '7' L = '6'
move2 '7' R = '8'
move2 '7' D = 'B'
move2 '8' U = '4'
move2 '8' L = '7'
move2 '8' R = '9'
move2 '8' D = 'C'
move2 '9' L = '8'
move2 'A' R = 'B'
move2 'A' U = '6'
move2 'B' U = '7'
move2 'B' L = 'A'
move2 'B' R = 'C'
move2 'B' D = 'D'
move2 'C' U = '8'
move2 'C' L = 'B'
move2 'D' U = 'B'
move2 x _ = x


parse-line-ch : List Char → List Direction
parse-line-ch [] = []
parse-line-ch ('U' ∷ xs) = U ∷ (parse-line-ch xs)
parse-line-ch ('L' ∷ xs) = L ∷ (parse-line-ch xs)
parse-line-ch ('R' ∷ xs) = R ∷ (parse-line-ch xs)
parse-line-ch ('D' ∷ xs) = D ∷ (parse-line-ch xs)
parse-line-ch (_ ∷ xs) = (parse-line-ch xs)

parse-line : String → List Direction
parse-line = parse-line-ch ∘ toList

apply-sequence : {A : Set} → (A → Direction → A) → A → List Direction → A
apply-sequence f start [] = start
apply-sequence f start (x ∷ xs) = apply-sequence f (f start x) xs

apply-multi-sequence : {A : Set} → (A → Direction → A) → A → List (List Direction) → List A
apply-multi-sequence f _ [] = []
apply-multi-sequence f start (x ∷ xs) = (apply-sequence f start x) ∷ (apply-multi-sequence f (apply-sequence f start x) xs)

find-sequence : String → String
find-sequence x = intersperse "" (map show codes) ++ "\n"
  where
    paths : List (List Direction)
    paths = ((map parse-line) ∘ lines) x
    codes : List Nat
    codes = apply-multi-sequence move 5 paths

find-sequence2 : String → String
find-sequence2 x = (fromList codes) ++ "\n"
  where
    paths : List (List Direction)
    paths = ((map parse-line) ∘ lines) x
    codes : List Char
    codes = apply-multi-sequence move2 '5' paths

test-apply-sequence-a : apply-sequence move 5 (parse-line "ULL") ≡ 1
test-apply-sequence-a = refl

test-apply-sequence-b : apply-sequence move 1 (parse-line "RRDDD") ≡ 9
test-apply-sequence-b = refl

test-apply-sequence-c : apply-sequence move 9 (parse-line "LURDL") ≡ 8
test-apply-sequence-c = refl

test-apply-sequence-d : apply-sequence move 8 (parse-line "UUUUD") ≡ 5
test-apply-sequence-d = refl

test-apply-multi-sequence : find-sequence "ULL\nRRDDD\nLURDL\nUUUUD" ≡ "1985\n"
test-apply-multi-sequence = refl

test-apply-multi-sequence2 : find-sequence2 "ULL\nRRDDD\nLURDL\nUUUUD" ≡ "5DB3\n"
test-apply-multi-sequence2 = refl
