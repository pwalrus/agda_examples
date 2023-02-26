module d18.autom where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; make-perms ; rem-dot)
open import util.lookup using (LookupStrTree ; build-str-tree ; has_val ; set_val ; all_values ; LTPair) renaming (read_val to read-tree)
open import util.json using (readIntMaybe)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using (_==_ ; _<?_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_) renaming (_==_ to _==n_ ; _-_ to nat-diff)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip)
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties renaming (_==_ to _==c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Function.Base using (_∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)

parse-line-ch : List Char → Maybe (List Bool)
parse-line-ch [] = just []
parse-line-ch (x ∷ xs) with (parse-line-ch xs)
parse-line-ch (x ∷ xs) | (just ys) = if (x ==c '.') then (just (false ∷ ys)) else( if (x ==c '#') then (just (true ∷ ys)) else nothing)
parse-line-ch (x ∷ xs) | nothing = nothing

parse-line : String → Maybe (List Bool)
parse-line = parse-line-ch ∘ toList

set-last : {A : Set} → A → List A → List A
set-last q [] = []
set-last q (x ∷ []) = q ∷ []
set-last q (x ∷ xs) = x ∷ (set-last q xs)

set-first : {A : Set} → A → List A → List A
set-first q [] = []
set-first q (x ∷ xs) = q ∷ xs

set-corners-last : List (List Bool) → List (List Bool)
set-corners-last [] = []
set-corners-last (x ∷ y ∷ xs) = x ∷ (set-corners-last (y ∷ xs))
set-corners-last (x ∷ []) = (set-first true) (set-last true x) ∷ []

set-corners-first : List (List Bool) → List (List Bool)
set-corners-first [] = []
set-corners-first (x ∷ xs) = (set-first true) (set-last true x) ∷ xs

set-corners : List (List Bool) → List (List Bool)
set-corners = set-corners-first ∘ set-corners-last

count-true : List Bool → Nat
count-true [] = 0
count-true (true ∷ xs) = suc (count-true xs)
count-true (false ∷ xs) = count-true xs

over-two : Bool → List Bool → Bool
over-two true x with (count-true x)
over-two true x | 0 = false
over-two true x | 1 = false
over-two true x | 2 = true
over-two true x | 3 = true
over-two true x | _ = false
over-two false x with (count-true x)
over-two false x | 0 = false
over-two false x | 1 = false
over-two false x | 2 = false
over-two false x | 3 = true
over-two false x | _ = false

zero-row : Nat → List Bool
zero-row 0 = []
zero-row (suc p) = false ∷ (zero-row p)

pad-left-right : List Bool → List Bool
pad-left-right x = concat ((false ∷ []) ∷ x ∷ (false ∷ []) ∷ [])

pad-grid : List (List Bool) → List (List Bool)
pad-grid x = map pad-left-right extra-rows
  where
    extra-rows : List (List Bool)
    extra-rows = concat ((zero-row (length x) ∷ []) ∷ x ∷ (zero-row (length x) ∷ []) ∷ [])

calc-next-row-h : (List Bool × List Bool × List Bool) → List Bool
calc-next-row-h (aa ∷ ab ∷ ac ∷ xs , ba ∷ bb ∷ bc ∷ ys , ca ∷ cb ∷ cc ∷ zs) = 
  over-two bb (aa ∷ ab ∷ ac ∷ ba ∷ bc ∷ ca ∷ cb ∷ cc ∷ []) ∷ calc-next-row-h ( ab ∷ ac ∷ xs , bb ∷ bc ∷ ys , cb ∷ cc ∷ zs)
calc-next-row-h _ = [] 

calc-next-h : List (List Bool) → List (List Bool)
calc-next-h (a ∷ b ∷ c ∷ xs) = (calc-next-row-h (a , b , c)) ∷ (calc-next-h (b ∷ c ∷ xs))
calc-next-h _ = []

calc-next : List (List Bool) → List (List Bool)
calc-next inp = calc-next-h padded
  where
    padded : List (List Bool)
    padded = pad-grid inp

show-row : List Bool → String
show-row [] = ""
show-row (false ∷ xs) = "0" ++ show-row xs
show-row (true ∷ xs) = "1" ++ show-row xs

iter-calc-next : Nat → List (List Bool) → List (List Bool)
iter-calc-next 0 grid = grid
iter-calc-next (suc p) grid = iter-calc-next p (calc-next grid)

iter-calc-next-b : Nat → List (List Bool) → List (List Bool)
iter-calc-next-b 0 grid = grid
iter-calc-next-b (suc p) grid = iter-calc-next-b p ((set-corners ∘ calc-next) grid)

step-through : String → String
step-through x = "sol: " ++ show (foldr _+_ 0 (map count-true new-grid)) ++ "\n"
  where
    grid : List (List Bool)
    grid = (unmaybe ∘ (map parse-line) ∘ lines) x
    new-grid : List (List Bool)
    new-grid = iter-calc-next 100 grid

step-through-b : String → String
step-through-b x = "sol: " ++ show (foldr _+_ 0 (map count-true new-grid)) ++ "\n"
  where
    grid : List (List Bool)
    grid = (unmaybe ∘ (map parse-line) ∘ lines) x
    new-grid : List (List Bool)
    new-grid = iter-calc-next-b 100 (set-corners grid)

test-pad-grid : (unlines ∘ (map show-row) ∘ pad-grid ∘ unmaybe ∘ (map parse-line) ∘ lines) "#.#\n...\n#.#" ≡ "00000\n01010\n00000\n01010\n00000"
test-pad-grid = refl

test-calc-next : (unlines ∘ (map show-row) ∘ calc-next ∘ unmaybe ∘ (map parse-line) ∘ lines) ".#.#.#\n...##.\n#....#\n..#...\n#.#..#\n####.." ≡ "001100\n001101\n000110\n000000\n100000\n101100"
test-calc-next = refl



