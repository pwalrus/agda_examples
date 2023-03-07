

module d9.tsm where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; make-perms ; unique-insert-str ; min-by-fm)
open import util.lookup using (LookupTree ; build_tree ; has_val ; set_val ; all_values) renaming (read_val to read_tree)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; _+_ ; suc ; _<_)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Bool using (Bool)
open import Data.Bool.Base using (if_then_else_ ; _∨_ ; _∧_)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Function.Base using (_∘_)
open import Data.Product using (_×_ ; _,_)
open import Agda.Builtin.Equality using (refl ; _≡_)


data Link : Set where
  link : String → String → Nat → Link

is-match : String → String → Link → Bool
is-match x y (link lhs rhs _) = ((x == lhs) ∧ (y == rhs)) ∨ ((y == lhs) ∧ (x == rhs))

show-link : Link → String
show-link (link lhs rhs d) = lhs ++ " to " ++ rhs ++ " = " ++ (show d) 

parse-line-w : List String →  Maybe Link
parse-line-w (lhs ∷ "to" ∷ rhs ∷ "=" ∷ d ∷ _) with (readMaybe 10 d)
parse-line-w (lhs ∷ "to" ∷ rhs ∷ "=" ∷ d ∷ _) | nothing = nothing
parse-line-w (lhs ∷ "to" ∷ rhs ∷ "=" ∷ d ∷ _) | (just x) = just (link lhs rhs x)
parse-line-w _ = nothing

parse-line : String → Maybe Link
parse-line x = parse-line-w ( words x)

unique-cities : List Link → List String
unique-cities ((link lhs rhs _) ∷ xs) = unique-insert-str (unique-insert-str (unique-cities xs) lhs) rhs
unique-cities _ = []

lookup-pair : String → String → List Link → Maybe Nat
lookup-pair x y db with (filterᵇ (λ {q → is-match x y q}) db)
lookup-pair x y db | [] = nothing
lookup-pair x y db | (link _ _ d) ∷ _ = just d

rank-path : Nat → List String → List Link → Maybe Nat
rank-path 0 _ _ = nothing
rank-path (suc l) (x ∷ y ∷ xs) db with (lookup-pair x y db)
rank-path (suc l) (x ∷ y ∷ xs) db | (just part) with rank-path l (y ∷ xs) db
rank-path (suc l) (x ∷ y ∷ xs) db | (just part) | (just rest) = just (part + rest)
rank-path (suc l) (x ∷ y ∷ xs) db | (just part) | nothing = nothing
rank-path (suc l) (x ∷ y ∷ xs) db | nothing = nothing
rank-path _ _ _ = just 0

show-path : List String → List Link → String
show-path cities db with (rank-path (suc (length cities)) cities db)
show-path cities db | just score = (foldr _++_ "" cities) ++ " = " ++ (show score)
show-path cities db | nothing = (foldr _++_ "" cities) ++ " is invalid"

maybe-show-path : Maybe (List String) → List Link → String
maybe-show-path nothing _ = "none found"
maybe-show-path (just p) db = show-path p db

min-path : List (List String) → List Link -> Maybe (List String)
min-path x db = min-by-fm (suc (length x)) x
  λ {b → (rank-path (suc (length b)) b db)}

shortest : String → String
shortest x = maybe-show-path mp db
  where
    db : List Link
    db = unmaybe (map parse-line (lines x))
    cities : List String
    cities = unique-cities db
    perms : List (List String)
    perms = make-perms cities
    mp : Maybe (List String)
    mp = min-path perms db

test-parse-line : parse-line "A to B = 3" ≡ just (link "A" "B" 3)
test-parse-line = refl

test-rank-a : rank-path 4 ("A" ∷ "B" ∷ "C" ∷ []) ((link "A" "B" 2) ∷ (link "C" "B" 3) ∷ []) ≡ just 5
test-rank-a = refl


test-unmaybe : unmaybe (map parse-line (lines  "A to B = 3\nC to B = 2")) ≡ (link "A" "B" 3) ∷ (link "C" "B" 2) ∷ []
test-unmaybe = refl

test-unique-cities : unique-cities ((link "A" "B" 3) ∷ (link "C" "B" 2) ∷ []) ≡ "C" ∷ "B" ∷ "A" ∷ []
test-unique-cities = refl
