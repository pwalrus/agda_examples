

module d9.tsm where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; make-perms)
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

is_match : String → String → Link → Bool
is_match x y (link lhs rhs _) = ((x == lhs) ∧ (y == rhs)) ∨ ((y == lhs) ∧ (x == rhs))

show_link : Link → String
show_link (link lhs rhs d) = lhs ++ " to " ++ rhs ++ " = " ++ (show d) 

parse_line_w : List String →  Maybe Link
parse_line_w (lhs ∷ "to" ∷ rhs ∷ "=" ∷ d ∷ _) with (readMaybe 10 d)
parse_line_w (lhs ∷ "to" ∷ rhs ∷ "=" ∷ d ∷ _) | nothing = nothing
parse_line_w (lhs ∷ "to" ∷ rhs ∷ "=" ∷ d ∷ _) | (just x) = just (link lhs rhs x)
parse_line_w _ = nothing

parse_line : String → Maybe Link
parse_line x = parse_line_w ( words x)

unique_insert_str : List String → String → List String
unique_insert_str [] l = l ∷ []
unique_insert_str (x ∷ xs) l = if ( x == l)
   then x ∷ xs
   else x ∷ (unique_insert_str xs l)

unique_cities : List Link → List String
unique_cities ((link lhs rhs _) ∷ xs) = unique_insert_str (unique_insert_str (unique_cities xs) lhs) rhs
unique_cities _ = []

lookup_pair : String → String → List Link → Maybe Nat
lookup_pair x y db with (filterᵇ (λ {q → is_match x y q}) db)
lookup_pair x y db | [] = nothing
lookup_pair x y db | (link _ _ d) ∷ _ = just d

rank_path : Nat → List String → List Link → Maybe Nat
rank_path 0 _ _ = nothing
rank_path (suc l) (x ∷ y ∷ xs) db with (lookup_pair x y db)
rank_path (suc l) (x ∷ y ∷ xs) db | (just part) with rank_path l (y ∷ xs) db
rank_path (suc l) (x ∷ y ∷ xs) db | (just part) | (just rest) = just (part + rest)
rank_path (suc l) (x ∷ y ∷ xs) db | (just part) | nothing = nothing
rank_path (suc l) (x ∷ y ∷ xs) db | nothing = nothing
rank_path _ _ _ = just 0

show_path : List String → List Link → String
show_path cities db with (rank_path (suc (length cities)) cities db)
show_path cities db | just score = (foldr _++_ "" cities) ++ " = " ++ (show score)
show_path cities db | nothing = (foldr _++_ "" cities) ++ " is invalid"

maybe_show_path : Maybe (List String) → List Link → String
maybe_show_path nothing _ = "none found"
maybe_show_path (just p) db = show_path p db

min_by_func : {A : Set} → Nat → List A → (A → Maybe Nat) → Maybe A
min_by_func 0 _ _ = nothing
min_by_func (suc l) [] f = nothing
min_by_func (suc l) (x ∷ []) f = just x
min_by_func (suc l) (x ∷ y ∷ xs) f with (f x)
min_by_func (suc l) (x ∷ y ∷ xs) f | (just xr) with (f y)
min_by_func (suc l) (x ∷ y ∷ xs) f | (just xr) | (just yr) = if (xr < yr) then (min_by_func l (x ∷ xs) f) else (min_by_func l (y ∷ xs) f)
min_by_func (suc l) (x ∷ y ∷ xs) f | (just xr) | nothing = nothing
min_by_func (suc l) (x ∷ y ∷ xs) f | nothing = nothing

min_path : List (List String) → List Link -> Maybe (List String)
min_path x db = min_by_func (suc (length x)) x
  λ {b → (rank_path (suc (length b)) b db)}


shortest : String → String
shortest x = maybe_show_path mp db
  where
    db : List Link
    db = unmaybe (map parse_line (lines x))
    cities : List String
    cities = unique_cities db
    perms : List (List String)
    perms = make-perms cities
    mp : Maybe (List String)
    mp = min_path perms db

test_parse_line : parse_line "A to B = 3" ≡ just (link "A" "B" 3)
test_parse_line = refl

test_rank_a : rank_path 4 ("A" ∷ "B" ∷ "C" ∷ []) ((link "A" "B" 2) ∷ (link "C" "B" 3) ∷ []) ≡ just 5
test_rank_a = refl


test_unmaybe : unmaybe (map parse_line (lines  "A to B = 3\nC to B = 2")) ≡ (link "A" "B" 3) ∷ (link "C" "B" 2) ∷ []
test_unmaybe = refl

test_unique_cities : unique_cities ((link "A" "B" 3) ∷ (link "C" "B" 2) ∷ []) ≡ "C" ∷ "B" ∷ "A" ∷ []
test_unique_cities = refl
