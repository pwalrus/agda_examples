module d13.table where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; make-perms)
open import util.lookup using (LookupTree ; build-tree ; has-val ; set-val ; all-values) renaming (read-val to read-tree)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Int using (Int ; pos)
open import Data.Integer.Base using (_+_ ; _-_ ; _≤ᵇ_)
open import Data.Integer.Show renaming (show to showz)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_)
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
  link : String → String → Int → Link

val-of : Link → Int
val-of (link _ _ d) = d

show-link : Link → String
show-link (link lhs rhs d) = lhs ++ " to " ++ rhs ++ " = " ++ (showz d)

rem-dot : List Char → List Char
rem-dot [] = []
rem-dot (x ∷ xs) with (rem-dot xs)
rem-dot (x ∷ xs) | [] = x ∷ []
rem-dot (x ∷ xs) | ('.' ∷ []) = x ∷ []
rem-dot (x ∷ xs) | (y ∷ ys) = x ∷ y ∷ ys

rem-dot-s : String → String
rem-dot-s = fromList ∘ rem-dot ∘ toList

unique-insert-str : List String → String → List String
unique-insert-str [] l = l ∷ []
unique-insert-str (x ∷ xs) l = if ( x == l)
   then x ∷ xs
   else x ∷ (unique-insert-str xs l)

unique-nodes : List Link → List String
unique-nodes ((link lhs rhs _) ∷ xs) = unique-insert-str (unique-insert-str (unique-nodes xs) lhs) rhs
unique-nodes _ = []

is-match : String → String → Link → Bool
is-match x y (link lhs rhs _) = ((x == lhs) ∧ (y == rhs)) ∨ ((y == lhs) ∧ (x == rhs))

lookup-pair : String → String → List Link → Maybe Int
lookup-pair x y db with (filterᵇ (λ {q → is-match x y q}) db)
lookup-pair x y db | [] = nothing
lookup-pair x y db | links = just (foldr _+_ (pos 0)
  (map val-of links)
  )

rank-path-h : Nat → String → List String → List Link → Maybe Int
rank-path-h 0 _ _ _ = nothing
rank-path-h (suc l) first (x ∷ []) db = (lookup-pair x first db)
rank-path-h (suc l) first (x ∷ y ∷ xs) db with (lookup-pair x y db)
rank-path-h (suc l) first (x ∷ y ∷ xs) db | (just part) with rank-path-h l first (y ∷ xs) db
rank-path-h (suc l) first (x ∷ y ∷ xs) db | (just part) | (just rest) = just (part + rest)
rank-path-h (suc l) first (x ∷ y ∷ xs) db | (just part) | nothing = nothing
rank-path-h (suc l) first (x ∷ y ∷ xs) db | nothing = nothing
rank-path-h _ _ _ _ = just (pos 0)

rank-path : List String → List Link → Maybe Int
rank-path [] _ = nothing
rank-path (x ∷ y ∷ []) db = (lookup-pair x y db)
rank-path (x ∷ xs) db = rank-path-h (suc (length (x ∷ xs))) x (x ∷ xs) db

parse-dir : String → Nat → Int
parse-dir "lose" d = (pos 0) - pos d
parse-dir _ d = pos d

parse-line-w : List String →  Maybe Link
parse-line-w (lhs ∷ "would" ∷ dir ∷ d ∷ "happiness" ∷ "units" ∷ "by" ∷ "sitting" ∷ "next" ∷ "to" ∷ rhs ∷ _) with (readMaybe 10 d)
parse-line-w (lhs ∷ "would" ∷ dir ∷ d ∷ "happiness" ∷ "units" ∷ "by" ∷ "sitting" ∷ "next" ∷ "to" ∷ rhs ∷ _) | nothing = nothing
parse-line-w (lhs ∷ "would" ∷ dir ∷ d ∷ "happiness" ∷ "units" ∷ "by" ∷ "sitting" ∷ "next" ∷ "to" ∷ rhs ∷ _) | (just x) = just (link lhs (rem-dot-s rhs) (parse-dir dir x))
parse-line-w _ = nothing

parse-line : String → Maybe Link
parse-line x = parse-line-w ( words x)

show-path : List String → List Link → String
show-path nodes db with (rank-path nodes db)
show-path nodes db | just score = (foldr _++_ "" nodes) ++ " = " ++ (showz score)
show-path nodes db | nothing = (foldr _++_ "" nodes) ++ " is invalid"

add-me : List Link → List Link
add-me x = concat (x ∷ (map (λ {y → link "Me" y (pos 0)}) nodes) ∷ (map (λ {y → link y "Me" (pos 0)}) nodes) ∷ [])
  where
    nodes : List String
    nodes = unique-nodes x

maybe-show-path : Maybe (List String) → List Link → String
maybe-show-path nothing _ = "none found"
maybe-show-path (just p) db = show-path p db

min-by-func : {A : Set} → Nat → List A → (A → Maybe Int) → Maybe A
min-by-func 0 _ _ = nothing
min-by-func (suc l) [] f = nothing
min-by-func (suc l) (x ∷ []) f = just x
min-by-func (suc l) (x ∷ y ∷ xs) f with (f x)
min-by-func (suc l) (x ∷ y ∷ xs) f | (just xr) with (f y)
min-by-func (suc l) (x ∷ y ∷ xs) f | (just xr) | (just yr) = if (yr ≤ᵇ xr) then (min-by-func l (x ∷ xs) f) else (min-by-func l (y ∷ xs) f)
min-by-func (suc l) (x ∷ y ∷ xs) f | (just xr) | nothing = nothing
min-by-func (suc l) (x ∷ y ∷ xs) f | nothing = nothing

min-path : List (List String) → List Link -> Maybe (List String)
min-path x db = min-by-func (suc (length x)) x
  λ {b → (rank-path b db)}

total-hap : String → String
total-hap x = "\n" ++ maybe-show-path (min-path perms links) links ++ "\n"
  where
    links-unme : List Link
    links-unme = unmaybe (((map parse-line) ∘ lines) x)
    links : List Link
    links = add-me links-unme
    nodes : List String
    nodes = unique-nodes links
    perms : List (List String)
    perms = make-perms nodes
    mp : Maybe (List String)
    mp = min-path perms links

test-parse-line : parse-line "Alice would gain 54 happiness units by sitting next to Bob." ≡ just (link "Alice" "Bob" (pos 54))
test-parse-line = refl

--test-total-hap-b : total-hap ("Alice would gain 54 happiness units by sitting next to Bob.\n"
--  ++ "Alice would lose 79 happiness units by sitting next to Carol.\n"
--  ++ "Bob would gain 83 happiness units by sitting next to Alice.\n"
--  ++ "Bob would lose 7 happiness units by sitting next to Carol.\n"
--  ++ "Carol would lose 62 happiness units by sitting next to Alice.\n"
--  ++ "Carol would gain 60 happiness units by sitting next to Bob.") ≡ "\nCarolBobAlice = 49\n"
--test-total-hap-b = refl
