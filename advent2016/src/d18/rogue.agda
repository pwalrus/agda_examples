
module d18.rogue where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; each-one ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; split ; empty-table ; show-table ; transpose ; eq-classes ; rem-match ; partitionᵇ ; deduplicateᵇ ; index-of) renaming (trim to trim-ch)
open import util.lookup using (str-lt ; quick-sort ; LookupStrTree) renaming (all-kv to all-str-kv)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree ; has-val ; all-kv) renaming (set-val to set-tree ; read-val to read-tree ; rem-val to rem-tree)
open import util.json using (readIntMaybe ; rem-lst-c)
open import util.search using (search-rec-breadth ; search-rec-all)
open import util.hash using (hash-md5)
open import util.nat_stuff using (mod-nat ; div-nat ; lin-mod-system)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; unwords ; intersperse ; fromChar ; padRight)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe ; showInBase)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using (_≤ᵇ_) renaming (_+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Properties using (_≟_)
open import Data.Integer.Show using () renaming (show to showz)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; take ; drop ; head ; last; tail ; any ; all ; cartesianProductWith ; applyUpTo ; scanr ; reverse)
open import Agda.Builtin.Char using (Char ; primCharToNat ; primNatToChar)
open import Data.Char.Properties renaming (_==_ to _==c_ ; _<?_ to _<c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function.Base using (_∘_ ; id ; const)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


is-trap : Bool → Bool → Bool → Bool
is-trap true true false = true
is-trap false true true = true
is-trap true false false = true
is-trap false false true = true
is-trap _ _ _ = false

private
  mk-new-row-h : List Bool → List Bool
  mk-new-row-h [] = []
  mk-new-row-h (x ∷ []) = []
  mk-new-row-h (x ∷ y ∷ []) = (is-trap x y false) ∷ []
  mk-new-row-h (x ∷ y ∷ z ∷ xs) = (is-trap x y z) ∷ mk-new-row-h (y ∷ z ∷ xs)

mk-new-row : List Bool → List Bool
mk-new-row xs = mk-new-row-h (false ∷ xs)

mk-n-rows : Nat → List Bool → List (List Bool)
mk-n-rows 0 l = []
mk-n-rows 1 l = l ∷ []
mk-n-rows (suc n) l with (mk-n-rows n l)
mk-n-rows (suc n) l | [] = l ∷ []
mk-n-rows (suc n) l | (y ∷ ys) = (mk-new-row y) ∷ y ∷ ys

count-safe : List (List Bool) → Nat
count-safe = foldr _+_ 0 ∘ concat ∘ map (map (λ {q → if not q then 1 else 0}))

show-line : List Bool → String
show-line = fromList ∘ map (λ {q → if q then '^' else '.'})

show-lines : List (List Bool) → String
show-lines = unlines ∘ map show-line

parse-line : String → List Bool
parse-line = map (λ {q → if q ==c '^' then true else false}) ∘ toList

show-safe-tile-count : String → String
show-safe-tile-count x = "safe: " ++ (show ∘ count-safe ∘ mk-n-rows target ∘ parse-line) init ++ "\n"
  where
    init : String
    init = (fromMaybe "" ∘ head ∘ words) x
    target : Nat
    target = (fromMaybe 0 ∘ readMaybe 10 ∘ fromMaybe "" ∘ head ∘ drop 1 ∘ words) x


test-mk-new-row-a : (show-line ∘ mk-new-row ∘ parse-line) "..^^." ≡ ".^^^^"
test-mk-new-row-a = refl

test-mk-new-row-b : (show-line ∘ mk-new-row ∘ parse-line) ".^^^^" ≡ "^^..^"
test-mk-new-row-b = refl

test-mk-n-row-a : (show-lines ∘ reverse ∘ mk-n-rows 10 ∘ parse-line) ".^^.^.^^^^" ≡ ".^^.^.^^^^\n" ++
  "^^^...^..^\n" ++
  "^.^^.^.^^.\n" ++
  "..^^...^^^\n" ++
  ".^^^^.^^.^\n" ++
  "^^..^.^^..\n" ++
  "^^^^..^^^.\n" ++
  "^..^^^^.^^\n" ++
  ".^^^..^.^^\n" ++
  "^^.^^^..^^"
test-mk-n-row-a = refl

test-count-safe-a : (count-safe ∘ mk-n-rows 10 ∘ parse-line) ".^^.^.^^^^" ≡ 38
test-count-safe-a = refl

