module d14.defrag where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; list-minus ; conseq ; index-of ; set-at ; wordsByᵇ ; get-sub-wrap ; set-sub-wrap ; is-in ; unique-insert) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; build-str-tree ; LTPair ; counter ; quick-sort ; str-lt ; all-values ; all-keys ; unique-list)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree ; has-val ; all-kv) renaming (set-val to set-tree ; read-val to read-tree)
open import util.json using (readIntMaybe)
open import util.search using (search-rec-breadth-dedup ; branch-bound ; components)
open import util.nat_stuff using (div-nat ; mod-nat ; max)
open import util.bitwise using (bitwise-xor ; to-bin ; show-bool)
open import util.grid using (Point ; point ; show-point ; neighbors-2d)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String using (toList ; fromList ; _++_ ; unlines ; intersperse ; fromChar ; padLeft)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred ; _⊔_)
open import Data.Nat.Show using (show ; readMaybe ; showInBase)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer using (∣_∣) renaming (_<?_ to _<?z_ ; _+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Show using () renaming (show to show-z)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; reverse ; head ; cartesianProductWith ; applyUpTo ; take ; drop ; any ; all)
open import Agda.Builtin.Char using (Char ; primCharToNat ; primToLower)
open import Data.Char.Properties using () renaming (_==_ to _==c_ ; _<?_ to _<c?_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function using (_∘_ ; id ; flip)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₂ ; uncurry)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


open import d10.knot using (KnotState ; add-lengths ; init-knot ; iter-func ; trim ; all-steps ; hash-16)


hash-all-h : Nat → List Nat → List Nat → List Nat
hash-all-h 0 _ _ = []
hash-all-h (suc lm) ys [] = reverse ys
hash-all-h (suc lm) ys xs = hash-all-h lm (((hash-16 ∘ take 16) xs) ∷ ys) (drop 16 xs)

hash-all : List Nat → List Nat
hash-all xs = hash-all-h (length xs) [] xs

hash-to-hex : String → List Nat
hash-to-hex x = hsh
  where
    seq : List Nat
    seq = (add-lengths ∘ map primCharToNat ∘ toList ∘ trim) x
    fst-round : KnotState Nat
    fst-round = all-steps seq init-knot
    last-round : KnotState Nat
    last-round = iter-func 63 (all-steps seq) fst-round
    hsh : List Nat
    hsh = hash-all (KnotState.chlst last-round)

to-bits-array : List Nat → List Bool
to-bits-array = concat ∘ map (reverse) ∘ map (take 8) ∘ map to-bin

make-grid : String → List (List Bool)
make-grid xs = (map to-bits-array ∘ map hash-to-hex ∘ applyUpTo (λ {q → (xs ++ "-" ++ show q)})) 128

count-used-in-grid : String → String
count-used-in-grid xs = "used: " ++  (show ∘ foldr _+_ 0 ∘ map (λ {true → 1 ; _ → 0}) ∘ concat ∘ make-grid ∘ trim) xs ++ "\n"

mangle-offs : Nat
mangle-offs = 100000

mangle-id : Point → Nat
mangle-id (point x y) = 10 * mangle-offs * ∣ pos mangle-offs +z x ∣ + ∣ pos mangle-offs +z y ∣

grid-to-points : List (List Bool) → List Point
grid-to-points xs = map (uncurry point) flattened
  where
    nested : List (Nat × List (Nat × Bool))
    nested = (map (map₂ (filterᵇ proj₂)) ∘ enumerate ∘ map enumerate) xs
    flattened : List (Int × Int)
    flattened = concat (map (λ {(a , lst) → map (λ {(b , _) → pos a , pos b}) lst}) nested)

find-connected : List Point → List (List Point)
find-connected xs = components show-point neighbors-2d-flt xs
  where
    db : LookupNatTree Bool
    db = build-nat-tree (map (λ {q → mangle-id q , true}) xs)
    neighbors-2d-flt : Point → List Point
    neighbors-2d-flt = filterᵇ (λ {q → has-val (mangle-id q) db}) ∘ neighbors-2d

find-frag-components : String → String
find-frag-components x = (unlines ∘ map (intersperse ",") ∘ map (map show-point)) comps ++ "\ntotal: " ++ show (length comps) ++ "\n"
  where
    grid : List (List Bool)
    grid = (make-grid ∘ trim) x
    comps : List (List Point)
    comps = (find-connected ∘ grid-to-points) grid

test-bits-array : (intersperse "" ∘ map show-bool ∘ to-bits-array ∘ unmaybe ∘ map (readMaybe 16))  ("a0" ∷ "c2" ∷ "01" ∷ []) ≡ "101000001100001000000001"
test-bits-array = refl

-- its slow
--test-count-used-in-grid : count-used-in-grid "flqrgnkx" ≡ "used: 8108\n"
--test-count-used-in-grid = refl

test-grid-to-points : (unlines ∘ map show-point ∘ grid-to-points) ((true ∷ false ∷ []) ∷ (false ∷ true ∷ []) ∷ []) ≡ "(0, 0)\n(1, 1)"
test-grid-to-points = refl

