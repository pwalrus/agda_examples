module d11.hex where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; list-minus ; conseq ; index-of ; set-at ; wordsByᵇ ; get-sub-wrap ; set-sub-wrap) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; build-str-tree ; LTPair ; counter ; quick-sort ; str-lt ; all-values ; all-keys ; all-kv ; has-val) renaming (set-val to set-tree ; read-val to read-tree)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree)
open import util.json using (readIntMaybe)
open import util.search using (search-rec-breadth-dedup ; branch-bound)
open import util.nat_stuff using (div-nat ; mod-nat ; max)
open import util.bitwise using (bitwise-xor)
open import util.grid using (Point ; point ; show-point) renaming (HexDirection to Direction ; rev-dir-hex to rev-dir ; compass-hex to compass ; move-hex to move ; parse-dir-hex to parse-dir ; dist-hex to dist)
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

_==z_ : Int → Int → Bool
_==z_ x y = isYes (x ≟ y)

_<z_ : Int → Int → Bool
_<z_ x y = isYes (x <?z y)

trim : String → String
trim = fromList ∘ trim-ch ∘ toList

lower : String → String
lower = fromList ∘ map primToLower ∘ toList

parse-path : String → List Direction
parse-path = unmaybe ∘ map parse-dir ∘ map lower ∘ map trim ∘ wordsByᵇ (λ {q → q ==c ','})

center-point : Point
center-point = point (pos 0) (pos 0)

apply-moves : Nat → List Direction → Point → (Nat × Point)
apply-moves mx [] p = (mx , p)
apply-moves mx (x ∷ xs) p = apply-moves new-mx xs new-p
  where
    new-p : Point
    new-p = move x p
    new-mx : Nat
    new-mx = max mx (dist center-point new-p)

point-from-path : String → String
point-from-path x = show-point final-p ++ ", dist: " ++ show (dist center-point final-p) ++ ", max-dist: " ++ (show ∘ proj₁) final-pair ++ "\n"
  where
    path : List Direction
    path = parse-path (trim x)
    final-pair : Nat × Point
    final-pair = apply-moves 0 path center-point
    final-p : Point
    final-p = proj₂ final-pair

test-apply-moves-a : (show-point ∘ proj₂ ∘ apply-moves 0 (parse-path "N,N,NE")) center-point ≡ "(1, 2)"
test-apply-moves-a = refl

test-dist-a : (dist center-point ∘ proj₂ ∘ apply-moves 0 (parse-path "N,N,NE")) center-point ≡ 3
test-dist-a = refl

test-dist-b : (dist center-point ∘ proj₂ ∘ apply-moves 0 (parse-path "NE,NE,SW,SW")) center-point ≡ 0
test-dist-b = refl

test-dist-c : (dist center-point ∘ proj₂ ∘ apply-moves 0 (parse-path "NE,NE,S,S")) center-point ≡ 2
test-dist-c = refl

test-apply-moves-b : (show-point ∘ proj₂ ∘  apply-moves 0 (parse-path "se,sw,se,sw,sw")) center-point ≡ "(-1, -3)"
test-apply-moves-b = refl

test-dist-d : (dist center-point ∘ proj₂ ∘ apply-moves 0 (parse-path "SE,SW,SE,SW,SW")) center-point ≡ 3
test-dist-d = refl
