module d11.hex where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; list-minus ; conseq ; index-of ; set-at ; wordsByᵇ ; get-sub-wrap ; set-sub-wrap) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; build-str-tree ; LTPair ; counter ; quick-sort ; str-lt ; all-values ; all-keys ; all-kv ; has-val) renaming (set-val to set-tree ; read-val to read-tree)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree)
open import util.json using (readIntMaybe)
open import util.search using (search-rec-breadth-dedup ; branch-bound)
open import util.nat_stuff using (div-nat ; mod-nat ; max)
open import util.bitwise using (bitwise-xor)
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


data Direction : Set where
  N : Direction
  NE : Direction
  NW : Direction
  S : Direction
  SE : Direction
  SW : Direction

rev-dir : Direction → Direction
rev-dir N = S
rev-dir NW = SE
rev-dir NE = SW
rev-dir S = N
rev-dir SW = NE
rev-dir SE = NW

record Point : Set where
  constructor point
  field
    x : Int
    y : Int

_==z_ : Int → Int → Bool
_==z_ x y = isYes (x ≟ y)

_<z_ : Int → Int → Bool
_<z_ x y = isYes (x <?z y)

compass : Point → Point → Direction
compass (point x1 y1) (point x2 y2) with (x1 ==z x2)
compass (point x1 y1) (point x2 y2) | true with (y1 <z y2)
compass (point x1 y1) (point x2 y2) | true | true = N
compass (point x1 y1) (point x2 y2) | true | _ = S
compass (point x1 y1) (point x2 y2) | _  with (y1 <z y2)
compass (point x1 y1) (point x2 y2) | _ | true with (x1 <z x2)
compass (point x1 y1) (point x2 y2) | _ | true | true = NE
compass (point x1 y1) (point x2 y2) | _ | true | false = NW
compass (point x1 y1) (point x2 y2) | _ | false with (x1 <z x2)
compass (point x1 y1) (point x2 y2) | _ | false | true = SE
compass (point x1 y1) (point x2 y2) | _ | false | false = SW


parse-dir : String → Maybe Direction
parse-dir "n" = just N
parse-dir "ne" = just NE
parse-dir "nw" = just NW
parse-dir "s" = just S
parse-dir "se" = just SE
parse-dir "sw" = just SW
parse-dir _ = nothing

trim : String → String
trim = fromList ∘ trim-ch ∘ toList

lower : String → String
lower = fromList ∘ map primToLower ∘ toList

parse-path : String → List Direction
parse-path = unmaybe ∘ map parse-dir ∘ map lower ∘ map trim ∘ wordsByᵇ (λ {q → q ==c ','})

show-point : Point → String
show-point (point x y) = "(" ++ show-z x ++ ", " ++ show-z y ++ ")"

odd-col : Point → Bool
odd-col (point x _) = mod-nat ∣ x ∣ 2 ==n 1

sucz : Int → Int
sucz x = x +z pos 1

predz : Int → Int
predz x = x -z pos 1

move : Direction → Point → Point
move N (point x y) = point x (sucz y)
move NE (point x y) = point (sucz x) (if odd-col (point x y) then (sucz y) else y)
move NW (point x y) = point (predz x) (if odd-col (point x y) then (sucz y) else y)
move S (point x y) = point x (predz y)
move SE (point x y) = point (sucz x) (if odd-col (point x y) then y else (predz y))
move SW (point x y) = point (predz x) (if odd-col (point x y) then y else (predz y))

private
  dist-h : Nat → Nat → Point → Point → Nat
  dist-h 0 _ _ _ = 0
  dist-h (suc lm) accum (point x1 y1) (point x2 y2) with (x1 ==z x2)
  dist-h (suc lm) accum (point x1 y1) (point x2 y2) | true = accum + ∣ y2 -z y1 ∣
  dist-h (suc lm) accum (point x1 y1) (point x2 y2) | false with (compass (point x1 y1) (point x2 y2))
  dist-h (suc lm) accum (point x1 y1) (point x2 y2) | false | dir = dist-h lm (suc accum) (point x1 y1) (move (rev-dir dir) (point x2 y2))

dist : Point → Point → Nat
dist (point x1 y1) (point x2 y2) = dist-h (∣ x1 ∣ + ∣ y1 ∣ + ∣ x2 ∣ + ∣ y2 ∣) 0 (point x1 y1) (point x2 y2)

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

test-move-a : move NE center-point ≡ point (pos 1) (pos 0)
test-move-a = refl

test-move-b : (show-point ∘ move S ∘ move N) center-point ≡ "(0, 0)"
test-move-b = refl

test-move-c : (show-point ∘ move SE ∘ move NW) center-point ≡ "(0, 0)"
test-move-c = refl

test-move-d : (show-point ∘ move SW ∘ move NE) center-point ≡ "(0, 0)"
test-move-d = refl

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
