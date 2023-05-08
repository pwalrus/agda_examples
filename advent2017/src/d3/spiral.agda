module d3.spiral where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; list-minus ; conseq) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; LookupNatTree ; build-str-tree ; build-nat-tree ; has-val ; all-values ; all-keys ; all-kv ; LTPair) renaming (set-val to set-tree ; read-val to read-tree)
open import util.json using (readIntMaybe)
open import util.search using (search-rec-breadth-dedup ; branch-bound)
open import util.nat_stuff using (div-nat ; mod-nat)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse ; fromChar)
open import Data.String.Properties using (_==_ ; _<?_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using (∣_∣) renaming (_+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Show using () renaming (show to show-z)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; reverse ; head ; cartesianProductWith ; applyUpTo ; take ; drop)
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties using () renaming (_==_ to _==c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function using (_∘_ ; id)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


trim : String → String
trim = fromList ∘ trim-ch ∘ toList

largest-perfect-square-h : Nat → Nat → Nat → Nat
largest-perfect-square-h 0 _ _ = 0
largest-perfect-square-h (suc lm) idx target with (target < suc (suc idx * suc idx))
largest-perfect-square-h (suc lm) idx target | true = idx
largest-perfect-square-h (suc lm) idx target | false = largest-perfect-square-h lm (suc idx) target

largest-odd-perfect-square : Nat → Nat
largest-odd-perfect-square x = if (mod-nat largst 2 ==n 0) then pred largst else largst
  where
    largst : Nat
    largst = largest-perfect-square-h x 0 x

id-to-coord : Nat → (Int × Int)
id-to-coord x = if (x < 2) then (pos 0 , pos 0) else output
  where
    innersq : Nat
    innersq = largest-odd-perfect-square x
    outer-edge : Nat
    outer-edge = suc innersq
    perim-steps : Nat
    perim-steps = x - (innersq * innersq)
    output : Int × Int
    output with (perim-steps < suc outer-edge)
    output | true = (pos (suc (div-nat innersq 2)) , pos perim-steps -z pos (suc (div-nat innersq 2)))
    output | false with (perim-steps < suc (2 * outer-edge))
    output | false | true = (pos outer-edge -z pos perim-steps +z pos (suc (div-nat innersq 2)) , pos (suc (div-nat innersq 2)) )
    output | false | false with (perim-steps < suc (3 * outer-edge))
    output | false | false | true = (negsuc (div-nat innersq 2) , pos (suc (div-nat innersq 2)) -z pos perim-steps +z pos (2 * outer-edge))
    output | false | false | false = (pos perim-steps -z pos (3 * outer-edge) -z pos (suc (div-nat innersq 2)) , negsuc (div-nat innersq 2))

manhat-dist : (Int × Int) → (Int × Int) → Nat
manhat-dist (x1 , y1) (x2 , y2) = ∣ x1 -z x2 ∣ + ∣ y1 -z y2 ∣

dist-to-center : String → String
dist-to-center x = output
  where
    inp : Maybe Nat
    inp = (readMaybe 10 ∘ trim) x
    output : String
    output with inp
    output | (just n) = "dist: " ++ show (manhat-dist (pos 0 , pos 0) (id-to-coord n)) ++ "\n"
    output | nothing = "bad input\n"


neigh : (Int × Int) → List (Int × Int)
neigh (x , y) =
  (x +z pos 1 , y +z pos 1)
  ∷ (x +z pos 1 , y)
  ∷ (x +z pos 1 , y -z pos 1)
  ∷ (x -z pos 1 , y +z pos 1)
  ∷ (x -z pos 1 , y)
  ∷ (x -z pos 1 , y -z pos 1)
  ∷ (x , y +z pos 1)
  ∷ (x , y -z pos 1)
  ∷ []


mangle-offs : Nat
mangle-offs = 100000

mangle-id : (Int × Int) → Nat
mangle-id (x , y) = 10 * mangle-offs * ∣ pos mangle-offs +z x ∣ + ∣ pos mangle-offs +z y ∣

accumulate-sums : Nat → Nat → Nat → LookupNatTree Nat → LookupNatTree Nat
accumulate-sums 0 _ _ db = db
accumulate-sums (suc lm) idx target db = if (totaln < target) then (accumulate-sums lm (suc idx) target updated-tree) else updated-tree
  where
    coord : Int × Int
    coord = id-to-coord idx
    neighbors : List Nat
    neighbors = (unmaybe ∘ map (λ {q → read-tree q db }) ∘ map mangle-id ∘ neigh) coord
    totaln : Nat
    totaln = foldr _+_ 0 neighbors
    updated-tree : LookupNatTree Nat
    updated-tree = set-tree (mangle-id coord) totaln db


show-db : LookupNatTree Nat → String
show-db = unlines ∘ map (λ {(a , b) → show a ++ ": " ++ show b}) ∘ all-kv 

accumulate-to-goal : String → String
accumulate-to-goal x = output
  where
    inp : Maybe Nat
    inp = (readMaybe 10 ∘ trim) x
    init-tree : LookupNatTree Nat
    init-tree = build-nat-tree ((mangle-id (pos 0 , pos 0) , 1) ∷ (mangle-id (pos 1 , pos 0) , 1) ∷ [])
    output : String
    output with inp
    output | (just n) = "" ++ show-db (accumulate-sums 1000000 2 n init-tree) ++ "\n"
    output | nothing = "bad input\n"


test-lar-perf : largest-odd-perfect-square 27 ≡ 5
test-lar-perf = refl

test-lar-perf-b : largest-odd-perfect-square 9 ≡ 1
test-lar-perf-b = refl

test-lar-perf-c : largest-odd-perfect-square 1 ≡ 0
test-lar-perf-c = refl

test-id-to-coord-a : id-to-coord 2 ≡ (pos 1 , pos 0)
test-id-to-coord-a = refl

test-id-to-coord-b : id-to-coord 12 ≡ (pos 2 , pos 1)
test-id-to-coord-b = refl

test-id-to-coord-c : id-to-coord 14 ≡ (pos 1 , pos 2)
test-id-to-coord-c = refl

test-id-to-coord-d : id-to-coord 5 ≡ (negsuc 0 , pos 1)
test-id-to-coord-d = refl

test-id-to-coord-e : id-to-coord 18 ≡ (negsuc 1 , pos 1)
test-id-to-coord-e = refl

test-id-to-coord-f : id-to-coord 7 ≡ (negsuc 0 , negsuc 0)
test-id-to-coord-f = refl

test-id-to-coord-g : id-to-coord 22 ≡ (negsuc 0 , negsuc 1)
test-id-to-coord-g = refl

test-id-to-coord-h : id-to-coord 9 ≡ (pos 1 , negsuc 0)
test-id-to-coord-h = refl

test-id-to-coord-i : id-to-coord 1 ≡ (pos 0 , pos 0)
test-id-to-coord-i = refl

test-dist-to-center-a : dist-to-center "1" ≡ "dist: 0\n"
test-dist-to-center-a = refl

test-dist-to-center-b : dist-to-center "12" ≡ "dist: 3\n"
test-dist-to-center-b = refl

test-dist-to-center-c : dist-to-center "23" ≡ "dist: 2\n"
test-dist-to-center-c = refl

test-dist-to-center-d : dist-to-center "1024" ≡ "dist: 31\n"
test-dist-to-center-d = refl

test-mangle-id : mangle-id (pos 3 , negsuc 2) ≡ 100003099997
test-mangle-id = refl

test-accumulate-to-goal : accumulate-to-goal "55" ≡
  "100002100001: 57\n" ++
  "100002100000: 54\n" ++
  "100002099999: 26\n" ++
  "100001100001: 2\n" ++
  "100001100000: 1\n" ++
  "100001099999: 25\n" ++
  "100000100001: 4\n" ++
  "100000100000: 1\n" ++
  "100000099999: 23\n" ++
  "99999100001: 5\n" ++
  "99999100000: 10\n" ++
  "99999099999: 11\n"
test-accumulate-to-goal = refl
