
module d1.taxi where

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


abs-d : Int → Int → Int
abs-d x y = if (x ≤ᵇ y) then (y -z x) else (x -z y)

manhattan : (Int × Int) → (Int × Int) → Int
manhattan (x , y) (a , b) = (abs-d x a) +z (abs-d y b)

data Dir : Set where
  north : Dir
  west : Dir
  east : Dir
  south : Dir

data Move : Set where
  move : String → Nat → Move

data Pos : Set where
  point : Dir → (Int × Int) → Pos

manhattan-p : Pos → Pos → Int
manhattan-p (point _ p1) (point _ p2) = manhattan p1 p2

show-move : Move → String
show-move (move t d) = t ++ show d

show-pos : Pos → String
show-pos (point _ (x , y) ) = showz x ++ "," ++ showz y

drop-first : String → String
drop-first inp = output
  where
    inp-ch : List Char
    inp-ch = toList inp
    output : String
    output with inp-ch
    output | [] = ""
    output | (x ∷ xs) = fromList xs

get-first : String → String
get-first inp = output
  where
    inp-ch : List Char
    inp-ch = toList inp
    output : String
    output with inp-ch
    output | [] = ""
    output | (x ∷ xs) = fromList (x ∷ [])

rem-comma : String → String
rem-comma = fromList ∘ (rem-lst-c ',') ∘ trim-ch ∘ toList 

trim : String → String
trim = fromList ∘ trim-ch ∘ toList

parse-line : String → Maybe Move
parse-line inp with (readMaybe 10 (drop-first inp))
parse-line inp | nothing = nothing
parse-line inp | (just x) = just (move (get-first inp) x)

parse-seq : String → List Move
parse-seq = unmaybe ∘ (map parse-line) ∘ (map trim) ∘ (split ',')

apply-dir-change : Move → Dir → Dir
apply-dir-change (move "L" _) north = west
apply-dir-change (move "L" _) west = south
apply-dir-change (move "L" _) south = east
apply-dir-change (move "L" _) east = north
apply-dir-change (move "R" _) north = east
apply-dir-change (move "R" _) east = south
apply-dir-change (move "R" _) south = west
apply-dir-change (move "R" _) west = north
apply-dir-change _ d = d

apply-move : Pos → Move → Pos
apply-move (point dir1 (x , y)) (move t d) with (apply-dir-change (move t d) dir1)
apply-move (point dir1 (x , y)) (move t d) | north = (point north (x , y +z (pos d)))
apply-move (point dir1 (x , y)) (move t d) | west = (point west (x -z (pos d) , y))
apply-move (point dir1 (x , y)) (move t d) | south = (point south (x , y -z (pos d)))
apply-move (point dir1 (x , y)) (move t d) | east = (point east (x +z (pos d) , y))

apply-seq : Pos → List Move → Pos
apply-seq p1 [] = p1
apply-seq p1 (x ∷ xs) = apply-seq (apply-move p1 x) xs

track-seq : Pos → LookupStrTree Bool → List Move → Maybe Pos
track-seq p1 db [] = nothing
track-seq p1 db (x ∷ xs) = next
  where
    p2 : Pos
    p2 = apply-move p1 x
    next : Maybe Pos
    next with (read-tree (show-pos p2) db)
    next | (just _) = just p2
    next | nothing = track-seq p2 (set-tree (show-pos p2) true db) xs

init-pos : Pos
init-pos = point north (pos 0 , pos 0)

make-steps-h : Nat → Move → List Move
make-steps-h 0 _ = []
make-steps-h _ (move _ 0) = []
make-steps-h (suc l) (move "L" (suc d)) = (move "L" 1) ∷ (make-steps-h l (move "C" d))
make-steps-h (suc l) (move "R" (suc d)) = (move "R" 1) ∷ (make-steps-h l (move "C" d))
make-steps-h (suc l) (move t (suc d)) = (move t 1) ∷ (make-steps-h l (move t d))

make-steps : Move → List Move
make-steps (move t d) = make-steps-h (suc d) (move t d)

breakdown-moves : List Move → List Move
breakdown-moves = concat ∘ (map make-steps)

calc-taxi-dist : String → String
calc-taxi-dist x = "dist: " ++ showz (manhattan-p final-pos init-pos) ++ " at " ++ show-pos final-pos ++ "\n"
  where
    final-pos : Pos
    final-pos = apply-seq init-pos (breakdown-moves (parse-seq x))

calc-taxi-twice : String → String
calc-taxi-twice x = output ++ "\n"
  where
    final-pos : Maybe Pos
    final-pos = track-seq init-pos (build-str-tree (("" , false) ∷ [])) (breakdown-moves (parse-seq x))
    output : String
    output with final-pos
    output | nothing = "no duplicate found"
    output | (just p1) = "dist: " ++ showz (manhattan-p p1 init-pos) ++ " at " ++ show-pos p1

test-parse-seq : ((intersperse ", ") ∘ (map show-move) ∘ parse-seq) "L12, R32, L5" ≡ "L12, R32, L5"
test-parse-seq = refl

test-move-seq :  apply-seq init-pos (parse-seq "L12, R32, L5") ≡ point west (negsuc 16 , pos 32)
test-move-seq = refl

test-calc-taxi-dist-a : calc-taxi-dist "R2, L3\n" ≡ "dist: 5 at 2,3\n"
test-calc-taxi-dist-a = refl

test-calc-taxi-dist-b : calc-taxi-dist "R2, R2, R2" ≡ "dist: 2 at 0,-2\n"
test-calc-taxi-dist-b = refl

test-calc-taxi-dist-c : calc-taxi-dist "R5, L5, R5, R3" ≡ "dist: 12 at 10,2\n"
test-calc-taxi-dist-c = refl

test-calc-taxi-twice : calc-taxi-twice "R8, R4, R4, R8" ≡ "dist: 4 at 4,0\n"
test-calc-taxi-twice = refl
