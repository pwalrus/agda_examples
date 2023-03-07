
module d21.rpg where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct) renaming (trim to trim-ch)
open import util.lookup using (LookupNatTree ; build-nat-tree ; has-val ; all-values ; all-keys ; all-kv ; LTPair) renaming (set-val to set-tree ; read-val to read-tree)
open import util.json using (readIntMaybe)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using (_==_ ; _<?_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Properties using (_≟_)
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

data ItemType : Set where
  weapon : ItemType
  armor : ItemType
  ring : ItemType

data Item : Set where
  item : ItemType → String → Nat → Nat → Nat → Item
  noitem : Item

showi : Item → String
showi noitem = "noitem"
showi (item _ name cost dam arm) = name

data Outfit : Set where
  outfit : Item → Item → Item → Item → Outfit

showo : Outfit → String
showo (outfit i1 i2 i3 i4) = showi i1 ++ "," ++ showi i2 ++ "," ++ showi i3 ++ "," ++ showi i4

data StatBundle : Set where
  statb : Nat → Nat → StatBundle

iname : Item → String
iname (item _ name _ _ _) = name
iname noitem = ""

idam : Item → Nat
idam (item _ _ cost dam arm) = dam
idam noitem = 0

icost : Item → Nat
icost (item _ _ cost dam arm) = cost
icost noitem = 0

iarm : Item → Nat
iarm (item _ _ cost dam arm) = arm
iarm noitem = 0

oitems : Outfit → List Item
oitems (outfit weap arm r1 r2) = weap ∷ arm ∷ r1 ∷ r2 ∷ []

odam : Outfit → Nat
odam = foldr _+_ 0 ∘ map idam ∘ oitems

ocost : Outfit → Nat
ocost = foldr _+_ 0 ∘ map icost ∘ oitems

oarm : Outfit → Nat
oarm = foldr _+_ 0 ∘ map iarm ∘ oitems

oeval : Outfit → StatBundle
oeval o = statb (odam o) (oarm o)

parse-three-int : String → String → String → Maybe (Nat × Nat × Nat)
parse-three-int x y z with (readMaybe 10 x)
parse-three-int x y z | (just rx) with (readMaybe 10 y)
parse-three-int x y z | (just rx) | (just ry) with (readMaybe 10 z)
parse-three-int x y z | (just rx) | (just ry) | (just rz) = just (rx , ry , rz)
parse-three-int x y z | (just rx) | (just ry) | nothing = nothing
parse-three-int x y z | (just rx) | nothing = nothing
parse-three-int x y z | nothing = nothing

parse-line-w : ItemType → List String → Maybe Item
parse-line-w itype (name ∷ a ∷ b ∷ c ∷ _) with (parse-three-int a b c)
parse-line-w itype (name ∷ a ∷ b ∷ c ∷ _) | nothing = nothing
parse-line-w itype (name ∷ a ∷ b ∷ c ∷ _) | just (cost , dam , arm ) = just(item itype name cost dam arm)
parse-line-w _ _ = nothing

parse-line : ItemType → String → Maybe Item
parse-line itype x = parse-line-w itype (words x)

std-weapons : List Item
std-weapons = (unmaybe ∘ (map (parse-line weapon)) ∘ lines)
  ("Dagger        8     4       0\n" ++
  "Shortsword   10     5       0\n" ++
  "Warhammer    25     6       0\n" ++
  "Longsword    40     7       0\n" ++
  "Greataxe     74     8       0")

std-armor : List Item
std-armor = noitem ∷ (unmaybe ∘ (map (parse-line armor)) ∘ lines)
  ("Leather      13     0       1\n" ++
  "Chainmail    31     0       2\n" ++
  "Splintmail   53     0       3\n" ++
  "Bandedmail   75     0       4\n" ++
  "Platemail   102     0       5")

std-ring : List Item
std-ring = noitem ∷ (unmaybe ∘ (map (parse-line ring)) ∘ lines)
  ("Damage+1    25     1       0\n" ++
  "Damage+2    50     2       0\n" ++
  "Damage+3   100     3       0\n" ++
  "Defense+1   20     0       1\n" ++
  "Defense+2   40     0       2\n" ++
  "Defense+3   80     0       3")

valid-outfit : Outfit → Bool
valid-outfit (outfit weap arm noitem _) = true
valid-outfit (outfit weap arm _ noitem) = true
valid-outfit (outfit weap arm r1 r2) with (iname r1 == iname r2)
valid-outfit (outfit weap arm r1 r2) | true = false
valid-outfit (outfit weap arm r1 r2) | false = true

inst-outfit : (((Item × Item) × Item) × Item) → Outfit
inst-outfit (((a , b) , c) , d) = outfit a b c d

all-outfits : List Outfit
all-outfits = filterᵇ valid-outfit outfits
  where
    combs : List (((Item × Item) × Item) × Item)
    combs = cartproduct (cartproduct (cartproduct std-weapons std-armor) std-ring) std-ring
    outfits : List Outfit
    outfits = map inst-outfit combs

max-hp : Nat
max-hp = 100

boss-hp : Nat
boss-hp = 104

boss-bundle : StatBundle
boss-bundle = statb 8 1

eval-outfit-h : StatBundle → StatBundle → Nat → Nat → Nat → (Nat × Nat)
eval-outfit-h _ _ 0 _ _ = (0 , 0)
eval-outfit-h (statb p-dam p-arm) (statb b-dam b-arm) (suc l) p-hp b-hp with (b-hp + b-arm - p-dam)
eval-outfit-h (statb p-dam p-arm) (statb b-dam b-arm) (suc l) p-hp b-hp | 0 = (p-hp , 0)
eval-outfit-h (statb p-dam p-arm) (statb b-dam b-arm) (suc l) p-hp b-hp | new-b-hp with (p-hp + p-arm - b-dam)
eval-outfit-h (statb p-dam p-arm) (statb b-dam b-arm) (suc l) p-hp b-hp | new-b-hp | 0 = (0 , new-b-hp)
eval-outfit-h (statb p-dam p-arm) (statb b-dam b-arm) (suc l) p-hp b-hp | new-b-hp | new-p-hp = eval-outfit-h  (statb p-dam p-arm) (statb b-dam b-arm) l new-p-hp new-b-hp

eval-outfit : StatBundle → (Nat × Nat)
eval-outfit p-bundle = eval-outfit-h p-bundle boss-bundle (max-hp + boss-hp) max-hp boss-hp

win-fight : StatBundle → Bool
win-fight p-bundle with (eval-outfit p-bundle)
win-fight p-bundle | (_ , 0) = true
win-fight p-bundle | _ = false

omin : (Nat × Outfit) → (Nat × Outfit) → (Nat × Outfit)
omin x y = if proj₁ x < (proj₁ y) then x else y

omax : (Nat × Outfit) → (Nat × Outfit) → (Nat × Outfit)
omax x y = if proj₁ x < (proj₁ y) then y else x

cheapest-winner : String → String
cheapest-winner x = "\ncost: " ++ (show ∘ proj₁) best-outfit ++ " <-- " ++ (showo ∘ proj₂) best-outfit  ++ "\n"
  where
    winning-outfits : List Outfit
    winning-outfits = filterᵇ (win-fight ∘ oeval) all-outfits
    costs : List (Nat × Outfit)
    costs = map (λ {q → ocost q , q}) winning-outfits
    best-outfit : Nat × Outfit
    best-outfit = foldr omin (10000 , (outfit noitem noitem noitem noitem)) costs

expensive-loser : String → String
expensive-loser x = "\ncost: " ++ (show ∘ proj₁) best-outfit ++ " <-- " ++ (showo ∘ proj₂) best-outfit  ++ "\n"
  where
    winning-outfits : List Outfit
    winning-outfits = filterᵇ (not ∘ win-fight ∘ oeval) all-outfits
    costs : List (Nat × Outfit)
    costs = map (λ {q → ocost q , q}) winning-outfits
    best-outfit : Nat × Outfit
    best-outfit = foldr omax (0 , (outfit noitem noitem noitem noitem)) costs

test-eval-outfit-h : eval-outfit-h (statb 5 5) (statb 7 2) 100 8 12 ≡ (2 , 0)
test-eval-outfit-h = refl

test-eval-outfit-h-a : eval-outfit-h (statb 4 0) (statb 8 1) 100 100 104 ≡ (0 , 65)
test-eval-outfit-h-a = refl

test-oeval : oeval (outfit (item weapon "Dagger" 8 4 0) noitem noitem noitem) ≡ statb 4 0
test-oeval = refl

test-win-fight : win-fight (statb 4 0) ≡ false
test-win-fight = refl

test-cheapest-winner : cheapest-winner "" ≡ "\ncost: 78 <-- Longsword,Leather,Damage+1,noitem\n"
test-cheapest-winner = refl

test-expensive-loser : expensive-loser "" ≡ "\ncost: 148 <-- Dagger,noitem,Damage+3,Defense+2\n"
test-expensive-loser = refl
