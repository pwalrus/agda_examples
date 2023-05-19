module util.grid where

open import util.nat_stuff using (mod-nat)
open import Agda.Builtin.List using (List ; _∷_ ; [])
open import Data.List using (map)
open import Agda.Builtin.Nat using (Nat ; suc) renaming (_==_ to _==n_ ; _+_ to _+n_)
open import Agda.Builtin.Int using (Int ; pos)
open import Data.Integer using (_≟_ ; _<?_ ; _+_ ; _-_ ; ∣_∣)
open import Data.Integer.Show using () renaming (show to show-z)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable using (isYes)
open import Agda.Builtin.String using (String)
open import Data.String using (_++_ ; intersperse)
open import Agda.Builtin.Maybe using (Maybe ; just ; nothing)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Function using (_∘_ ; flip)


_==z_ : Int → Int → Bool
_==z_ x y = isYes (x ≟ y)

_<z_ : Int → Int → Bool
_<z_ x y = isYes (x <? y)


data HexDirection : Set where
  N : HexDirection
  NE : HexDirection
  NW : HexDirection
  S : HexDirection
  SE : HexDirection
  SW : HexDirection

all-dir-hex : List HexDirection
all-dir-hex = N ∷ NE ∷ NW ∷ S ∷ SE ∷ SW ∷ []

parse-dir-hex : String → Maybe HexDirection
parse-dir-hex "n" = just N
parse-dir-hex "ne" = just NE
parse-dir-hex "nw" = just NW
parse-dir-hex "s" = just S
parse-dir-hex "se" = just SE
parse-dir-hex "sw" = just SW
parse-dir-hex _ = nothing

rev-dir-hex : HexDirection → HexDirection
rev-dir-hex N = S
rev-dir-hex NW = SE
rev-dir-hex NE = SW
rev-dir-hex S = N
rev-dir-hex SW = NE
rev-dir-hex SE = NW

record Point : Set where
  constructor point
  field
    x : Int
    y : Int

show-point : Point → String
show-point (point x y) = "(" ++ show-z x ++ ", " ++ show-z y ++ ")"

compass-hex : Point → Point → HexDirection
compass-hex (point x1 y1) (point x2 y2) with (x1 ==z x2)
compass-hex (point x1 y1) (point x2 y2) | true with (y1 <z y2)
compass-hex (point x1 y1) (point x2 y2) | true | true = N
compass-hex (point x1 y1) (point x2 y2) | true | _ = S
compass-hex (point x1 y1) (point x2 y2) | _  with (y1 <z y2)
compass-hex (point x1 y1) (point x2 y2) | _ | true with (x1 <z x2)
compass-hex (point x1 y1) (point x2 y2) | _ | true | true = NE
compass-hex (point x1 y1) (point x2 y2) | _ | true | false = NW
compass-hex (point x1 y1) (point x2 y2) | _ | false with (x1 <z x2)
compass-hex (point x1 y1) (point x2 y2) | _ | false | true = SE
compass-hex (point x1 y1) (point x2 y2) | _ | false | false = SW

sucz : Int → Int
sucz x = x + pos 1

predz : Int → Int
predz x = x - pos 1

odd-col : Point → Bool
odd-col (point x _) = mod-nat ∣ x ∣ 2 ==n 1

move-hex : HexDirection → Point → Point
move-hex N (point x y) = point x (sucz y)
move-hex NE (point x y) = point (sucz x) (if odd-col (point x y) then (sucz y) else y)
move-hex NW (point x y) = point (predz x) (if odd-col (point x y) then (sucz y) else y)
move-hex S (point x y) = point x (predz y)
move-hex SE (point x y) = point (sucz x) (if odd-col (point x y) then y else (predz y))
move-hex SW (point x y) = point (predz x) (if odd-col (point x y) then y else (predz y))

neighbors-hex : Point → List Point
neighbors-hex p = map (flip move-hex p) all-dir-hex

private
  dist-hex-h : Nat → Nat → Point → Point → Nat
  dist-hex-h 0 _ _ _ = 0
  dist-hex-h (suc lm) accum (point x1 y1) (point x2 y2) with (x1 ==z x2)
  dist-hex-h (suc lm) accum (point x1 y1) (point x2 y2) | true = accum +n ∣ y2 - y1 ∣
  dist-hex-h (suc lm) accum (point x1 y1) (point x2 y2) | false with (compass-hex (point x1 y1) (point x2 y2))
  dist-hex-h (suc lm) accum (point x1 y1) (point x2 y2) | false | dir = dist-hex-h lm (suc accum) (point x1 y1) (move-hex (rev-dir-hex dir) (point x2 y2))

dist-hex : Point → Point → Nat
dist-hex (point x1 y1) (point x2 y2) = dist-hex-h (∣ x1 ∣ +n ∣ y1 ∣ +n ∣ x2 ∣ +n ∣ y2 ∣) 0 (point x1 y1) (point x2 y2)


data Dir2d : Set where
  N2D : Dir2d
  E2D : Dir2d
  S2D : Dir2d
  W2D : Dir2d

all-dir-2d : List Dir2d
all-dir-2d = N2D ∷ E2D ∷ W2D ∷ S2D ∷ []

parse-dir-2d : String → Maybe Dir2d
parse-dir-2d "n" = just N2D
parse-dir-2d "e" = just E2D
parse-dir-2d "s" = just S2D
parse-dir-2d "w" = just W2D
parse-dir-2d _ = nothing

rev-dir-2d : Dir2d → Dir2d
rev-dir-2d N2D = S2D
rev-dir-2d W2D = E2D
rev-dir-2d E2D = W2D
rev-dir-2d S2D = N2D

center-point : Point
center-point = point (pos 0) (pos 0)

compass-2d : Point → Point → Dir2d
compass-2d (point x1 y1) (point x2 y2) with (x1 ==z x2)
compass-2d (point x1 y1) (point x2 y2) | true with (y1 <z y2)
compass-2d (point x1 y1) (point x2 y2) | true | true = N2D
compass-2d (point x1 y1) (point x2 y2) | true | _ = S2D
compass-2d (point x1 y1) (point x2 y2) | _  with (x1 <z x2)
compass-2d (point x1 y1) (point x2 y2) | _  | true = E2D
compass-2d (point x1 y1) (point x2 y2) | _  | false = W2D

move-2d : Dir2d → Point → Point
move-2d N2D (point x y) = point x (sucz y)
move-2d S2D (point x y) = point x (predz y)
move-2d E2D (point x y) = point (sucz x) y
move-2d W2D (point x y) = point (predz x) y

neighbors-2d : Point → List Point
neighbors-2d p = map (flip move-2d p) all-dir-2d

dist-2d : Point → Point → Nat
dist-2d (point x1 y1) (point x2 y2) = ∣ x1 - x2 ∣ +n ∣ y1 - y2 ∣

test-move-hex-a : move-hex NE center-point ≡ point (pos 1) (pos 0)
test-move-hex-a = refl

test-move-hex-b : (show-point ∘ move-hex S ∘ move-hex N) center-point ≡ "(0, 0)"
test-move-hex-b = refl

test-move-hex-c : (show-point ∘ move-hex SE ∘ move-hex NW) center-point ≡ "(0, 0)"
test-move-hex-c = refl

test-move-hex-d : (show-point ∘ move-hex SW ∘ move-hex NE) center-point ≡ "(0, 0)"
test-move-hex-d = refl

test-dist-hex-a : (dist-hex center-point ∘ move-hex SW ∘ move-hex NE) center-point ≡ 0
test-dist-hex-a = refl

test-dist-hex-b : (dist-hex center-point ∘ move-hex N ∘ move-hex NE) center-point ≡ 2
test-dist-hex-b = refl

test-move-2d-a : (show-point ∘ move-2d S2D ∘ move-2d N2D) center-point ≡ "(0, 0)"
test-move-2d-a = refl

test-move-2d-b : (show-point ∘ move-2d N2D ∘ move-2d N2D) center-point ≡ "(0, 2)"
test-move-2d-b = refl

test-move-2d-c : (show-point ∘ move-2d W2D ∘ move-2d E2D) center-point ≡ "(0, 0)"
test-move-2d-c = refl

test-move-2d-d : (show-point ∘ move-2d E2D ∘ move-2d E2D) center-point ≡ "(2, 0)"
test-move-2d-d = refl

test-dist-2d-a : dist-2d center-point center-point ≡ 0
test-dist-2d-a = refl

test-dist-2d-b : dist-2d center-point (point (pos 2) (pos 3)) ≡ 5
test-dist-2d-b = refl

test-neigh-2d : (intersperse "," ∘ map show-point ∘ neighbors-2d) center-point ≡ "(0, 1),(1, 0),(-1, 0),(0, -1)"
test-neigh-2d = refl
