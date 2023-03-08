module advent2016 where

open import Agda.Builtin.IO
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String

open import d1.taxi using (calc-taxi-dist ; calc-taxi-twice)

postulate interact : (String → String) → IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC interact = \ f -> interact ( T.unpack . f . T.pack ) #-}

main : IO ⊤
main = interact calc-taxi-twice

