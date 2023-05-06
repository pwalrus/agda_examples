

module util.hash where

open import Agda.Builtin.String using (String)

postulate hash-md5 : String → String

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import Data.Digest.Pure.MD5 as M #-}
{-# FOREIGN GHC import Data.ByteString.Lazy.Char8 as C #-}

{-# COMPILE GHC hash-md5 = T.pack . show . md5 . C.pack . T.unpack  #-}

