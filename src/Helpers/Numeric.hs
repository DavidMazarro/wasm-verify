{-# LANGUAGE CPP #-}

module Helpers.Numeric where

import Data.Word (Word32, Word64)
#if MIN_VERSION_base(4,15,0)
import GHC.Natural
#elif MIN_VERSION_base(4,12,0)
#else 
import GHC.Natural
#endif

i32ToSignedInteger :: Word32 -> Integer
i32ToSignedInteger n
  | n <= (maxBound :: Word32) `div` 2 = fromIntegral n
  | otherwise = fromIntegral n - fromIntegral (maxBound :: Word32) - 1

i64ToSignedInteger :: Word64 -> Integer
i64ToSignedInteger n
  | n <= (maxBound :: Word64) `div` 2 = fromIntegral n
  | otherwise = fromIntegral n - fromIntegral (maxBound :: Word64) - 1

-- 'naturalToInt' and 'intToNatural' were only available in the base library
-- from version 4.12.0 up to 4.14.3, for some reason
-- unbeknownst to me. So this piece here defines the function
-- when the system's GHC base version is outside that range.
#if MIN_VERSION_base(4,15,0)
naturalToInt :: Natural -> Int
naturalToInt = fromInteger . naturalToInteger
intToNatural :: Int -> Natural
intToNatural = integerToNatural . toInteger
#elif MIN_VERSION_base(4,12,0)
#else 
naturalToInt :: Natural -> Int
naturalToInt = fromInteger . naturalToInteger
intToNatural :: Int -> Natural
intToNatural = integerToNatural . toInteger
#endif
