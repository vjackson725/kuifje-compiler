module Language.Kuifje.ShallowConsts where

-- This file is a little bit evil.
-- It uses unsafePerformIO and IORef to give us global mutable constants
-- without an IO wrapper. This is wildly unsafe, but we assume these
-- are only written once, in the logic that reads in command line arguments.
-- This makes it somewhat okay.

import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

-- Rationals are converted to decimal numbers on printing
-- If this integer is negative, they are printed as exact rationals
-- defaults to 2
refDecimalPrecision :: IORef Integer
{-# NOINLINE refDecimalPrecision #-}
refDecimalPrecision = unsafePerformIO $ newIORef 2

writeDecimalPrecision :: Integer -> IO ()
writeDecimalPrecision x = writeIORef refDecimalPrecision x

decimalPrecision :: Integer
decimalPrecision = unsafePerformIO $ readIORef refDecimalPrecision