{-# LANGUAGE CPP #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2011-2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
----------------------------------------------------------------------------
module Data.Semigroup.Semitraversable
  ( Semitraversable(..)
  , semifoldMapDefault
  ) where

import Control.Applicative
#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup
#endif
import Data.Semigroup.Semitraversable.Class

semifoldMapDefault :: (Semitraversable f, Semigroup m) => (a -> m) -> f a -> m
semifoldMapDefault f = getConst . semitraverse (Const . f)
