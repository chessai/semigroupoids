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
module Data.Semigroup.Semibitraversable
  ( Semibitraversable(..)
  , semibifoldMapDefault
  ) where

import Control.Applicative
#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup
#endif
import Data.Semigroup.Semitraversable.Class

semibifoldMapDefault :: (Semibitraversable t, Semigroup m) => (a -> m) -> (b -> m) -> t a b -> m
semibifoldMapDefault f g = getConst . semibitraverse (Const . f) (Const . g)
{-# INLINE semibifoldMapDefault #-}
