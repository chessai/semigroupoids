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
module Data.Semigroup.Semibifoldable
  ( Semibifoldable(..)
  , semibitraverse_
  , semibifor_
  , semisemisemibisequenceA_
  , semibifoldMapDefault
  ) where

import Control.Applicative
import Data.Bifoldable
import Data.Functor.Semiapplicative
import Data.Semigroup
import Data.Semigroup.Semifoldable.Class
import Prelude hiding (foldr)

newtype Act f a = Act { getAct :: f a }

instance Semiapplicative f => Semigroup (Act f a) where
  Act a <> Act b = Act (a .> b)
  {-# INLINE (<>) #-}

instance Functor f => Functor (Act f) where
  fmap f (Act a) = Act (f <$> a)
  {-# INLINE fmap #-}
  b <$ Act a = Act (b <$ a)
  {-# INLINE (<$) #-}

semibitraverse_ :: (Semibifoldable t, Semiapplicative f) => (a -> f b) -> (c -> f d) -> t a c -> f ()
semibitraverse_ f g t = getAct (semibifoldMap (Act . ignore . f) (Act . ignore . g) t)
{-# INLINE semibitraverse_ #-}

semibifor_ :: (Semibifoldable t, Semiapplicative f) => t a c -> (a -> f b) -> (c -> f d) -> f ()
semibifor_ t f g = semibitraverse_ f g t
{-# INLINE semibifor_ #-}

ignore :: Functor f => f a -> f ()
ignore = (() <$)
{-# INLINE ignore #-}

semisemisemibisequenceA_ :: (Semibifoldable t, Semiapplicative f) => t (f a) (f b) -> f ()
semisemisemibisequenceA_ t = getAct (semibifoldMap (Act . ignore) (Act . ignore) t)
{-# INLINE semisemisemibisequenceA_ #-}

-- | Usable default for foldMap, but only if you define semibifoldMap yourself
semibifoldMapDefault :: (Semibifoldable t, Monoid m) => (a -> m) -> (b -> m) -> t a b -> m
semibifoldMapDefault f g = unwrapMonoid . bifoldMap (WrapMonoid . f) (WrapMonoid . g)
{-# INLINE semibifoldMapDefault #-}
