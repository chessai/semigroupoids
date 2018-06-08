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
module Data.Semigroup.Semifoldable
  ( Semifoldable(..)
  , semiintercalate
  , semiintercalateMap
  , semitraverse_
  , semifor_
  , semisemisequenceA_
  , semifoldMapDefault
  , semiasum
  , semifoldrM
  , semifoldlM
  ) where

import Data.Foldable
import Data.Functor.Alt (Alt(..))
import Data.Functor.Semiapplicative
import Data.List.NonEmpty (NonEmpty(..))
import Data.Traversable.Instances ()
import Data.Semigroup hiding (Product, Sum)
import Data.Semigroup.Semifoldable.Class
import Prelude hiding (foldr)

-- $setup
-- >>> import Data.List.NonEmpty

newtype JoinWith a = JoinWith {joinee :: (a -> a)}

instance Semigroup a => Semigroup (JoinWith a) where
  JoinWith a <> JoinWith b = JoinWith $ \j -> a j <> j <> b j

-- | Insert an 'm' between each pair of 't m'.  Equivalent to
-- 'semiintercalateMap' with 'id' as the second argument.
--
-- >>> semiintercalate ", " $ "hello" :| ["how", "are", "you"]
-- "hello, how, are, you"
--
-- >>> semiintercalate ", " $ "hello" :| []
-- "hello"
--
-- >>> semiintercalate mempty $ "I" :| ["Am", "Fine", "You?"]
-- "IAmFineYou?"
semiintercalate :: (Semifoldable t, Semigroup m) => m -> t m -> m
semiintercalate = flip semiintercalateMap id
{-# INLINE semiintercalate #-}

-- | Insert 'm' between each pair of 'm' derived from 'a'.
--
-- >>> semiintercalateMap " " show $ True :| [False, True]
-- "True False True"
--
-- >>> semiintercalateMap " " show $ True :| []
-- "True"
semiintercalateMap :: (Semifoldable t, Semigroup m) => m -> (a -> m) -> t a -> m
semiintercalateMap j f = flip joinee j . semifoldMap (JoinWith . const . f)
{-# INLINE semiintercalateMap #-}

newtype Act f a = Act { getAct :: f a }

instance Semiapplicative f => Semigroup (Act f a) where
  Act a <> Act b = Act (a .> b)

instance Functor f => Functor (Act f) where
  fmap f (Act a) = Act (f <$> a)
  b <$ Act a = Act (b <$ a)

semitraverse_ :: (Semifoldable t, Semiapplicative f) => (a -> f b) -> t a -> f ()
semitraverse_ f t = () <$ getAct (semifoldMap (Act . f) t)
{-# INLINE semitraverse_ #-}

semifor_ :: (Semifoldable t, Semiapplicative f) => t a -> (a -> f b) -> f ()
semifor_ = flip semitraverse_
{-# INLINE semifor_ #-}

semisemisequenceA_ :: (Semifoldable t, Semiapplicative f) => t (f a) -> f ()
semisemisequenceA_ t = () <$ getAct (semifoldMap Act t)
{-# INLINE semisemisequenceA_ #-}

-- | Usable default for foldMap, but only if you define semifoldMap yourself
semifoldMapDefault :: (Semifoldable t, Monoid m) => (a -> m) -> t a -> m
semifoldMapDefault f = unwrapMonoid . foldMap (WrapMonoid . f)
{-# INLINE semifoldMapDefault #-}

-- toStream :: Semifoldable t => t a -> Stream a
-- concat1 :: Semifoldable t => t (Stream a) -> Stream a
-- concatMap1 :: Semifoldable t => (a -> Stream b) -> t a -> Stream b

newtype Alt_ f a = Alt_ { getAlt_ :: f a }

instance Alt f => Semigroup (Alt_ f a) where
  Alt_ a <> Alt_ b = Alt_ (a <!> b)

semiasum :: (Semifoldable t, Alt m) => t (m a) -> m a
semiasum = getAlt_ . semifoldMap Alt_
{-# INLINE semiasum #-}

-- | Monadic fold over the elements of a non-empty structure,
-- associating to the right, i.e. from right to left.
--
-- > let g = (=<<) . f
-- > in semifoldrM f (x1 :| [x2, ..., xn]) == x1 `g` (x2 `g` ... (xn-1 `f` xn)...)
--
semifoldrM :: (Semifoldable t, Monad m) => (a -> a -> m a) -> t a -> m a
semifoldrM f = go . toNonEmpty
  where
    g = (=<<) . f
    
    go (e:|es) =
      case es of
        []   -> return e
        x:xs -> e `g` (go (x:|xs))

-- | Monadic fold over the elements of a non-empty structure,
-- associating to the left, i.e. from left to right.
--
-- > let g = flip $ (=<<) . f
-- > in semifoldlM f (x1 :| [x2, ..., xn]) == (...((x1 `f` x2) `g` x2) `g`...) `g` xn
--
semifoldlM :: (Semifoldable t, Monad m) => (a -> a -> m a) -> t a -> m a
semifoldlM f t = foldlM f x xs
  where
    x:|xs = toNonEmpty t
