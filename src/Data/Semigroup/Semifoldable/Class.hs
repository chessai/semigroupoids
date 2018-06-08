{-# LANGUAGE CPP, TypeOperators #-}

#ifndef MIN_VERSION_semigroups
#define MIN_VERSION_semigroups(x,y,z) 0
#endif

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
module Data.Semigroup.Semifoldable.Class
  ( Semifoldable(..)
  , Semibifoldable(..)
  ) where

import Control.Applicative
import Control.Applicative.Backwards
import Control.Applicative.Lift
import Control.Monad.Trans.Identity
import Data.Bifoldable
import Data.Bifunctor.Biff
import Data.Bifunctor.Clown
import Data.Bifunctor.Flip
import Data.Bifunctor.Join
import Data.Bifunctor.Product as Bifunctor
import Data.Bifunctor.Joker
import Data.Bifunctor.Tannen
import Data.Bifunctor.Wrapped
import Data.Foldable

import Data.Functor.Identity
import Data.Functor.Product as Functor
import Data.Functor.Reverse
import Data.Functor.Sum as Functor
import Data.Functor.Compose
import Data.List.NonEmpty (NonEmpty(..))

#if MIN_VERSION_base(4,4,0)
import Data.Complex
#endif

#ifdef MIN_VERSION_tagged
import Data.Tagged
#endif

import Data.Traversable.Instances ()

#ifdef MIN_VERSION_containers
import Data.Tree
#endif

import Data.Monoid as Monoid hiding ((<>))
import Data.Semigroup as Semigroup hiding (Product, Sum)
import Data.Orphans ()
-- import Data.Ord -- missing Foldable, https://ghc.haskell.org/trac/ghc/ticket/15098#ticket

#ifdef MIN_VERSION_generic_deriving
import Generics.Deriving.Base
#else
import GHC.Generics
#endif

import Prelude hiding (foldr)

class Foldable t => Semifoldable t where
  semifold :: Semigroup m => t m -> m
  semifoldMap :: Semigroup m => (a -> m) -> t a -> m
  toNonEmpty :: t a -> NonEmpty a

  semifoldMap f = maybe (error "semifoldMap") id . getOption . foldMap (Option . Just . f)
  semifold = semifoldMap id
  toNonEmpty = semifoldMap (:|[])

instance Semifoldable Monoid.Sum where
  semifoldMap f (Monoid.Sum a) = f a

instance Semifoldable Monoid.Product where
  semifoldMap f (Monoid.Product a) = f a

instance Semifoldable Monoid.Dual where
  semifoldMap f (Monoid.Dual a) = f a

#if MIN_VERSION_base(4,8,0)
instance Semifoldable f => Semifoldable (Monoid.Alt f) where
  semifoldMap g (Alt m) = semifoldMap g m
#endif

instance Semifoldable Semigroup.First where
  semifoldMap f (Semigroup.First a) = f a

instance Semifoldable Semigroup.Last where
  semifoldMap f (Semigroup.Last a) = f a

instance Semifoldable Semigroup.Min where
  semifoldMap f (Semigroup.Min a) = f a

instance Semifoldable Semigroup.Max where
  semifoldMap f (Semigroup.Max a) = f a

instance Semifoldable f => Semifoldable (Rec1 f) where
  semifoldMap f (Rec1 as) = semifoldMap f as

instance Semifoldable f => Semifoldable (M1 i c f) where
  semifoldMap f (M1 as) = semifoldMap f as

instance Semifoldable Par1 where
  semifoldMap f (Par1 a) = f a

instance (Semifoldable f, Semifoldable g) => Semifoldable (f :*: g) where
  semifoldMap f (as :*: bs) = semifoldMap f as <> semifoldMap f bs

instance (Semifoldable f, Semifoldable g) => Semifoldable (f :+: g) where
  semifoldMap f (L1 as) = semifoldMap f as
  semifoldMap f (R1 bs) = semifoldMap f bs

instance Semifoldable V1 where
  semifoldMap _ v = v `seq` undefined

instance (Semifoldable f, Semifoldable g) => Semifoldable (f :.: g) where
  semifoldMap f (Comp1 m) = semifoldMap (semifoldMap f) m

class Bifoldable t => Semibifoldable t where
  semibifold :: Semigroup m => t m m -> m
  semibifold = semibifoldMap id id
  {-# INLINE semibifold #-}

  semibifoldMap :: Semigroup m => (a -> m) -> (b -> m) -> t a b -> m
  semibifoldMap f g = maybe (error "semibifoldMap") id . getOption . bifoldMap (Option . Just . f) (Option . Just . g)
  {-# INLINE semibifoldMap #-}

#if MIN_VERSION_semigroups(0,16,2)
instance Semibifoldable Arg where
  semibifoldMap f g (Arg a b) = f a <> g b
#endif

instance Semibifoldable Either where
  semibifoldMap f _ (Left a) = f a
  semibifoldMap _ g (Right b) = g b
  {-# INLINE semibifoldMap #-}

instance Semibifoldable (,) where
  semibifoldMap f g (a, b) = f a <> g b
  {-# INLINE semibifoldMap #-}

instance Semibifoldable ((,,) x) where
  semibifoldMap f g (_,a,b) = f a <> g b
  {-# INLINE semibifoldMap #-}

instance Semibifoldable ((,,,) x y) where
  semibifoldMap f g (_,_,a,b) = f a <> g b
  {-# INLINE semibifoldMap #-}

instance Semibifoldable ((,,,,) x y z) where
  semibifoldMap f g (_,_,_,a,b) = f a <> g b
  {-# INLINE semibifoldMap #-}

instance Semibifoldable Const where
  semibifoldMap f _ (Const a) = f a
  {-# INLINE semibifoldMap #-}

#ifdef MIN_VERSION_tagged
instance Semibifoldable Tagged where
  semibifoldMap _ g (Tagged b) = g b
  {-# INLINE semibifoldMap #-}
#endif

instance (Semibifoldable p, Semifoldable f, Semifoldable g) => Semibifoldable (Biff p f g) where
  semibifoldMap f g = semibifoldMap (semifoldMap f) (semifoldMap g) . runBiff
  {-# INLINE semibifoldMap #-}

instance Semifoldable f => Semibifoldable (Clown f) where
  semibifoldMap f _ = semifoldMap f . runClown
  {-# INLINE semibifoldMap #-}

instance Semibifoldable p => Semibifoldable (Flip p) where
  semibifoldMap f g = semibifoldMap g f . runFlip
  {-# INLINE semibifoldMap #-}

instance Semibifoldable p => Semifoldable (Join p) where
  semifoldMap f (Join a) = semibifoldMap f f a
  {-# INLINE semifoldMap #-}

instance Semifoldable g => Semibifoldable (Joker g) where
  semibifoldMap _ g = semifoldMap g . runJoker
  {-# INLINE semibifoldMap #-}

instance (Semibifoldable f, Semibifoldable g) => Semibifoldable (Bifunctor.Product f g) where
  semibifoldMap f g (Bifunctor.Pair x y) = semibifoldMap f g x <> semibifoldMap f g y
  {-# INLINE semibifoldMap #-}

instance (Semifoldable f, Semibifoldable p) => Semibifoldable (Tannen f p) where
  semibifoldMap f g = semifoldMap (semibifoldMap f g) . runTannen
  {-# INLINE semibifoldMap #-}

instance Semibifoldable p => Semibifoldable (WrappedBifunctor p) where
  semibifoldMap f g = semibifoldMap f g . unwrapBifunctor
  {-# INLINE semibifoldMap #-}

#if MIN_VERSION_base(4,4,0)
instance Semifoldable Complex where
  semifoldMap f (a :+ b) = f a <> f b
  {-# INLINE semifoldMap #-}
#endif

#ifdef MIN_VERSION_containers
instance Semifoldable Tree where
  semifoldMap f (Node a []) = f a
  semifoldMap f (Node a (x:xs)) = f a <> semifoldMap (semifoldMap f) (x :| xs)
#endif

instance Semifoldable Identity where
  semifoldMap f = f . runIdentity

#ifdef MIN_VERSION_tagged
instance Semifoldable (Tagged a) where
  semifoldMap f (Tagged a) = f a
#endif

instance Semifoldable m => Semifoldable (IdentityT m) where
  semifoldMap f = semifoldMap f . runIdentityT

instance Semifoldable f => Semifoldable (Backwards f) where
  semifoldMap f = semifoldMap f . forwards

instance (Semifoldable f, Semifoldable g) => Semifoldable (Compose f g) where
  semifoldMap f = semifoldMap (semifoldMap f) . getCompose

instance Semifoldable f => Semifoldable (Lift f) where
  semifoldMap f (Pure x)  = f x
  semifoldMap f (Other y) = semifoldMap f y

instance (Semifoldable f, Semifoldable g) => Semifoldable (Functor.Product f g) where
  semifoldMap f (Functor.Pair a b) = semifoldMap f a <> semifoldMap f b

instance Semifoldable f => Semifoldable (Reverse f) where
  semifoldMap f = getDual . semifoldMap (Dual . f) . getReverse

instance (Semifoldable f, Semifoldable g) => Semifoldable (Functor.Sum f g) where
  semifoldMap f (Functor.InL x) = semifoldMap f x
  semifoldMap f (Functor.InR y) = semifoldMap f y

instance Semifoldable NonEmpty where
  semifoldMap f (a :| []) = f a
  semifoldMap f (a :| b : bs) = f a <> semifoldMap f (b :| bs)
  toNonEmpty = id

instance Semifoldable ((,) a) where
  semifoldMap f (_, x) = f x

instance Semifoldable g => Semifoldable (Joker g a) where
  semifoldMap g = semifoldMap g . runJoker
  {-# INLINE semifoldMap #-}
