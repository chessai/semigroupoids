{-# LANGUAGE CPP, TypeOperators #-}
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
module Data.Semigroup.Semitraversable.Class
  ( Semibitraversable(..)
  , Semitraversable(..)
  ) where

import Control.Applicative
import Control.Applicative.Backwards
import Control.Applicative.Lift
import Control.Monad.Trans.Identity
import Data.Bitraversable
import Data.Bifunctor
import Data.Bifunctor.Biff
import Data.Bifunctor.Clown
import Data.Bifunctor.Flip
import Data.Bifunctor.Joker
import Data.Bifunctor.Join
import Data.Bifunctor.Product as Bifunctor
import Data.Bifunctor.Tannen
import Data.Bifunctor.Wrapped
import Data.Functor.Semiapplicative
import Data.Functor.Compose

import Data.Functor.Identity
import Data.Functor.Product as Functor
import Data.Functor.Reverse
import Data.Functor.Sum as Functor
import Data.List.NonEmpty (NonEmpty(..))
import Data.Monoid as Monoid hiding ((<>))
import Data.Orphans ()
import Data.Semigroup as Semigroup
import Data.Semigroup.Semifoldable.Class (Semifoldable)
import Data.Semigroup.Semibifoldable
#ifdef MIN_VERSION_tagged
import Data.Tagged
#endif
#if __GLASGOW_HASKELL__ < 710
import Data.Traversable
#endif
import Data.Traversable.Instances ()

#if MIN_VERSION_base(4,4,0)
import Data.Complex
#endif

#ifdef MIN_VERSION_containers
import Data.Tree
#endif

#ifdef MIN_VERSION_generic_deriving
import Generics.Deriving.Base
#else
import GHC.Generics
#endif

class (Semibifoldable t, Bitraversable t) => Semibitraversable t where
  semibitraverse :: Semiapplicative f => (a -> f b) -> (c -> f d) -> t a c -> f (t b d)
  semibitraverse f g  = semibisequence . bimap f g
  {-# INLINE semibitraverse #-}

  semibisequence :: Semiapplicative f => t (f a) (f b) -> f (t a b)
  semibisequence = semibitraverse id id
  {-# INLINE semibisequence #-}

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
  {-# MINIMAL semibitraverse | semibisequence #-}
#endif

#if MIN_VERSION_semigroups(0,16,2)
instance Semibitraversable Arg where
  semibitraverse f g (Arg a b) = Arg <$> f a <.> g b
#endif

instance Semibitraversable Either where
  semibitraverse f _ (Left a) = Left <$> f a
  semibitraverse _ g (Right b) = Right <$> g b
  {-# INLINE semibitraverse #-}

instance Semibitraversable (,) where
  semibitraverse f g (a, b) = (,) <$> f a <.> g b
  {-# INLINE semibitraverse #-}

instance Semibitraversable ((,,) x) where
  semibitraverse f g (x, a, b) = (,,) x <$> f a <.> g b
  {-# INLINE semibitraverse #-}

instance Semibitraversable ((,,,) x y) where
  semibitraverse f g (x, y, a, b) = (,,,) x y <$> f a <.> g b
  {-# INLINE semibitraverse #-}

instance Semibitraversable ((,,,,) x y z) where
  semibitraverse f g (x, y, z, a, b) = (,,,,) x y z <$> f a <.> g b
  {-# INLINE semibitraverse #-}

instance Semibitraversable Const where
  semibitraverse f _ (Const a) = Const <$> f a
  {-# INLINE semibitraverse #-}

#ifdef MIN_VERSION_tagged
instance Semibitraversable Tagged where
  semibitraverse _ g (Tagged b) = Tagged <$> g b
  {-# INLINE semibitraverse #-}
#endif

instance (Semibitraversable p, Semitraversable f, Semitraversable g) => Semibitraversable (Biff p f g) where
  semibitraverse f g = fmap Biff . semibitraverse (semitraverse f) (semitraverse g) . runBiff
  {-# INLINE semibitraverse #-}

instance Semitraversable f => Semibitraversable (Clown f) where
  semibitraverse f _ = fmap Clown . semitraverse f . runClown
  {-# INLINE semibitraverse #-}

instance Semibitraversable p => Semibitraversable (Flip p) where
  semibitraverse f g = fmap Flip . semibitraverse g f . runFlip
  {-# INLINE semibitraverse #-}

instance Semibitraversable p => Semitraversable (Join p) where
  semitraverse f (Join a) = fmap Join (semibitraverse f f a)
  {-# INLINE semitraverse #-}
  semisequence (Join a) = fmap Join (semibisequence a)
  {-# INLINE semisequence #-}

instance Semitraversable g => Semibitraversable (Joker g) where
  semibitraverse _ g = fmap Joker . semitraverse g . runJoker
  {-# INLINE semibitraverse #-}

instance (Semibitraversable f, Semibitraversable g) => Semibitraversable (Bifunctor.Product f g) where
  semibitraverse f g (Bifunctor.Pair x y) = Bifunctor.Pair <$> semibitraverse f g x <.> semibitraverse f g y
  {-# INLINE semibitraverse #-}

instance (Semitraversable f, Semibitraversable p) => Semibitraversable (Tannen f p) where
  semibitraverse f g = fmap Tannen . semitraverse (semibitraverse f g) . runTannen
  {-# INLINE semibitraverse #-}

instance Semibitraversable p => Semibitraversable (WrappedBifunctor p) where
  semibitraverse f g = fmap WrapBifunctor . semibitraverse f g . unwrapBifunctor
  {-# INLINE semibitraverse #-}


class (Semifoldable t, Traversable t) => Semitraversable t where
  semitraverse :: Semiapplicative f => (a -> f b) -> t a -> f (t b)
  semisequence :: Semiapplicative f => t (f b) -> f (t b)

  semisequence = semitraverse id
  semitraverse f = semisequence . fmap f

#if __GLASGOW_HASKELL__ >= 708
  {-# MINIMAL semitraverse | semisequence #-}
#endif

instance Semitraversable f => Semitraversable (Rec1 f) where
  semitraverse f (Rec1 as) = Rec1 <$> semitraverse f as

instance Semitraversable f => Semitraversable (M1 i c f) where
  semitraverse f (M1 as) = M1 <$> semitraverse f as

instance Semitraversable Par1 where
  semitraverse f (Par1 a) = Par1 <$> f a

instance Semitraversable V1 where
  semitraverse _ v = v `seq` undefined

instance (Semitraversable f, Semitraversable g) => Semitraversable (f :*: g) where
  semitraverse f (as :*: bs) = (:*:) <$> semitraverse f as <.> semitraverse f bs

instance (Semitraversable f, Semitraversable g) => Semitraversable (f :+: g) where
  semitraverse f (L1 as) = L1 <$> semitraverse f as
  semitraverse f (R1 bs) = R1 <$> semitraverse f bs

instance (Semitraversable f, Semitraversable g) => Semitraversable (f :.: g) where
  semitraverse f (Comp1 m) = Comp1 <$> semitraverse (semitraverse f) m

instance Semitraversable Identity where
  semitraverse f = fmap Identity . f . runIdentity

instance Semitraversable f => Semitraversable (IdentityT f) where
  semitraverse f = fmap IdentityT . semitraverse f . runIdentityT

instance Semitraversable f => Semitraversable (Backwards f) where
  semitraverse f = fmap Backwards . semitraverse f . forwards

instance (Semitraversable f, Semitraversable g) => Semitraversable (Compose f g) where
  semitraverse f = fmap Compose . semitraverse (semitraverse f) . getCompose

instance Semitraversable f => Semitraversable (Lift f) where
  semitraverse f (Pure x)  = Pure <$> f x
  semitraverse f (Other y) = Other <$> semitraverse f y

instance (Semitraversable f, Semitraversable g) => Semitraversable (Functor.Product f g) where
  semitraverse f (Functor.Pair a b) = Functor.Pair <$> semitraverse f a <.> semitraverse f b

instance Semitraversable f => Semitraversable (Reverse f) where
  semitraverse f = fmap Reverse . forwards . semitraverse (Backwards . f) . getReverse

instance (Semitraversable f, Semitraversable g) => Semitraversable (Functor.Sum f g) where
  semitraverse f (Functor.InL x) = Functor.InL <$> semitraverse f x
  semitraverse f (Functor.InR y) = Functor.InR <$> semitraverse f y

#if MIN_VERSION_base(4,4,0)
instance Semitraversable Complex where
  semitraverse f (a :+ b) = (:+) <$> f a <.> f b
  {-# INLINE semitraverse #-}
#endif

#ifdef MIN_VERSION_tagged
instance Semitraversable (Tagged a) where
  semitraverse f (Tagged a) = Tagged <$> f a
#endif

#ifdef MIN_VERSION_containers
instance Semitraversable Tree where
  semitraverse f (Node a []) = (`Node`[]) <$> f a
  semitraverse f (Node a (x:xs)) = (\b (y:|ys) -> Node b (y:ys)) <$> f a <.> semitraverse (semitraverse f) (x :| xs)
#endif

instance Semitraversable NonEmpty where
  semitraverse f (a :| []) = (:|[]) <$> f a
  semitraverse f (a :| (b: bs)) = (\a' (b':| bs') -> a' :| b': bs') <$> f a <.> semitraverse f (b :| bs)

instance Semitraversable ((,) a) where
  semitraverse f (a, b) = (,) a <$> f b

instance Semitraversable g => Semitraversable (Joker g a) where
  semitraverse g = fmap Joker . semitraverse g . runJoker
  {-# INLINE semitraverse #-}

instance Semitraversable Monoid.Sum where
  semitraverse g (Monoid.Sum a) = Monoid.Sum <$> g a

instance Semitraversable Monoid.Product where
  semitraverse g (Monoid.Product a) = Monoid.Product <$> g a

instance Semitraversable Monoid.Dual where
  semitraverse g (Monoid.Dual a) = Monoid.Dual <$> g a

#if MIN_VERSION_base(4,8,0)
instance Semitraversable f => Semitraversable (Monoid.Alt f) where
  semitraverse g (Alt m) = Alt <$> semitraverse g m
#endif

instance Semitraversable Semigroup.First where
  semitraverse g (Semigroup.First a) = Semigroup.First <$> g a

instance Semitraversable Semigroup.Last where
  semitraverse g (Semigroup.Last a) = Semigroup.Last <$> g a

instance Semitraversable Semigroup.Min where
  semitraverse g (Semigroup.Min a) = Semigroup.Min <$> g a

instance Semitraversable Semigroup.Max where
  semitraverse g (Semigroup.Max a) = Semigroup.Max <$> g a
