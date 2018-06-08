{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
#if __GLASGOW_HASKELL__ >= 708
{-# LANGUAGE EmptyCase #-}
#endif

#ifndef MIN_VERSION_semigroups
#define MIN_VERSION_semigroups(x,y,z) 1
#endif

#if __GLASGOW_HASKELL__ >= 702 && __GLASGOW_HASKELL <= 706 && defined(MIN_VERSION_comonad) && !(MIN_VERSION_comonad(3,0,3))
{-# LANGUAGE Trustworthy #-}
#endif

{-# OPTIONS_HADDOCK not-home #-}

#if __GLASGOW_HASKELL__ >= 708 && __GLASGOW_HASKELL__ < 710
{-# OPTIONS_GHC -fno-warn-amp #-}
#endif

{-# OPTIONS_GHC -fno-warn-deprecations #-}

-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2011-2018 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- This module is used to resolve the cyclic we get from defining these
-- classes here rather than in a package upstream. Otherwise we'd get
-- orphaned heads for many instances on the types in @transformers@ and @bifunctors@.
----------------------------------------------------------------------------
module Data.Functor.Semimonad.Class (
  -- * Semiapplicativeable functors
    Semiapplicative(..)
  -- * Wrappers
  , WrappedApplicative(..)
  , MaybeSemiapplicative(..)
  -- * Semimonadable functors
  , Semimonad(..)
  , apDefault
  , returning
  -- * Biappliable bifunctors
  , Biapply(..)
  ) where

import Data.Semigroup
import Control.Applicative
import Control.Applicative.Backwards
import Control.Applicative.Lift
import Control.Arrow
import Control.Category
import Control.Monad (ap)
import Control.Monad.Trans.Cont
import Control.Monad.Trans.Error
import Control.Monad.Trans.Except
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader
import Control.Monad.Trans.List
import qualified Control.Monad.Trans.RWS.Lazy as Lazy
import qualified Control.Monad.Trans.State.Lazy as Lazy
import qualified Control.Monad.Trans.Writer.Lazy as Lazy
import qualified Control.Monad.Trans.RWS.Strict as Strict
import qualified Control.Monad.Trans.State.Strict as Strict
import qualified Control.Monad.Trans.Writer.Strict as Strict
import Data.Biapplicative
import Data.Bifunctor.Biff
import Data.Bifunctor.Clown
import Data.Bifunctor.Flip
import Data.Bifunctor.Joker
import Data.Bifunctor.Join
import Data.Bifunctor.Product as Bifunctor
import Data.Bifunctor.Tannen
import Data.Bifunctor.Wrapped
import Data.Functor.Compose
import Data.Functor.Constant
import Data.Functor.Identity
import Data.Functor.Product as Functor
import Data.Functor.Reverse
import Data.Functor.Extend
import Data.List.NonEmpty
import Data.Semigroup as Semigroup
import Data.Monoid as Monoid hiding ((<>))
import Data.Orphans ()
import GHC.Generics as Generics
import Language.Haskell.TH (Q)
import Prelude hiding (id, (.))

#if MIN_VERSION_base(4,6,0)
import Data.Ord (Down (..))
#else
import GHC.Exts (Down (..))
#endif


#if MIN_VERSION_base(4,4,0)
import Data.Complex
#endif

#ifdef MIN_VERSION_containers
import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Sequence (Seq)
import Data.Tree (Tree)
#endif

#ifdef MIN_VERSION_tagged
import Data.Tagged
#endif

#if defined(MIN_VERSION_tagged) || MIN_VERSION_base(4,7,0)
import Data.Proxy
#endif

#ifdef MIN_VERSION_unordered_containers
import Data.Hashable
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
#endif

#ifdef MIN_VERSION_comonad
import Control.Comonad
import Control.Comonad.Trans.Env
import Control.Comonad.Trans.Store
import Control.Comonad.Trans.Traced
#else
($>) :: Functor f => f a -> b -> f b
($>) = flip (<$)
#endif

infixl 1 >>-
infixl 4 <.>, <., .>

-- | A strong lax semi-monoidal endofunctor.
-- This is equivalent to an 'Applicative' without 'pure'.
--
-- Laws:
--
-- @
-- ('.') '<$>' u '<.>' v '<.>' w = u '<.>' (v '<.>' w)
-- x '<.>' (f '<$>' y) = ('.' f) '<$>' x '<.>' y
-- f '<$>' (x '<.>' y) = (f '.') '<$>' x '<.>' y
-- @
--
-- The laws imply that `.>` and `<.` really ignore their
-- left and right results, respectively, and really
-- return their right and left results, respectively.
-- Specifically,
--
-- @
-- (mf '<$>' m) '.>' (nf '<$>' n) = nf '<$>' (m '.>' n)
-- (mf '<$>' m) '<.' (nf '<$>' n) = mf '<$>' (m '<.' n)
-- @
class Functor f => Semiapplicative f where
  (<.>) :: f (a -> b) -> f a -> f b
  (<.>) = liftF2 id

  -- | @ a '.>' b = 'const' 'id' '<$>' a '<.>' b @
  (.>) :: f a -> f b -> f b
  a .> b = const id <$> a <.> b

  -- | @ a '<.' b = 'const' '<$>' a '<.>' b @
  (<.) :: f a -> f b -> f a
  a <. b = const <$> a <.> b

  -- | Lift a binary function into a comonad with zipping
  liftF2 :: (a -> b -> c) -> f a -> f b -> f c
  liftF2 f a b = f <$> a <.> b
  {-# INLINE liftF2 #-}

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
  {-# MINIMAL (<.>) | liftF2 #-}
#endif

#ifdef MIN_VERSION_tagged
instance Semiapplicative (Tagged a) where
  (<.>) = (<*>)
  (<.) = (<*)
  (.>) = (*>)
#endif

#if defined(MIN_VERSION_tagged) || MIN_VERSION_base(4,7,0)
instance Semiapplicative Proxy where
  (<.>) = (<*>)
  (<.) = (<*)
  (.>) = (*>)
#endif

instance Semiapplicative f => Semiapplicative (Backwards f) where
  Backwards f <.> Backwards a = Backwards (flip id <$> a <.> f)

instance (Semiapplicative f, Semiapplicative g) => Semiapplicative (Compose f g) where
  Compose f <.> Compose x = Compose ((<.>) <$> f <.> x)

instance Semigroup f => Semiapplicative (Constant f) where
  Constant a <.> Constant b = Constant (a <> b)
  Constant a <.  Constant b = Constant (a <> b)
  Constant a  .> Constant b = Constant (a <> b)

instance Semiapplicative f => Semiapplicative (Lift f) where
  Pure f  <.> Pure x  = Pure (f x)
  Pure f  <.> Other y = Other (f <$> y)
  Other f <.> Pure x  = Other (($ x) <$> f)
  Other f <.> Other y = Other (f <.> y)

instance (Semiapplicative f, Semiapplicative g) => Semiapplicative (Functor.Product f g) where
  Functor.Pair f g <.> Functor.Pair x y = Functor.Pair (f <.> x) (g <.> y)

instance Semiapplicative f => Semiapplicative (Reverse f) where
  Reverse a <.> Reverse b = Reverse (a <.> b)

instance Semigroup m => Semiapplicative ((,)m) where
  (m, f) <.> (n, a) = (m <> n, f a)
  (m, a) <.  (n, _) = (m <> n, a)
  (m, _)  .> (n, b) = (m <> n, b)

instance Semiapplicative NonEmpty where
  (<.>) = ap

instance Semiapplicative (Either a) where
  Left a  <.> _       = Left a
  Right _ <.> Left a  = Left a
  Right f <.> Right b = Right (f b)

  Left a  <.  _       = Left a
  Right _ <.  Left a  = Left a
  Right a <.  Right _ = Right a

  Left a   .> _       = Left a
  Right _  .> Left a  = Left a
  Right _  .> Right b = Right b

instance Semigroup m => Semiapplicative (Const m) where
  Const m <.> Const n = Const (m <> n)
  Const m <.  Const n = Const (m <> n)
  Const m  .> Const n = Const (m <> n)

instance Semiapplicative ((->)m) where
  (<.>) = (<*>)
  (<. ) = (<* )
  ( .>) = ( *>)

instance Semiapplicative ZipList where
  (<.>) = (<*>)
  (<. ) = (<* )
  ( .>) = ( *>)

instance Semiapplicative [] where
  (<.>) = (<*>)
  (<. ) = (<* )
  ( .>) = ( *>)

instance Semiapplicative IO where
  (<.>) = (<*>)
  (<. ) = (<* )
  ( .>) = ( *>)

instance Semiapplicative Maybe where
  (<.>) = (<*>)
  (<. ) = (<* )
  ( .>) = ( *>)

instance Semiapplicative Option where
  (<.>) = (<*>)
  (<. ) = (<* )
  ( .>) = ( *>)

instance Semiapplicative Identity where
  (<.>) = (<*>)
  (<. ) = (<* )
  ( .>) = ( *>)

instance Semiapplicative w => Semiapplicative (IdentityT w) where
  IdentityT wa <.> IdentityT wb = IdentityT (wa <.> wb)

instance Monad m => Semiapplicative (WrappedMonad m) where
  (<.>) = (<*>)
  (<. ) = (<* )
  ( .>) = ( *>)

instance Arrow a => Semiapplicative (WrappedArrow a b) where
  (<.>) = (<*>)
  (<. ) = (<* )
  ( .>) = ( *>)

#if MIN_VERSION_base(4,4,0)
instance Semiapplicative Complex where
  (a :+ b) <.> (c :+ d) = a c :+ b d
#endif

-- Applicative Q was only added in template-haskell 2.7 (GHC 7.4), so
-- define in terms of Monad instead.
instance Semiapplicative Q where
  (<.>) = ap

#ifdef MIN_VERSION_containers
-- | A Map is not 'Applicative', but it is an instance of 'Semiapplicative'
instance Ord k => Semiapplicative (Map k) where
  (<.>) = Map.intersectionWith id
  (<. ) = Map.intersectionWith const
  ( .>) = Map.intersectionWith (const id)

-- | An IntMap is not 'Applicative', but it is an instance of 'Semiapplicative'
instance Semiapplicative IntMap where
  (<.>) = IntMap.intersectionWith id
  (<. ) = IntMap.intersectionWith const
  ( .>) = IntMap.intersectionWith (const id)

instance Semiapplicative Seq where
  (<.>) = ap

instance Semiapplicative Tree where
  (<.>) = (<*>)
  (<. ) = (<* )
  ( .>) = ( *>)
#endif

#ifdef MIN_VERSION_unordered_containers
-- | A 'HashMap' is not 'Applicative', but it is an instance of 'Semiapplicative'
instance (Hashable k, Eq k) => Semiapplicative (HashMap k) where
  (<.>) = HashMap.intersectionWith id
#endif

-- MaybeT is _not_ the same as Compose f Maybe
instance (Functor m, Monad m) => Semiapplicative (MaybeT m) where
  (<.>) = apDefault

-- ErrorT e is _not_ the same as Compose f (Either e)
instance (Functor m, Monad m) => Semiapplicative (ErrorT e m) where
  (<.>) = apDefault

instance (Functor m, Monad m) => Semiapplicative (ExceptT e m) where
  (<.>) = apDefault

instance Semiapplicative m => Semiapplicative (ReaderT e m) where
  ReaderT f <.> ReaderT a = ReaderT $ \e -> f e <.> a e

instance Semiapplicative m => Semiapplicative (ListT m) where
  ListT f <.> ListT a = ListT $ (<.>) <$> f <.> a

-- unfortunately, WriterT has its wrapped product in the wrong order to just use (<.>) instead of flap
instance (Semiapplicative m, Semigroup w) => Semiapplicative (Strict.WriterT w m) where
  Strict.WriterT f <.> Strict.WriterT a = Strict.WriterT $ flap <$> f <.> a where
    flap (x,m) (y,n) = (x y, m <> n)

instance (Semiapplicative m, Semigroup w) => Semiapplicative (Lazy.WriterT w m) where
  Lazy.WriterT f <.> Lazy.WriterT a = Lazy.WriterT $ flap <$> f <.> a where
    flap ~(x,m) ~(y,n) = (x y, m <> n)

instance Semimonad m => Semiapplicative (Strict.StateT s m) where
  (<.>) = apDefault

instance Semimonad m => Semiapplicative (Lazy.StateT s m) where
  (<.>) = apDefault

instance (Semimonad m, Semigroup w) => Semiapplicative (Strict.RWST r w s m) where
  (<.>) = apDefault

instance (Semimonad m, Semigroup w) => Semiapplicative (Lazy.RWST r w s m) where
  (<.>) = apDefault

instance Semiapplicative (ContT r m) where
  ContT f <.> ContT v = ContT $ \k -> f $ \g -> v (k . g)

#ifdef MIN_VERSION_comonad
instance (Semigroup e, Semiapplicative w) => Semiapplicative (EnvT e w) where
  EnvT ef wf <.> EnvT ea wa = EnvT (ef <> ea) (wf <.> wa)

instance (Semiapplicative w, Semigroup s) => Semiapplicative (StoreT s w) where
  StoreT ff m <.> StoreT fa n = StoreT ((<*>) <$> ff <.> fa) (m <> n)

instance Semiapplicative w => Semiapplicative (TracedT m w) where
  TracedT wf <.> TracedT wa = TracedT (ap <$> wf <.> wa)
#endif

-- | Wrap an 'Applicative' to be used as a member of 'Semiapplicative'
newtype WrappedApplicative f a = WrapApplicative { unwrapApplicative :: f a }

instance Functor f => Functor (WrappedApplicative f) where
  fmap f (WrapApplicative a) = WrapApplicative (f <$> a)

instance Applicative f => Semiapplicative (WrappedApplicative f) where
  WrapApplicative f <.> WrapApplicative a = WrapApplicative (f <*> a)
  WrapApplicative a <.  WrapApplicative b = WrapApplicative (a <*  b)
  WrapApplicative a  .> WrapApplicative b = WrapApplicative (a  *> b)

instance Applicative f => Applicative (WrappedApplicative f) where
  pure = WrapApplicative . pure
  WrapApplicative f <*> WrapApplicative a = WrapApplicative (f <*> a)
  WrapApplicative a <*  WrapApplicative b = WrapApplicative (a <*  b)
  WrapApplicative a  *> WrapApplicative b = WrapApplicative (a  *> b)

instance Alternative f => Alternative (WrappedApplicative f) where
  empty = WrapApplicative empty
  WrapApplicative a <|> WrapApplicative b = WrapApplicative (a <|> b)

-- | Transform a Semiapplicative into an Applicative by adding a unit.
newtype MaybeSemiapplicative f a = MaybeSemiapplicative { runMaybeSemiapplicative :: Either (f a) a }

instance Functor f => Functor (MaybeSemiapplicative f) where
  fmap f (MaybeSemiapplicative (Right a)) = MaybeSemiapplicative (Right (f     a ))
  fmap f (MaybeSemiapplicative (Left fa)) = MaybeSemiapplicative (Left  (f <$> fa))

instance Semiapplicative f => Semiapplicative (MaybeSemiapplicative f) where
  MaybeSemiapplicative (Right f) <.> MaybeSemiapplicative (Right a) = MaybeSemiapplicative (Right (f        a ))
  MaybeSemiapplicative (Right f) <.> MaybeSemiapplicative (Left fa) = MaybeSemiapplicative (Left  (f    <$> fa))
  MaybeSemiapplicative (Left ff) <.> MaybeSemiapplicative (Right a) = MaybeSemiapplicative (Left  (($a) <$> ff))
  MaybeSemiapplicative (Left ff) <.> MaybeSemiapplicative (Left fa) = MaybeSemiapplicative (Left  (ff   <.> fa))

  MaybeSemiapplicative a         <. MaybeSemiapplicative (Right _) = MaybeSemiapplicative a
  MaybeSemiapplicative (Right a) <. MaybeSemiapplicative (Left fb) = MaybeSemiapplicative (Left (a  <$ fb))
  MaybeSemiapplicative (Left fa) <. MaybeSemiapplicative (Left fb) = MaybeSemiapplicative (Left (fa <. fb))

  MaybeSemiapplicative (Right _) .> MaybeSemiapplicative b = MaybeSemiapplicative b
  MaybeSemiapplicative (Left fa) .> MaybeSemiapplicative (Right b) = MaybeSemiapplicative (Left (fa $> b ))
  MaybeSemiapplicative (Left fa) .> MaybeSemiapplicative (Left fb) = MaybeSemiapplicative (Left (fa .> fb))

instance Semiapplicative f => Applicative (MaybeSemiapplicative f) where
  pure a = MaybeSemiapplicative (Right a)
  (<*>) = (<.>)
  (<* ) = (<. )
  ( *>) = ( .>)

instance Extend f => Extend (MaybeSemiapplicative f) where
  duplicated w@(MaybeSemiapplicative Right{}) = MaybeSemiapplicative (Right w)
  duplicated (MaybeSemiapplicative (Left fa)) = MaybeSemiapplicative (Left (extended (MaybeSemiapplicative . Left) fa))

#ifdef MIN_VERSION_comonad
instance Comonad f => Comonad (MaybeSemiapplicative f) where
  duplicate w@(MaybeSemiapplicative Right{}) = MaybeSemiapplicative (Right w)
  duplicate (MaybeSemiapplicative (Left fa)) = MaybeSemiapplicative (Left (extend (MaybeSemiapplicative . Left) fa))
  extract (MaybeSemiapplicative (Left fa)) = extract fa
  extract (MaybeSemiapplicative (Right a)) = a

instance Semiapplicative (Cokleisli w a) where
  Cokleisli f <.> Cokleisli a = Cokleisli (\w -> (f w) (a w))
#endif

instance Semiapplicative Down where (<.>)=(<*>);(.>)=(*>);(<.)=(<*)

instance Semiapplicative Monoid.Sum where (<.>)=(<*>);(.>)=(*>);(<.)=(<*)
instance Semiapplicative Monoid.Product where (<.>)=(<*>);(.>)=(*>);(<.)=(<*)
instance Semiapplicative Monoid.Dual where (<.>)=(<*>);(.>)=(*>);(<.)=(<*)
instance Semiapplicative Monoid.First where (<.>)=(<*>);(.>)=(*>);(<.)=(<*)
instance Semiapplicative Monoid.Last where (<.>)=(<*>);(.>)=(*>);(<.)=(<*)
#if MIN_VERSION_base(4,8,0)
deriving instance Semiapplicative f => Semiapplicative (Monoid.Alt f)
#endif
-- in GHC 8.6 we'll have to deal with Semiapplicative f => Semiapplicative (Ap f) the same way
instance Semiapplicative Semigroup.First where (<.>)=(<*>);(.>)=(*>);(<.)=(<*)
instance Semiapplicative Semigroup.Last where (<.>)=(<*>);(.>)=(*>);(<.)=(<*)
instance Semiapplicative Semigroup.Min where (<.>)=(<*>);(.>)=(*>);(<.)=(<*)
instance Semiapplicative Semigroup.Max where (<.>)=(<*>);(.>)=(*>);(<.)=(<*)

instance (Semiapplicative f, Semiapplicative g) => Semiapplicative (f :*: g) where
  (a :*: b) <.> (c :*: d) = (a <.> c) :*: (b <.> d)

deriving instance Semiapplicative f => Semiapplicative (M1 i t f)
deriving instance Semiapplicative f => Semiapplicative (Rec1 f)

instance (Semiapplicative f, Semiapplicative g) => Semiapplicative (f :.: g) where
  Comp1 m <.> Comp1 n = Comp1 $ (<.>) <$> m <.> n

instance Semiapplicative U1 where (<.>)=(<*>);(.>)=(*>);(<.)=(<*)

instance Semigroup c => Semiapplicative (K1 i c) where
  K1 a <.> K1 b = K1 (a <> b)
  K1 a <.  K1 b = K1 (a <> b)
  K1 a  .> K1 b = K1 (a <> b)
instance Semiapplicative Par1 where (<.>)=(<*>);(.>)=(*>);(<.)=(<*)

instance Semiapplicative Generics.V1 where
#if __GLASGOW_HASKELL__ >= 708
  e <.> _ = case e of {}
#else
  e <.> _ = e `seq` undefined
#endif

-- | A 'Monad' sans 'return'.
--
-- Minimal definition: Either 'join' or '>>-'
--
-- If defining both, then the following laws (the default definitions) must hold:
--
-- > join = (>>- id)
-- > m >>- f = join (fmap f m)
--
-- Laws:
--
-- > induced definition of <.>: f <.> x = f >>- (<$> x)
--
-- Finally, there are two associativity conditions:
--
-- > associativity of (>>-):    (m >>- f) >>- g == m >>- (\x -> f x >>- g)
-- > associativity of join:     join . join = join . fmap join
--
-- These can both be seen as special cases of the constraint that
--
-- > associativity of (->-): (f ->- g) ->- h = f ->- (g ->- h)
--

class Semiapplicative m => Semimonad m where
  (>>-) :: m a -> (a -> m b) -> m b
  m >>- f = join (fmap f m)

  join :: m (m a) -> m a
  join = (>>- id)

#if __GLASGOW_HASKELL__ >= 708
  {-# MINIMAL (>>-) | join #-}
#endif

returning :: Functor f => f a -> (a -> b) -> f b
returning = flip fmap

apDefault :: Semimonad f => f (a -> b) -> f a -> f b
apDefault f x = f >>- \f' -> f' <$> x

instance Semigroup m => Semimonad ((,)m) where
  ~(m, a) >>- f = let (n, b) = f a in (m <> n, b)

#ifdef MIN_VERSION_tagged
instance Semimonad (Tagged a) where
  Tagged a >>- f = f a
  join (Tagged a) = a
#endif

#if defined(MIN_VERSION_tagged) || MIN_VERSION_base(4,7,0)
instance Semimonad Proxy where
  _ >>- _ = Proxy
  join _ = Proxy
#endif

instance Semimonad (Either a) where
  Left a  >>- _ = Left a
  Right a >>- f = f a

instance (Semimonad f, Semimonad g) => Semimonad (Functor.Product f g) where
  Functor.Pair m n >>- f = Functor.Pair (m >>- fstP . f) (n >>- sndP . f) where
    fstP (Functor.Pair a _) = a
    sndP (Functor.Pair _ b) = b

instance Semimonad ((->)m) where
  f >>- g = \e -> g (f e) e

instance Semimonad [] where
  (>>-) = (>>=)

instance Semimonad NonEmpty where
  (>>-) = (>>=)

instance Semimonad IO where
  (>>-) = (>>=)

instance Semimonad Maybe where
  (>>-) = (>>=)

instance Semimonad Option where
  (>>-) = (>>=)

instance Semimonad Identity where
  (>>-) = (>>=)

instance Semimonad Q where
  (>>-) = (>>=)

instance Semimonad m => Semimonad (IdentityT m) where
  IdentityT m >>- f = IdentityT (m >>- runIdentityT . f)

instance Monad m => Semimonad (WrappedMonad m) where
  WrapMonad m >>- f = WrapMonad $ m >>= unwrapMonad . f

instance (Functor m, Monad m) => Semimonad (MaybeT m) where
  (>>-) = (>>=) -- distributive law requires Monad to inject @Nothing@

instance (Semiapplicative m, Monad m) => Semimonad (ListT m) where
  (>>-) = (>>=) -- distributive law requires Monad to inject @[]@

instance (Functor m, Monad m) => Semimonad (ErrorT e m) where
  m >>- k = ErrorT $ do
    a <- runErrorT m
    case a of
      Left l -> return (Left l)
      Right r -> runErrorT (k r)

instance (Functor m, Monad m) => Semimonad (ExceptT e m) where
  m >>- k = ExceptT $ do
    a <- runExceptT m
    case a of
      Left l -> return (Left l)
      Right r -> runExceptT (k r)

instance Semimonad m => Semimonad (ReaderT e m) where
  ReaderT m >>- f = ReaderT $ \e -> m e >>- \x -> runReaderT (f x) e

instance (Semimonad m, Semigroup w) => Semimonad (Lazy.WriterT w m) where
  m >>- k = Lazy.WriterT $
    Lazy.runWriterT m >>- \ ~(a, w) ->
    Lazy.runWriterT (k a) `returning` \ ~(b, w') ->
      (b, w <> w')

instance (Semimonad m, Semigroup w) => Semimonad (Strict.WriterT w m) where
  m >>- k = Strict.WriterT $
    Strict.runWriterT m >>- \ (a, w) ->
    Strict.runWriterT (k a) `returning` \ (b, w') ->
      (b, w <> w')

instance Semimonad m => Semimonad (Lazy.StateT s m) where
  m >>- k = Lazy.StateT $ \s ->
    Lazy.runStateT m s >>- \ ~(a, s') ->
    Lazy.runStateT (k a) s'

instance Semimonad m => Semimonad (Strict.StateT s m) where
  m >>- k = Strict.StateT $ \s ->
    Strict.runStateT m s >>- \ ~(a, s') ->
    Strict.runStateT (k a) s'

instance (Semimonad m, Semigroup w) => Semimonad (Lazy.RWST r w s m) where
  m >>- k = Lazy.RWST $ \r s ->
    Lazy.runRWST m r s >>- \ ~(a, s', w) ->
    Lazy.runRWST (k a) r s' `returning` \ ~(b, s'', w') ->
      (b, s'', w <> w')

instance (Semimonad m, Semigroup w) => Semimonad (Strict.RWST r w s m) where
  m >>- k = Strict.RWST $ \r s ->
    Strict.runRWST m r s >>- \ (a, s', w) ->
    Strict.runRWST (k a) r s' `returning` \ (b, s'', w') ->
      (b, s'', w <> w')

instance Semimonad (ContT r m) where
  m >>- k = ContT $ \c -> runContT m $ \a -> runContT (k a) c

{-
instance ArrowSemiapplicative a => Semimonad (WrappedArrow a b) where
  (>>-) = (>>=)
-}

#if MIN_VERSION_base(4,4,0)
instance Semimonad Complex where
  (a :+ b) >>- f = a' :+ b' where
    a' :+ _  = f a
    _  :+ b' = f b
  {-# INLINE (>>-) #-}
#endif

#ifdef MIN_VERSION_containers
-- | A 'Map' is not a 'Monad', but it is an instance of 'Semimonad'
instance Ord k => Semimonad (Map k) where
  m >>- f = Map.mapMaybeWithKey (\k -> Map.lookup k . f) m

-- | An 'IntMap' is not a 'Monad', but it is an instance of 'Semimonad'
instance Semimonad IntMap where
  m >>- f = IntMap.mapMaybeWithKey (\k -> IntMap.lookup k . f) m

instance Semimonad Seq where
  (>>-) = (>>=)

instance Semimonad Tree where
  (>>-) = (>>=)
#endif

#ifdef MIN_VERSION_unordered_containers
-- | A 'HashMap' is not a 'Monad', but it is an instance of 'Semimonad'
instance (Hashable k, Eq k) => Semimonad (HashMap k) where
  -- this is needlessly painful
  m >>- f = HashMap.fromList $ do
    (k, a) <- HashMap.toList m
    case HashMap.lookup k (f a) of
      Just b -> [(k,b)]
      Nothing -> []
#endif

instance Semimonad Down where Down a >>- f = f a

instance Semimonad Monoid.Sum where (>>-) = (>>=)
instance Semimonad Monoid.Product where (>>-) = (>>=)
instance Semimonad Monoid.Dual where (>>-) = (>>=)
instance Semimonad Monoid.First where (>>-) = (>>=)
instance Semimonad Monoid.Last where (>>-) = (>>=)
#if MIN_VERSION_base(4,8,0)
instance Semimonad f => Semimonad (Monoid.Alt f) where
  Alt m >>- k = Alt (m >>- getAlt . k)
#endif
-- in GHC 8.6 we'll have to deal with Semimonad f => Semimonad (Ap f) the same way
instance Semimonad Semigroup.First where (>>-) = (>>=)
instance Semimonad Semigroup.Last where (>>-) = (>>=)
instance Semimonad Semigroup.Min where (>>-) = (>>=)
instance Semimonad Semigroup.Max where (>>-) = (>>=)
instance Semimonad Generics.V1 where
#if __GLASGOW_HASKELL__ >= 708
  m >>- _ = case m of {}
#else
  m >>- _ = m `seq` undefined
#endif

infixl 4 <<.>>, <<., .>>

class Bifunctor p => Biapply p where
  (<<.>>) :: p (a -> b) (c -> d) -> p a c -> p b d

  -- |
  -- @
  -- a '.>' b ≡ 'const' 'id' '<$>' a '<.>' b
  -- @
  (.>>) :: p a b -> p c d -> p c d
  a .>> b = bimap (const id) (const id) <<$>> a <<.>> b
  {-# INLINE (.>>) #-}

  -- |
  -- @
  -- a '<.' b ≡ 'const' '<$>' a '<.>' b
  -- @
  (<<.) :: p a b -> p c d -> p a b
  a <<. b = bimap const const <<$>> a <<.>> b
  {-# INLINE (<<.) #-}

instance Biapply (,) where
  (f, g) <<.>> (a, b) = (f a, g b)
  {-# INLINE (<<.>>) #-}

#if MIN_VERSION_semigroups(0,16,2)
instance Biapply Arg where
  Arg f g <<.>> Arg a b = Arg (f a) (g b)
  {-# INLINE (<<.>>) #-}
#endif

instance Semigroup x => Biapply ((,,) x) where
  (x, f, g) <<.>> (x', a, b) = (x <> x', f a, g b)
  {-# INLINE (<<.>>) #-}

instance (Semigroup x, Semigroup y) => Biapply ((,,,) x y) where
  (x, y, f, g) <<.>> (x', y', a, b) = (x <> x', y <> y', f a, g b)
  {-# INLINE (<<.>>) #-}

instance (Semigroup x, Semigroup y, Semigroup z) => Biapply ((,,,,) x y z) where
  (x, y, z, f, g) <<.>> (x', y', z', a, b) = (x <> x', y <> y', z <> z', f a, g b)
  {-# INLINE (<<.>>) #-}

instance Biapply Const where
  Const f <<.>> Const x = Const (f x)
  {-# INLINE (<<.>>) #-}

#ifdef MIN_VERSION_tagged
instance Biapply Tagged where
  Tagged f <<.>> Tagged x = Tagged (f x)
  {-# INLINE (<<.>>) #-}
#endif

instance (Biapply p, Semiapplicative f, Semiapplicative g) => Biapply (Biff p f g) where
  Biff fg <<.>> Biff xy = Biff (bimap (<.>) (<.>) fg <<.>> xy)
  {-# INLINE (<<.>>) #-}

instance Semiapplicative f => Biapply (Clown f) where
  Clown fg <<.>> Clown xy = Clown (fg <.> xy)
  {-# INLINE (<<.>>) #-}

instance Biapply p => Biapply (Flip p) where
  Flip fg <<.>> Flip xy = Flip (fg <<.>> xy)
  {-# INLINE (<<.>>) #-}

instance Semiapplicative g => Biapply (Joker g) where
  Joker fg <<.>> Joker xy = Joker (fg <.> xy)
  {-# INLINE (<<.>>) #-}

-- orphan mess
instance Biapply p => Semiapplicative (Join p) where
  Join f <.> Join a = Join (f <<.>> a)
  {-# INLINE (<.>) #-}
  Join a .> Join b = Join (a .>> b)
  {-# INLINE (.>) #-}
  Join a <. Join b = Join (a <<. b)
  {-# INLINE (<.) #-}

instance (Biapply p, Biapply q) => Biapply (Bifunctor.Product p q) where
  Bifunctor.Pair w x <<.>> Bifunctor.Pair y z = Bifunctor.Pair (w <<.>> y) (x <<.>> z)
  {-# INLINE (<<.>>) #-}

instance (Semiapplicative f, Biapply p) => Biapply (Tannen f p) where
  Tannen fg <<.>> Tannen xy = Tannen ((<<.>>) <$> fg <.> xy)
  {-# INLINE (<<.>>) #-}

instance Biapply p => Biapply (WrappedBifunctor p) where
  WrapBifunctor fg <<.>> WrapBifunctor xy = WrapBifunctor (fg <<.>> xy)
  {-# INLINE (<<.>>) #-}
