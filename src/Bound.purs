module Bound (
    class Bound, subst, flipSubst, (=<<<), (>>>=), substDefault,
    Var(..),
    Scope(..), unScope,
    fromScope, toScope,
    abstract, abstract1,
    instantiate, instantiate1
    ) where

import Control.Monad.Trans.Class (class MonadTrans, lift)
import Control.Monad.Cont (ContT)
import Control.Monad.Except (ExceptT)
import Control.Monad.List.Trans (ListT)
import Control.Monad.Maybe.Trans (MaybeT)
import Control.Monad.RWS (RWST)
import Control.Monad.Reader (ReaderT)
import Control.Monad.State (StateT)
import Control.Monad.Writer (WriterT)
import Data.Bifunctor (class Bifunctor)
import Data.Bifoldable (class Bifoldable, bifoldrDefault, bifoldlDefault)
import Data.Bitraversable (class Bitraversable, bisequenceDefault)
import Data.Foldable (class Foldable, foldrDefault, foldlDefault)
import Data.Generic (class Generic, gShow)
import Data.Traversable (class Traversable, sequenceDefault)
import Data.Maybe (Maybe(..))
import Data.Monoid (class Monoid, mempty)
import Prelude


class Bound t where
    subst :: forall f a c. Monad f => (a -> f c) -> t f a -> t f c

substDefault :: forall t f a c. (MonadTrans t, Monad f, Monad (t f)) => (a -> f c) -> t f a -> t f c
substDefault f m = m >>= (f >>> lift)

flipSubst :: forall f t a c. (Bound t, Monad f) => t f a -> (a -> f c) -> t f c
flipSubst = flip subst

infixl 1 subst as =<<<
infixr 1 flipSubst as >>>=


instance boundContT :: Bound (ContT r) where
    subst = substDefault
instance boundExceptT :: Bound (ExceptT e) where
    subst = substDefault
instance boundListT :: Bound ListT where
    subst = substDefault
instance boundMaybeT :: Bound MaybeT where
    subst = substDefault
instance boundRWST :: Monoid w => Bound (RWST r w s) where
    subst = substDefault
instance boundReaderT :: Bound (ReaderT r) where
    subst = substDefault
instance boundStateT :: Bound (StateT s) where
    subst = substDefault
instance boundWriterT :: Monoid w => Bound (WriterT w) where
    subst = substDefault


data Var b a = B b | F a

derive instance genericVar :: (Generic b, Generic a) => Generic (Var b a)
derive instance eqVar :: (Eq b, Eq a) => Eq (Var b a)
derive instance ordVar :: (Ord b, Ord a) => Ord (Var b a)
instance showVar :: (Generic b, Generic a) => Show (Var b a) where
    show = gShow

instance functorVar :: Functor (Var b) where
    map = liftA1
instance applyVar :: Apply (Var b) where
    apply = ap
instance applicativeVar :: Applicative (Var b) where
    pure = F
instance bindVar :: Bind (Var b) where
    bind (B x) f = B x
    bind (F y) f = f y
instance monadVar :: Monad (Var b)

instance foldableVar :: Foldable (Var b) where
    foldMap f (B x) = mempty
    foldMap f (F y) = f y
    foldr f = foldrDefault f
    foldl f = foldlDefault f
instance traversableVar :: Traversable (Var b) where
    traverse f (B x) = pure (B x)
    traverse f (F y) = F <$> f y
    sequence x = sequenceDefault x

instance bifunctorVar :: Bifunctor Var where
    bimap f g (B x) = B (f x)
    bimap f g (F y) = F (g y)
instance bifoldableVar :: Bifoldable Var where
    bifoldMap f g (B x) = f x
    bifoldMap f g (F y) = g y
    bifoldr f = bifoldrDefault f
    bifoldl f = bifoldlDefault f
instance bitraversableVar :: Bitraversable Var where
    bitraverse f g (B x) = B <$> f x
    bitraverse f g (F y) = F <$> g y
    bisequence x = bisequenceDefault x


newtype Scope b f a = Scope (f (Var b (f a)))
unScope :: forall b f a. Scope b f a -> f (Var b (f a))
unScope (Scope x) = x

fromScope :: forall b f a. Monad f => Scope b f a -> f (Var b a)
fromScope scope = do
    var <- unScope scope
    case var of
        F expr -> map F expr
        B b -> pure (B b)

toScope :: forall b f a. Monad f => f (Var b a) -> Scope b f a
toScope = Scope <<< map (map pure)

derive instance genericScope :: (Generic b, Generic (f (Var b (f a))), Generic a) => Generic (Scope b f a)
derive instance eqScope :: (Eq b, Eq (f (Var b (f a))), Eq a) => Eq (Scope b f a)
derive instance ordScope :: (Ord b, Ord (f (Var b (f a))), Ord a) => Ord (Scope b f a)
instance showScope :: (Generic b, Generic (f (Var b (f a))), Generic a) => Show (Scope b f a) where
    show = gShow

instance functorScope :: Functor f => Functor (Scope b f) where
    map f = Scope <<< map (map (map f)) <<< unScope
instance applyScope :: Monad f => Apply (Scope b f) where
    apply = ap
instance applicativeScope :: Monad f => Applicative (Scope b f) where
    pure = Scope <<< pure <<< pure <<< pure
instance bindScope :: Monad f => Bind (Scope b f) where
    bind (Scope expr) f = Scope $ do
        var <- expr
        case var of
             B b -> pure (B b)
             F fx -> fx >>= (f >>> unScope)
instance monadScope :: Monad f => Monad (Scope b f)

instance monadTransScope :: MonadTrans (Scope b) where
    lift m = Scope (pure (F m))
instance boundScope :: Bound (Scope b) where
    subst = substDefault


abstract :: forall a b f. Monad f => (a -> Maybe b) -> f a -> Scope b f a
abstract f = Scope <<< map g
    where g var = case f var of
            Nothing -> F (pure var)
            Just b -> B b
abstract1 :: forall a f. (Eq a, Monad f) => a -> f a -> Scope Unit f a
abstract1 x = abstract (\y -> if x == y then Just unit else Nothing)


instantiate :: forall a b f. Monad f => (b -> f a) -> Scope b f a -> f a
instantiate f scope = do
    var <- unScope scope
    case var of
        B b -> f b
        F a -> a
instantiate1 :: forall a b f. Monad f => f a -> Scope b f a -> f a
instantiate1 expr = instantiate (const expr)


