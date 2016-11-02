-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Juan Carlos Saenz-Carrasco jcsaenzcarrasco@gmail.com
-- Paolo Veronelli            paolo.veronelli@gmail.com
-- September 2016
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

{-# language DataKinds#-}
{-# language GADTs#-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language FunctionalDependencies#-}
{-# language MultiParamTypeClasses#-}
{-# language TypeFamilies#-}
{-# language TypeSynonymInstances #-}
{-# language UndecidableInstances #-}
{-# language ViewPatterns#-}

module ForestX where

import Control.Applicative  ((<|>))
import Control.Arrow (second)
import Control.Monad (guard)
import Control.Monad.State (gets,put, MonadState)
import Control.Monad.State (Monad, MonadState, runState, State, evalState )
import Data.FingerTree (FingerTree, Measured (measure), (<|), fromList, empty, (><))
import Data.Foldable (toList)
import Data.Monoid (Sum (..))
import Data.Set (Set,member)
import Data.Tree (Tree)
import Data.Types.Isomorphic (Iso, Injective (to))

import CoreX

-- | modification tagger
data Modify (a :: Modification) 
-- | query tagger
data Query (a :: Queries)

-- | modification types
data Modification = LinkT | CutT

-- | query types
data Queries = PathT | SpanningT

-- | generic query language for algorithms
data Lang a b r where
    -- | link two vertices
    Link :: a -> a -> Lang a (Modify LinkT) ()
    -- | remove the link between two vertices
    Cut :: a -> a -> Lang a (Modify CutT) ()
    -- | compute the path between two vertices 
    Path :: a -> a -> Lang a (Query PathT) [a]
    -- | compute the spanning tree from a vertex
    Spanning :: a -> Lang a (Query SpanningT) (Tree a)

-- | possible exception condition for Lang interpreters
data Exception a b where
    -- | two vertices are part of the same graph, loop avoiding exception
    AlreadyConnectedVertices :: a -> a -> Exception a (Modify LinkT)
    -- | unlink two not linked vertices
    AlreadySeparatedVertices :: a -> a -> Exception a (Modify CutT)
    -- | a vertex was not found
    VertexNotFound :: a -> Exception a b 
    -- | vertices not connected
    NotConnectedVertices :: a -> a -> Exception a (Query PathT)
    -- | alternative exception conditions hold
    OrException :: Exception a b  -> Exception a b -> Exception a b

-- | query interpreter for algorithms
class Interpreter t a where
    -- | answer queries modifying the structure in the state 
    modify  :: (Monad m, MonadState (t a) m)  
            => Lang a (Modify c) ()  
            -> m (Either (Exception a (Modify c)) ()) 
    -- | queries are pure functions from state
    query   :: Lang a (Query c) r  
            -> t a          
            -> Either (Exception a (Query c)) r 

-- | A forest of Tours
newtype TourForest a = TourForest (FingerTree (Set a) (Tour a)) deriving Show

link :: Ord a => a -> a -> TourForest a 
    -> Either (Exception a (Modify LinkT))  (TourForest a)
link x y (TourForest h) = case select (member x) h of
        Nothing -> Left $ VertexNotFound x
        Just (ex,h') -> case member y $ measure ex of
            True -> Left $ AlreadyConnectedVertices x y
            False -> case  select (member y) h' of
                Nothing -> Left $ VertexNotFound y
                Just (ey,h'') -> Right . TourForest $
                        (splice (reroot x ex) y ey) <| h''

cut :: Ord a => a -> a -> TourForest a 
    -> Either (Exception a (Modify CutT)) (TourForest a)
cut x y (TourForest h) = case select (member y) h of
        Nothing -> Left $ VertexNotFound y
        Just (e,h') -> case (do
                guard $ x `member` measure e 
                let e' = reroot y e
                father x e' >>= guard . (== y)
                return e') of
                    Nothing -> Left $  OrException (AlreadySeparatedVertices x y) 
                        (VertexNotFound x)
                    Just e -> let (e1,e2) = extract x e in 
                        TourForest <$> (Right $ e1 <| e2 <| h')

fpath :: Ord a => a -> a -> TourForest a -> Either (Exception a (Query PathT)) [a]
fpath x y (TourForest h) = case select (member y) h of
        Nothing -> Left $ VertexNotFound y
        Just (e,_) -> case member x $ measure e of
            False -> Left $ OrException (NotConnectedVertices x y) (VertexNotFound x)
            True -> Right (path x y e)
