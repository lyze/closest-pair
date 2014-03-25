-- CIS 399, Homework #1
-- David Xu
--
-- A comparison of two closest-pair algorithms: The divide-and-conquer approach
-- has a runtime that is O(n log n). The dictionary-based algorithm has a time
-- complexity of O(n).

{-# OPTIONS -Wall -fwarn-tabs -fno-warn-type-defaults -fno-warn-orphans #-}
{-# LANGUAGE TemplateHaskell, FlexibleInstances, ScopedTypeVariables #-}

module Main where

import Data.List
import Data.Maybe

import qualified Data.HashTable.ST.Basic as C
import qualified Data.HashTable.Class as H
import Control.Monad.ST

import System.Random
import qualified System.Random.Shuffle

import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.All

import Criterion.Main

-------------------------------------------------------------------------------
-- Test driver
main :: IO ()
main = defaultMain
       [ bgroup "divide and conquer"
         [ bench "n = 10" $ nf closestPairDivideAndConquer (pointsGen' 10)
         , bench "n = 100" $ nf closestPairDivideAndConquer (pointsGen' 100)
         , bench "n = 1000" $ nf closestPairDivideAndConquer (pointsGen' 1000)
         , bench "n = 10000" $ nf closestPairDivideAndConquer (pointsGen' 10000)
         , bench "n = 100000" $ nf closestPairDivideAndConquer (pointsGen' 100000)
         -- , bench "1000000" $ nf closestPairDivideAndConquer (pointsGen' 1000000)
         ]
       ,
         bgroup "hashing"
         [ bench "n = 10" $ nf closestPairHashing' (pointsGen' 10)
         , bench "n = 100" $ nf closestPairHashing' (pointsGen' 100)
         , bench "n = 1000" $ nf closestPairHashing' (pointsGen' 1000)
         , bench "n = 10000" $ nf closestPairHashing' (pointsGen' 10000)
         , bench "n = 100000" $ nf closestPairHashing' (pointsGen' 100000)
         , bench "n = 1000000" $ nf closestPairHashing' (pointsGen' 1000000)
         ] ]
  where pointsGen' n = take n $ pointsGen 0
        gen = mkStdGen 0
        closestPairHashing' = closestPairHashing gen



pointsGen        :: Int -> [Point]
pointsGen seed = unGen arbitrary (mkStdGen seed) 99999999

-- getRandomArg           :: Gen a -> IO [a]
-- getRandomArg (MkGen m) =
--   do rnd <- newStdGen
--      let rnds rnd = rnd1 : rnds rnd2 where (rnd1, rnd2) = split rnd
--      return [(m r n) | (r,n) <- rnds rnd `zip` [0,2..20] ]


test :: IO (Bool)
test = $quickCheckAll

-------------------------------------------------------------------------------

type Point = (Double, Double)
type Distance = Double

-- Helper functions

dist                   :: Point -> Point -> Distance
dist (x1, y1) (x2, y2) = sqrt $ (x1 - x2)^2 + (y1 - y2)^2

dist' :: (Point, Point) -> Distance
dist' (p1, p2) = dist p1 p2

pointPairEq                   :: (Point, Point) -> (Point, Point) -> Bool
pointPairEq (p1, p2) (q1, q2) = p1 == q1 && p2 == q2 ||
                                p1 == q2 && p2 == q1
pairs        :: [a] -> [(a, a)]
pairs []     = []
pairs [_]    = []
pairs (z:zs) = [(x, y) | let x = z, y <- zs] ++ pairs zs


shuffle      :: RandomGen g => g -> [Point] -> [Point]
shuffle g xs = System.Random.Shuffle.shuffle' xs (length xs) g

-- Brute force reference implementation
closestPairBruteForce    :: [Point] -> (Point, Point)
closestPairBruteForce ps = minimumBy ord (pairs ps)
  where ord (p1, p2) (p3, p4)
          | dist p1 p2 < dist p3 p4  = LT
          | dist p1 p2 == dist p3 p4 = EQ
          | otherwise                = GT

-------------------------------------------------------------------------------
-- Property tests

-- prototype
f_closest      :: ([Point] -> (Point, Point)) -> [Point] -> Property
f_closest f ps = length ps > 1 ==> dist' (f ps) == dist' (closestPairBruteForce ps)

prop_divideAndConquer :: [Point] -> Property
prop_divideAndConquer = f_closest closestPairDivideAndConquer

prop_hashing   :: Int -> [Point] -> Property
prop_hashing s = (f_closest . closestPairHashing) $ mkStdGen s


-------------------------------------------------------------------------------
-- Problem 1 (a)

closestPairDivideAndConquer     :: [Point] -> (Point, Point)
closestPairDivideAndConquer []  = error "closestPairDivideAndConquer: empty list"
closestPairDivideAndConquer [_] = error "closestPairDivideAndConquer: singleton list"
closestPairDivideAndConquer ps
  | len <= 3    = closestPairBruteForce ps
  | otherwise = closestPairRec (sortByX ps) (sortByY ps) len
  where len = length ps
        sortByX = sortBy xOrd
        sortByY = sortBy yOrd
        xOrd (x1, _) (x2, _)
          | x1 < x2   = LT
          | x1 == x2  = EQ
          | otherwise = GT
        yOrd (_, y1) (_, y2)
          | y1 < y2   = LT
          | y1 == y2  = EQ
          | otherwise = GT

        closestPairRec pxs pys n
          | n <= 3 = closestPairBruteForce pxs
          | otherwise = select $ minZ sy
          where select Nothing
                  | dist q0 q1 < dist r0 r1 = (q0, q1)
                  | otherwise               = (r0, r1)
                select (Just (s, s'))
                  | dist s s' < d           = (s, s')
                  | dist q0 q1 < dist r0 r1 = (q0, q1)
                  | otherwise               = (r0, r1)
                nq         = ceiling (fromIntegral n / 2)
                nr         = n - nq
                divide     = splitAt nq
                (qxs, rxs) = divide pxs
                (x', _)    = last qxs -- max x-coordinate of point in Q
                (qys, rys) = partition (\(x, _) -> x <= x') pys
                (q0, q1)   = closestPairRec qxs qys nq
                (r0, r1)   = closestPairRec rxs rys nr
                d          = min (dist q0 q1) (dist r0 r1)
                sy         = filter (\(x, _) -> x' - x <= d) $ pys

                minZ        :: [Point] -> Maybe (Point, Point)
                minZ []     = Nothing
                minZ [_]    = Nothing
                minZ (s:ss) =
                  let s' = minimumBy ord $ take 15 ss in
                  case minZ ss of
                    Nothing      -> Just (s, s')
                    Just (t, t') -> if dist s s' <= dist t t'
                                    then Just (s, s')
                                    else Just (t, t')
                    where ord s1 s2
                           | dist s s1 < dist s s2  = LT
                           | dist s s1 == dist s s2 = EQ
                           | otherwise              = GT


--------------------------------------------------------------------------------
-- Problem 1 (b)
type SubsquareId = (Int, Int)

type HashTable s k v = C.HashTable s k v

type Dictionary s = HashTable s SubsquareId Point

makeDictionary :: H.HashTable h => Int -> ST s (h s k v)
makeDictionary = H.newSized

insertDict :: Dictionary s -> SubsquareId -> Point -> ST s ()
insertDict = H.insert

makeDictionaryFromList :: Int -> [(SubsquareId, Point)] -> ST s (Dictionary s)
makeDictionaryFromList = H.fromListWithSizeHint

sideLength                          :: (Point, Point) -> Double
sideLength ((llx, _), (urx, _)) = abs $ urx - llx

getSubsquare                                   :: (Point, Point) -> Double -> Point -> SubsquareId
getSubsquare ((llx, lly), (_, _)) d (x, y) =
  let s  = d / 2
      x' = (x - llx)
      y' = (y - lly)
  in  (floor $ x' / s, floor $ y' / s)

closeSubsquares        :: (Point, Point) -> Double -> Point -> [SubsquareId]
closeSubsquares sq d p = let (x, y) = getSubsquare sq d p
                             n = ceiling $ (sideLength sq) * 2 / d
                         in  [ (x', y') |
                               let ds = [-2..2],
                               dx <- ds, dy <- ds,
                               let x' = x + dx, let y' = y + dy,
                               x' >= 0, x' < n, y' >= 0, y' < n ]

neighbors             :: Dictionary s -> (Point, Point) -> Double -> Point -> ST s [Point]
neighbors dict sq d p = do l <- mapM (H.lookup dict) $ closeSubsquares sq d p
                           return $ catMaybes l

findCloser     :: Double -> Point -> [Point] -> Maybe (Point, Double)
findCloser d0 p0 = foldr f Nothing
  where f p z@(Just (_, e))
          | d < e    = Just (p, d)
          | otherwise = z
          where d = dist p p0

        f p Nothing
          | d < d0    = Just (p, d)
          | otherwise = Nothing
          where d = dist p0 p


getBoundingSquareN        :: [Point] -> ((Point, Point), Int)
getBoundingSquareN []     = error "getMinMaxN: empty list"
getBoundingSquareN (p:ps) = (squareify rect, n)
  where (rect, n) = foldr f ((p, p), 1) ps

        f (x, y) (((llx, lly), (urx, ury)), count) =
          let ul = (min llx x, min lly y)
              ur = (max urx x, max ury y)
          in  ((ul, ur), count + 1)

        squareify (ll@(llx, lly), (urx, ury)) =
          let s = max (urx - llx) (ury - lly)
          in  (ll, (s + llx, s + lly))

closestPairHashing                      :: (RandomGen g) => g -> [Point] ->
                                           (Point, Point)
closestPairHashing _   []               =
  error "closestPairHashing: empty list"

closestPairHashing _   [_]              =
  error "closestPairHashing: singleton list"

closestPairHashing gen points@(_:_:_) =
  let shuffled@(p1:p2:_) = shuffle gen points
      d0                 = dist p1 p2
      (box, num)         = getBoundingSquareN points
  in  runST $ do
    dict <- makeDictionary num
    closestPairHashing' box num (d0) (p1, p2) (dict) [] shuffled

      where closestPairHashing' _  _ _ best _    _    []     = return best
            closestPairHashing' sq n d best dict seen (p:ps) =
              do closePoints <- neighbors dict sq d p
                 case findCloser d p closePoints of
                   Just (s, d') ->
                     let updated = map (\q -> (getSubsquare sq d' q, q)) $ p : seen in
                     do
                       dict' <- makeDictionaryFromList n updated
                       closestPairHashing' sq n d' (p, s) dict' (p : seen) ps
                   Nothing ->
                     do
                       insertDict dict (getSubsquare sq d p) p
                       closestPairHashing' sq n d best (dict) (p : seen) ps
