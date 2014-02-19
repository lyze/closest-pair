-- CIS 399, Homework #1
-- David Xu

{-# OPTIONS -Wall -fwarn-tabs -fno-warn-type-defaults -fno-warn-orphans #-}
{-# LANGUAGE TemplateHaskell, FlexibleInstances, ScopedTypeVariables #-}

module Main where

import Data.List hiding (insert)
import qualified Data.HashTable.ST.Basic as C
import qualified Data.HashTable.Class as H
import Control.Monad.ST

import System.Random
import qualified System.Random.Shuffle

import Test.QuickCheck
import Test.QuickCheck.All

--------------------------------------------------------------------------------
-- Test driver
main :: IO (Bool)
main = $quickCheckAll



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

--------------------------------------------------------------------------------
-- Property tests

-- prototype
f_closest      :: ([Point] -> (Point, Point)) -> [Point] -> Property
f_closest f ps = length ps > 1 ==> dist' (f ps) == dist' (closestPairBruteForce ps)

prop_divideAndConquer :: [Point] -> Property
prop_divideAndConquer = f_closest closestPairDivideAndConquer

prop_hashing   :: Int -> [Point] -> Property
prop_hashing s = f_closest $ closestPairHashing $ mkStdGen s


--------------------------------------------------------------------------------
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

type SubsquareId = Int

type HashTable s k v = C.HashTable s k v

type Dictionary s = HashTable s SubsquareId Point

makeDictionary n = H.newSized n

getBoundingSquareN        :: [Point] -> ((Point, Point), Int)
getBoundingSquareN []     = error "getMinMaxN: empty list"
getBoundingSquareN (p:ps) = (squareify rect, n)
  where (rect, n) = foldr f ((p, p), 1) ps

        f (x, y) (((llx, lly), (urx, ury)), count) =
          let ul = (min llx x, min lly y) in
          let ur = (max urx x, max ury y) in
          ((ul, ur), count + 1)

        squareify (ll@(llx, lly), (urx, ury)) =
          let s = max (urx - llx) (ury - lly) in
          (ll, (s + llx, s + lly))

closestPairHashing                      :: (RandomGen g) => g -> [Point] ->
                                           (Point, Point)
closestPairHashing _   []               =
  error "closestPairHashing: empty list"

closestPairHashing _   [_]              =
  error "closestPairHashing: singleton list"

closestPairHashing gen points@(p1:p2:_) =
  let d0               = dist p1 p2 in
  let ((ul, ur), size) = getBoundingSquareN points in
  runST $ do
    (dict::Dictionary s) <- H.newSized size
    closestPairHashing' size (d0) (p1, p2) (dict) [] (shuffle gen points)
      where closestPairHashing' _ _ best          _    _    []     = return best
            closestPairHashing' n d best@(z1, z2) dict seen (p:ps) =
              case find (\q -> dist p q < d) seen of
                Just s ->
                  let d' = dist p s in
                  do
                    dict' <- H.fromListWithSizeHint n (map (\q -> (getSubsquare q, q)) $ p : seen)
                    closestPairHashing' n d' (p, s) dict' (p : seen) ps
                      where neighbors       = lookup' $ closeSubsquares p
                            closeSubsquares = undefined
                            lookup'         = undefined
                            insertList      = undefined
                Nothing ->
                  do H.insert dict (getSubsquare p) p
                     closestPairHashing' n d best (dict) (p : seen) ps

            getSubsquare p = undefined
