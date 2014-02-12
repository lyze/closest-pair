-- CIS 399, Homework #1
-- David Xu

{-# OPTIONS -Wall -fwarn-tabs -fno-warn-type-defaults -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances, ScopedTypeVariables #-}

module Main where

import Data.List

import Debug.Trace

import Test.QuickCheck

main :: IO ()
main = quickCheck $ prop_f_closest closestPairDivideAndConquer

type Point = (Double, Double)

pairs        :: [a] -> [(a, a)]
pairs []     = []
pairs [_]    = []
pairs (z:zs) = [(x, y) | let x = z, y <- zs] ++ pairs zs

sliding            :: Int -> [a] -> [[a]]
sliding n l@(_:xs) = take n l : sliding n xs
sliding _ []       = []

dist                   :: Point -> Point -> Double
dist (x1, y1) (x2, y2) = sqrt $ (x1 - x2)^2 + (y1 - y2)^2

dist' :: (Point, Point) -> Double
dist' (p1, p2) = dist p1 p2

distPairOrd                              :: (Point, Point) -> (Point, Point) -> Ordering
distPairOrd (p1, p2) (p3, p4)
          | dist p1 p2 < dist p3 p4  = LT
          | dist p1 p2 == dist p3 p4 = EQ
          | otherwise                = GT

pointPairEq                   :: (Point, Point) -> (Point, Point) -> Bool
pointPairEq (p1, p2) (q1, q2) = p1 == q1 && p2 == q2 ||
                                p1 == q2 && p2 == q1

closestPairBruteForce    :: [Point] -> (Point, Point)
closestPairBruteForce ps = minimumBy distPairOrd (pairs ps)

prop_f_closest      :: ([Point] -> (Point, Point)) -> [Point] -> Gen Prop
prop_f_closest f ps = length ps > 1 ==> dist' (f ps) == dist' (closestPairBruteForce ps)


closestPairDivideAndConquer     :: [Point] -> (Point, Point)
closestPairDivideAndConquer []  = error "closestPairDivideAndConquer: empty list"
closestPairDivideAndConquer [_] = error "closestPairDivideAndConquer: singleton list"
closestPairDivideAndConquer ps  =
  closestPairRec (sortByX ps) (sortByY ps) (length ps)
    where sortByX = sortBy xOrd
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
            | n <= 3 = minimumBy distPairOrd $ pairs pxs
            | otherwise = select $ trace ("minZ sy = " ++ (show $ minZ sy) ++ "\nq0, q1 = " ++ (show $ (q0, q1)) ++ "\nr0, r1 = " ++ (show $ (r0, r1))) $ minZ $ trace ("sy = " ++ show sy) sy
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
                    (qxs, rxs) = divide $ trace ("n = " ++ show n ++ "\npxs = " ++ show pxs) pxs
                    (x', _)    = last qxs -- max x-coordinate of point in Q
                    (qys, rys) = partition (\(x, _) -> x <= x') pys
                    (q0, q1)   = closestPairRec qxs qys nq
                    (r0, r1)   = closestPairRec rxs rys nr
                    d          = min (dist q0 q1) (dist r0 r1)

                    sy         = trace ("x' = " ++ show x') $ filter (\(x, _) -> x' - x <= d) $ trace ("pys = " ++ show pys) pys
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
