{-# LANGUAGE QuasiQuotes, ViewPatterns #-}

module Main where

import qualified Ferry as Q
import Ferry (Q,toQ,fromQ,qc,view)

import Database.HDBC.Sqlite3

employees :: Q [([Char], [Char], Int)]
employees = toQ [
    ("Simon",  "MS",   80)
  , ("Erik",   "MS",   90)
  , ("Phil",   "Ed",   40)
  , ("Gordon", "Ed",   45)
  , ("Paul",   "Yale", 60)
  ]

q1 = Q.map (\(view->(n,_,s)) -> Q.fromView (s,n)) employees
q2 = Q.sortWith id q1
q3 = Q.append q1 q2
q4 = Q.groupWith Q.fst q1
q5 = Q.map (+ 42) (toQ [1 .. 10 :: Int])

q6 = [$qc| e | e <- (toQ "foo"), let a = e |]

q7 = [$qc| (Q.the dept, Q.sum salary)
  | (name, dept, salary) <- employees
  , then group by dept
  , then Q.sortWith by (sum salary)
  , then Q.take 5 |]

-- output2 = [$qc| (snd (fst (the e)), (sum (snd (snd e))))
--   | e <- employees
--   , then group by (snd (fst e))
--   , then sortWith by (sum (snd (snd e)))
--   , then take 5 |]

conn :: Connection
conn = undefined

main :: IO ()
main = do
  fromQ conn q1 >>= print
  fromQ conn q2 >>= print
  fromQ conn q3 >>= print
  fromQ conn q4 >>= print
  fromQ conn q5 >>= print
  fromQ conn q6 >>= print
  fromQ conn q7 >>= print