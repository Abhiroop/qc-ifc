{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Main where

import Test.QuickCheck

data Instr = Push Int
           | Pop | Load | Store
           | Add | Noop | Halt
           deriving (Show, Eq)

type PC     = Int -- program counter
type Stack  = [Int]
type Memory = [Int]
type InstrMem = [Instr]

type MachineState = (PC, Stack, Memory, InstrMem)

(~>) :: InstrMem -> PC -> Instr
(~>) i pc = i !! pc


step :: MachineState -> MachineState
step ms@(pc, s, m, i)
  | step' (i ~> pc) == ms = error "Machine halted"
  | otherwise = step' (i ~> pc)
  where
    pc' = pc + 1
    step' :: Instr ->  MachineState
    step' Noop     = (pc', s, m, i)
    step' (Push n) = (pc', n:s, m, i)
    step' Pop      = (pc', tail s, m, i)
    step' Load     = (pc', (m !! head s):s, m, i)
    step' Store    = (pc', s', m', i)
      where (p:n:s') = s
            m' = updList p n m
    step' Add  = (pc', (n1 + n2):s', m, i)
      where (n1:n2:s') = s
    step' Halt = (pc, s, m, i) -- return the same state back

updList :: Int -> a -> [a] -> [a]
updList i x xs = take i xs ++ [x] ++ drop (i + 1) xs

main :: IO ()
main = putStrLn "Hello, Haskell!"
