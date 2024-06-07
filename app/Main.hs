{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Main where

import Test.QuickCheck

data Label = H | L deriving (Show, Eq)

data LabeledInt = LabeledInt Int Label deriving (Show, Eq)

data Instr = Push LabeledInt
           | Pop | Load | Store
           | Add | Noop | Halt
           deriving (Show, Eq)

type PC     = Int -- program counter
type Stack  = [LabeledInt]
type Memory = [LabeledInt]
type InstrMem = [Instr]

type MachineState = (PC, Stack, Memory, InstrMem)


instance Arbitrary Label where
  arbitrary = elements [H, L]

instance Arbitrary LabeledInt where
  arbitrary = do
    i <- choose (0, 5)
    l <- arbitrary
    pure $ LabeledInt i l

instance Arbitrary Instr where
  arbitrary = do
    li <- arbitrary
    elements [Push li, Pop, Load, Store, Add, Noop]

------- Equivalence relations -------

labeled_int_equiv :: LabeledInt -> LabeledInt -> Bool
labeled_int_equiv (LabeledInt _ H) (LabeledInt _ H) = True
labeled_int_equiv (LabeledInt n1 L) (LabeledInt n2 L) = n1 == n2
labeled_int_equiv _ _ = False

instr_equiv :: Instr -> Instr -> Bool
instr_equiv (Push n1l1) (Push n2l2) = labeled_int_equiv n1l1 n2l2
instr_equiv i1 i2 = i1 == i2


pushGen :: Gen (Instr, Instr)
pushGen = do
  l1 <- arbitrary
  l2 <- arbitrary
  i1 <- choose (0,5)
  i2 <- choose (0,5)
  return (Push (LabeledInt i1 l1), Push (LabeledInt i2 l2))

-- this property will fail; writing for practise
prop_instr_equiv :: Property
prop_instr_equiv = forAll pushGen (\(i1, i2) -> instr_equiv i1 i2)

-- Instruction memory equivalence
instr_mem_equiv :: InstrMem -> InstrMem -> Bool
instr_mem_equiv im1 im2 = and $ zipWith instr_equiv im1 im2

-- Data memory equivalence
mem_equiv :: Memory -> Memory -> Bool
mem_equiv m1 m2 = and $ zipWith labeled_int_equiv m1 m2


machine_state_equiv :: MachineState -> MachineState -> Bool
machine_state_equiv (_, _, m1, i1) (_, _, m2, i2) =
  mem_equiv m1 m2 && instr_mem_equiv i1 i2

-------- Non interference theorem --------


-- generate (arbitrary :: Gen [Instr])
-- generate $ vectorOf 5 (arbitrary :: Gen Instr)

equiv_ms_gen :: Gen (MachineState, MachineState)
equiv_ms_gen = do
  -- Machine State 1 --
  i1 <- vectorOf 5 arbitrary -- naive generator of instructions
  let ms1 = (0, [], replicate 10 initVal, i1 ++ [Halt])
  -- Machine State 2 --
  i2 <- equiv_instr_gen i1 []
  let ms2 = (0, [], replicate 10 initVal, i2 ++ [Halt])
  return (ms1, ms2)
  where
    initVal = LabeledInt 0 L

equiv_instr_gen :: [Instr] -> [Instr] -> Gen InstrMem
equiv_instr_gen [] i_equiv = return (reverse i_equiv)
equiv_instr_gen (i1 : is) i_equiv = do
  i_g <- arbitrary `suchThat` (\i_gen -> i1 `instr_equiv` i_gen)
  equiv_instr_gen is (i_g:i_equiv)


eeni :: Property
eeni =
  forAll equiv_ms_gen
  (\(ms1, ms2) -> (step ms1) `machine_state_equiv` (step ms2))

eeni_naive :: MachineState -> MachineState -> Property
eeni_naive ms1 ms2 =
  (ms1 `machine_state_equiv` ms2)
                   ==> (step ms1) `machine_state_equiv` (step ms2)


(~>) :: InstrMem -> PC -> Instr
(~>) i pc = i !! pc


step :: MachineState -> MachineState
step ms@(pc, s, m, i)
  | step' (i ~> pc) == ms = (pc, s, m, i) --error "Machine halted"
  | otherwise = step' (i ~> pc)
  where
    pc' = pc + 1
    step' :: Instr ->  MachineState
    step' Noop     = (pc', s, m, i)
    step' (Push n) = (pc', n:s, m, i)
    step' Pop      = (pc', tail s, m, i)
    step' Load     = (pc', n:(tail s), m, i)
      where (LabeledInt p _) = head s -- threw the label
            n = m !! p
    step' Store    = (pc', s', m', i)
      where ((LabeledInt p _):n:s') = s -- threw the label
            m' = updList p n m
    step' Add  = (pc', (LabeledInt (n1 + n2) L):s', m, i)
      where ((LabeledInt n1 _):(LabeledInt n2 _):s') = s -- threw two labels
    step' Halt = (pc, s, m, i) -- return the same state back

updList :: Int -> a -> [a] -> [a]
updList i x xs = take i xs ++ [x] ++ drop (i + 1) xs


main :: IO ()
main = putStrLn "Hello, Haskell!"

{-@ QuickCheck combinators

arbitrary :: Arbitrary a => Gen a

-- generators
vectorOf  :: Int   -> Gen a       -> Gen [a]
suchThat  :: Gen a -> (a -> Bool) -> Gen a
oneof     :: [Gen a] -> Gen a
choose    :: Random a => (a, a) -> Gen a
elements  :: [a] -> Gen a
frequency :: [(Int, Gen a)] -> Gen a

-- property combinators
forAll :: (Show a, Testable prop)
       => Gen a -> (a -> prop) -> Property
(==>)  :: Testable prop => Bool -> prop -> Property

generate :: Gen a -> IO a

@-}



