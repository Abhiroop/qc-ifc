{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Main where

import Test.QuickCheck

data Label = H | L deriving (Show, Eq)

-- least upper bound
(\/) :: Label -> Label -> Label
(\/) H H = H
(\/) H L = H
(\/) L H = H
(\/) L L = L

canFlowTo :: Label -> Label -> Bool
canFlowTo H H = True
canFlowTo L L = True
canFlowTo L H = True
canFlowTo H L = False



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
  arbitrary = sized genWellFormedInstr
  -- do
  --   li <- arbitrary
  --   elements [Push li, Pop, Load, Store, Add, Noop]

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
machine_state_equiv (pc1, _, m1, i1) (pc2, _, m2, i2)
  | pc1 == crash && pc2 == crash = True -- See NOTE 2
  | pc1 == crash && pc2 /= crash = False
  | pc1 /= crash && pc2 == crash = False
  | otherwise = mem_equiv m1 m2 && instr_mem_equiv i1 i2

-- NOTE 2
-- Because the program crashed, the observer can now only
-- observe the crash. There is no guarantee about the rest
-- of the machine state; it is considered corrupted.
-- We first check if both programs have crashed. If both
-- show crash behaviour we current consider them equivalent.
-- If one crashed and the other didn't then the programs
-- are not equivalent;
-- If both didn't crash, inspect the behaviour.

(~~) :: MachineState -> MachineState -> Bool
(~~) = machine_state_equiv


-------- Non interference theorem --------


-- generate (arbitrary :: Gen [Instr])
-- generate $ vectorOf 5 (arbitrary :: Gen Instr)

{- Well formed instruction constraints

          Stack size          Memory size
Noop          ~                    ~
Push          ~                    ~
Pop          >= 1                  ~
Load         >= 1         mem_size >= stack_head
Store        >= 2         mem_size >= stack_head
Add          >= 2                  ~
Halt          ~                    ~


mem_size constraint handling:
Labeled Int's generator chooses between 0 and 5 and the
mem_size is at static 10; so second constraint handled.

-}

genWellFormedInstr :: Int -> Gen Instr
genWellFormedInstr stackSize
  | stackSize == 0 = frequency [ (5, Push <$> l_int_gen)
                               , (1, return Noop)
                               , (1, return Halt)]
  | stackSize == 1 = frequency [ (4, Push <$> l_int_gen)
                               , (4, return Pop)
                               , (3, return Load)
                               , (3, return Noop)
                               , (1, return Halt)
                               ]
  | otherwise      = frequency [ (5, Push <$> l_int_gen)
                               , (5, return Pop)
                               , (4, return Load)
                               , (4, return Store)
                               , (5, return Add)
                               , (3, return Noop)
                               , (1, return Halt)
                               ]
  where
    l_int_gen :: Gen LabeledInt
    l_int_gen = arbitrary -- see NOTE 1 for strategy

-- Generator for a sequence of well-formed instructions
genWellFormedProgram :: Int -> Gen [Instr]
genWellFormedProgram stackSize = do
  instr <- genWellFormedInstr stackSize
  case instr of
    Push _ -> (instr :) <$> genWellFormedProgram (stackSize + 1)
    Pop    -> (instr :) <$> genWellFormedProgram (stackSize - 1)
    Add    -> (instr :) <$> genWellFormedProgram (stackSize - 2)
    Store  -> (instr :) <$> genWellFormedProgram (stackSize - 2)
    Halt   -> return [instr]
    _      -> (instr :) <$> genWellFormedProgram stackSize

initStackSize :: Int
initStackSize = 0

equiv_ms_gen :: Gen (MachineState, MachineState)
equiv_ms_gen = do
  -- Machine State 1 --
  i1 <- genWellFormedProgram initStackSize
  let ms1 = (0, [], replicate 10 initVal, i1)
  -- Machine State 2 --
  i2 <- equiv_instr_gen i1 []
  let ms2 = (0, [], replicate 10 initVal, i2)
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
  (\(ms1, ms2) ->
     (ms1 ~~ ms2) ==> -- generator ensures this; non needed
     (step ms1) ~~ (step ms2))




-- Bug #1 counterexample
i1 :: InstrMem
i1 = [Push (LabeledInt 3 L),Push (LabeledInt 1 H),Noop,Store,Push (LabeledInt 2 H),Load,Noop,Pop,Halt]

i2 :: InstrMem
i2 = [Push (LabeledInt 3 L),Push (LabeledInt 0 H),Noop,Store,Push (LabeledInt 1 H),Load,Noop,Pop,Halt]


-- Bug #2 counterexample
i3 = [Push (LabeledInt 1 H),Pop,Push (LabeledInt 5 H),Push (LabeledInt 4 H),Noop,Pop,Push (LabeledInt 5 H),Store,Push (LabeledInt 4 H),Noop,Noop,Pop,Push (LabeledInt 3 H),Noop,Push (LabeledInt 1 L),Pop,Load,Halt]

i4 = [Push (LabeledInt 5 H),Pop,Push (LabeledInt 3 H),Push (LabeledInt 2 H),Noop,Pop,Push (LabeledInt 3 H),Store,Push (LabeledInt 1 H),Noop,Noop,Pop,Push (LabeledInt 1 H),Noop,Push (LabeledInt 1 L),Pop,Load,Halt]

-- Bug #3 counterexample
i5 = [Noop,Push (LabeledInt 3 H),Noop,Push (LabeledInt 2 H),Load,Push (LabeledInt 3 L),Load,Pop,Noop,Add,Noop,Push (LabeledInt 2 L),Load,Push (LabeledInt 4 L),Push (LabeledInt 1 H),Add,Push (LabeledInt 4 L),Store,Push (LabeledInt 4 L),Pop,Push (LabeledInt 3 L),Push (LabeledInt 3 L),Load,Load,Add,Push (LabeledInt 2 H),Push (LabeledInt 0 L),Load,Halt]

i6 = [Noop,Push (LabeledInt 0 H),Noop,Push (LabeledInt 5 H),Load,Push (LabeledInt 3 L),Load,Pop,Noop,Add,Noop,Push (LabeledInt 2 L),Load,Push (LabeledInt 4 L),Push (LabeledInt 4 H),Add,Push (LabeledInt 4 L),Store,Push (LabeledInt 4 L),Pop,Push (LabeledInt 3 L),Push (LabeledInt 3 L),Load,Load,Add,Push (LabeledInt 1 H),Push (LabeledInt 0 L),Load,Halt]



i7 = [Push (LabeledInt 2 H),Push (LabeledInt 0 L),Load,Pop,Push (LabeledInt 1 L),Store,Push (LabeledInt 4 L),Load,Load,Push (LabeledInt 5 H),Push (LabeledInt 1 H),Store,Halt]

i8 = [Push (LabeledInt 4 H),Push (LabeledInt 0 L),Load,Pop,Push (LabeledInt 1 L),Store,Push (LabeledInt 4 L),Load,Load,Push (LabeledInt 0 H),Push (LabeledInt 0 H),Store,Halt]


ms1, ms2 :: MachineState
ms1 = (0, [], replicate 6 (LabeledInt 0 L), i7)
ms2 = (0, [], replicate 6 (LabeledInt 0 L), i8)


(~>) :: InstrMem -> PC -> Instr
(~>) i pc = i !! pc

-- @ upon program crash set PC = -1
crash :: PC
crash = -1

step :: MachineState -> MachineState
step ms@(pc, s, m, i)
  | pc == -1 = (pc, s, m, i) -- program crashed
  | step' (i ~> pc) == ms = (pc, s, m, i)
  | otherwise = step (step' (i ~> pc))
  where
    pc' = pc + 1
    step' :: Instr ->  MachineState
    step' Noop     = (pc', s, m, i)
    step' (Push n) = (pc', n:s, m, i)
    step' Pop      = (pc', tail s, m, i)
    -- step' Load     = (pc', n:(tail s), m, i)
    --   where (LabeledInt p _) = head s
    --         n = m !! p
    step' Load     = (pc', (LabeledInt n (l_n \/ l_p)):(tail s), m, i)
      where (LabeledInt p l_p) = head s
            (LabeledInt n l_n) = m !! p

    -- step' Store    = (pc', s', m', i) -- Bug #1
    --   where ((LabeledInt p _):n:s') = s
    --         m' = updList p n m
    -- step' Store    = (pc', s', m', i) -- Bug #2
    --   where ((LabeledInt p l_p):(LabeledInt n l_n):s') = s
    --         m' = updList p (LabeledInt n (l_p \/ l_n)) m
    step' Store
      | l_p `canFlowTo` l_n' = (pc', s', m', i)
      | otherwise = (crash, s, m, i)
      where ((LabeledInt p l_p):(LabeledInt n l_n):s') = s
            (LabeledInt _ l_n') = m !! p
            m' = updList p (LabeledInt n (l_n \/ l_p)) m
    -- step' Add  = (pc', (LabeledInt (n1 + n2) L):s', m, i) -- Bug #3
    --   where ((LabeledInt n1 _):(LabeledInt n2 _):s') = s
    step' Add  = (pc', (LabeledInt (n1 + n2) (l_1 \/ l_2)):s', m, i)
      where ((LabeledInt n1 l_1):(LabeledInt n2 l_2):s') = s -- threw two labels

    step' Halt = (pc, s, m, i) -- return the same state back

updList :: Int -> a -> [a] -> [a]
updList i x xs = take i xs ++ [x] ++ drop (i + 1) xs

main :: IO ()
main = putStrLn "Hello, Haskell!"

{-@ QuickCheck combinators

arbitrary :: Arbitrary a => Gen a

-- generators
listOf    :: Gen a -> Gen [a]
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
sample   :: Show a => Gen a -> IO ()
@-}



--NOTE 1
{-
Strategy: current generator for labeled int
  arbitrary = do
    i <- choose (0, 5)
    l <- arbitrary
    pure $ LabeledInt i l

instead use the a few bits of the integer to
differentiate between pointers and numbers;
Then you can have

i <- oneof [ choose (0,5) -- normal ints
           , generate pointers
           ]

Given that you do this now inside l_int_gen

l_int_gen memory = do
   (LabeledInt n l_n) <- arbitrary
   if (n is pointer)
   then ensure l_n `canFlowTo` (labelOf $ memory !! n)
        if flow not allowed keep generating till
        flow is allowed
        return ((LabeledInt n l_n))
   else arbitrary


-}
