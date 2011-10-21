COS 441 Assignment 3

Student Names: Michael Bailey, Leon Ho 
Student Logins: mabailey, tlho

This is a literate Haskell file. 
When you submit this file, it must type check and compile
in ghci when used with the SOE Animation and Picture libraries.

> import Control.Applicative
> import Data.Char as Char


Part I

(a) In lecture, we proved that our definition of equality on the type
MyPair a b was reflexive and transitive.  Define a type class instance
for MyBadPair a b that is reflexive but is *not* transitive.

> data Bit = On | Off
>             deriving (Show)
> instance Eq Bit where
>   On  == On  = True
>   Off == Off = True
>   On  == Off = False
>   Off == On  = False

> data Pair a b = Pair a b deriving (Show)
> instance (Eq a, Eq b) => Eq (Pair a b) where
>   (==) (Pair x1 y1) (Pair x2 y2) = (x1==x2)&&(y1==y2)

> data MyBadPair a b = MBP a b Int deriving (Show)
> instance (Eq a, Eq b) => Eq (MyBadPair a b) where
>   (==) (MBP x1 y1 0) (MBP x2 y2 0) = ((x1==x2)&&(y1==y2))||((x1==x2)&&(y1/=y2))||((x1/=x2)&&(y1==y2))

 data MyBadPair a b = MBP a b Int
                       deriving (Eq,Show)

(b) Prove that your definition of MyBadPair is not transitive by
giving concrete definitions for x, y, z such that x == y and y == z
but x /= z

> xc, yc, zc :: MyBadPair Bit Bit
> xc = MBP On On 0
> yc = MBP On Off 0
> zc = MBP Off Off 0
> b1 = xc == yc
> b2 = yc == zc
> b3 = xc == zc

If the following test evaluates to True, you have successfully given
a counterexample that proves your type class instance is not transitive.

> test_c = b1 && b2 && not b3

Part II

Lattices are common mathematical structures involving a set of objects and
an ordering (<:). 

Optional:  Find out more about lattices here:  
http://en.wikipedia.org/wiki/Lattice_%28order%29

> class Eq a => Lattice a where
>   bot  :: a                -- the lowest element in the ordering
>   top  :: a                -- the highest element in the ordering
>   (<:) :: a -> a -> Bool   -- the ordering
>   join :: a -> a -> a      -- join a b is the smallest thing bigger than both a and b 
>                            -- also called the least upper bound
>   meet :: a -> a -> a      -- join a b is the largest thing smaller than both a and b
>                            -- also called the greatest lower bound

Lattices must obey a number of laws.  Here are some of the laws.  
For any lattice elements x, y:

     bot <: x
       x <: top

       x <: join x y
meet x y <: x

meet x x == x   (idempotence I)
join x x == x   (idempotence II)

join x y == join y x    (commutativity)
meet x y == meet y x    (commutativity)

join x (join y z) == join (join x y) z   (associativity)
meet x (meet y z) == meet (meet x y) z   (associativity)

meet x (join x y) == x  (absorption I)
join x (meet x y) == x  (absorption II)


In government, and in secure programming systems, lattices are used to describe the
security level of data.  Let's define a security instance that satisfies the
laws above:

> data SecurityLevel = Public | Secret | TopSecret deriving (Eq,Show)

> instance Lattice SecurityLevel where
>   bot = Public
>   top = TopSecret
>
>   Public <: _          = True
>   _      <: TopSecret  = True
>   Secret <: Secret     = True
>   _      <: _          = False
>
>   join _         TopSecret = TopSecret
>   join TopSecret _         = TopSecret
>   join Public    Public    = Public
>   join _         _         = Secret
>
>   meet _         Public    = Public
>   meet Public    _         = Public
>   meet TopSecret TopSecret = TopSecret
>   meet _         _         = Secret

Optional:  Find out more about secure, information-flow tracking 
programming in Haskell here:  http://www.cis.upenn.edu/~stevez/papers/LZ06a.pdf

(a) Given any Lattice type a, it is possible to extend the lattice with a global bottom
element by injecting the Lattice type a into the Maybe a type.  Fill in the following
definitions to define the Maybe lattice such that they satisfy the Lattice axioms.

> instance Lattice a => Lattice (Maybe a) where
>  bot = Nothing
>  top = Just top

>  Nothing <: Nothing = False
>  Nothing <: (Just y) = True
>  (Just x) <: Nothing = False
>  (Just x) <: (Just y) = x <: y


>  join Nothing Nothing = Nothing
>  join Nothing (Just y) = Just y
>  join (Just x) Nothing = Just x
>  join (Just x) (Just y) = Just (join x y)

>  meet Nothing Nothing = Nothing
>  meet Nothing (Just y) = Nothing
>  meet (Just x) Nothing = Nothing
>  meet (Just x) (Just y) = Just (meet x y)


(b) Assuming all other Lattices satisfy the Lattice laws listed above,
prove your definition of join is an upper bound.

Prove:  for all x, y: x <: join x y

case x = Nothing, y = Just y
  1.) join x y = join Nothing (Just y)  (by substitution)
  2.) join Nothing (Just y) = Just y    (by our definition of join)
  3.) x <: join x y = x <: Just y       (by 2)
  4.) x <: Just y = Nothing <: Just y   (by substitution of x)
  5.) Nothing <: Just y = True          (by our def of <: )
case done

case x = Just x, y = Nothing
  1.) join x y = join (Just x) Nothing  (by substitution)
  2.) join (Just x) Nothing = Just x    (by our definition of join)
  3.) x <: join x y = x <: Just x       (by 2)
  4.) Just x <: Just x = x <: x         (by def of Just)
  5.) x <: x = x <: join x x            (by idempotence II)
  6.) x <: join x x = True              (by law "x <: join x y")
case done

case x = Just x, y = Just y
  1.) join x y = join (Just x) (Just y) (by substitution)
  2.) join (Just x) (Just y) = Just (join x y) (by our def of join)
  3.) x <: join x y = x <: Just (join x y)     (by substitution, 2)
  4.) x <: Just (join x y) = x <: join x y     (by def of Just)
  5.) x <: join x y = True                     (by law "x <: join x y")
case done


(c) Assuming all other Lattices satisfy the Lattice laws listed above,
prove the first absorption law.

Prove:  for all x, y:  meet x (join x y) == x

case y <: x
  1.) join x y = x                    (by def of join on case y <: x)
  2.) meet x (join x y) = meet x x    (by 1)
  3.) meet x x = x                    (by idempotence I)
case done

case x <: y
  1.) join x y = y                    (by def of join on case x <: y)
  2.) meet x (join x y) = meet x y    (by 1)
  3.) meet x y = x                    (by def of meet on case x <: y)
case done

case x = y
  1.) join x x = x                    (by idempotence II and case x = y)
  2.) meet x (join x x) = meet x x    (by 1)
  3.) meet x x = x                    (by idempotence I)
case done



Part III

Refer to Learn You a Haskell for Great Good, Chapter 7, pg 146-152 and Chapter 11 for 
information on Functors and Applicative Functors.

(a) Define two type class instances for Behavior.  One as a Functor.  One
as an Applicative.  Hint:  Analyze the types of the objects involved.  Know
the types that fmap, pure and <*> must have.  Construct their definitions
in a way such that the types line up.

> type Time = Float
> newtype Behavior a = Beh (Time -> a)
> instance Functor Behavior where
>   fmap f (Beh fn_returnsa) = Beh (\t -> f (fn_returnsa t))
> instance Applicative Behavior where
>   pure f = Beh (\t -> f)
>   (Beh f) <*> (Beh x) = Beh (\t -> f 0.5 (x t))
>

> -- determines a behavior's value at a time; useful for testing
> at :: Behavior a -> Time -> a
> at (Beh f) t = f t
>                
> time :: Behavior Time
> time = Beh (\t -> t)

The following laws for your definitions must hold (you do not have to submit
proofs for all of them, but you should check them yourself). 

For all behaviors u, v, w with appropriate types:

fmap (\x -> x) u = u

fmap (f . g) = fmap f . fmap g

pure (\x -> x) <*> u = u

pure (.) <*> u <*> v <*> w = u <*> (v <*> w)

pure f <*> pure x = pure (f x)

u <*> pure y = pure (\f -> f y) <*> u

fmap f x = pure f <*> x

(b) Show that you understand how to use these type classes.  Once you
have defined your type classes, prefix the following lines
with ">" so ghci will interpret them.

> phrase        :: Behavior String
> phrase        =  pure "The current time is: "

> toUpperString :: Behavior (String -> String)
> toUpperString =  pure (map Char.toUpper)

Then use those definitions, along with your type classes 
to create a Behavior String that equals 
"THE CURRENT TIME IS: ..." where "..." is the current 
time (ie: ticker has similar functionality to the 
ticker defined in the lecture slides).  If you
read the documentation concerning applicative functors
here:  

http://haskell.org/ghc/docs/6.12.1/html/libraries/base/Control-Applicative.html

you may find some useful functions such as <$> <$ <**> liftA liftA2 liftA3.
(You'll probably only use one of them below, but more may be useful later.)

> ticker :: Behavior String
> ticker = error "fill me in" -- change this

(c) Prove that for your definitions, 

    pure f <*> pure x = pure (f x)
           
(d) Prove that for your definitions, for any b :: Behavior a

    fmap (f . g) b = ((fmap f) . (fmap g)) b

    You may use the definition of function composition (f . g):
           
    (f . g) x = f (g x)
           

