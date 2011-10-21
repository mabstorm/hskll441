COS 441 Homework 3

This is a literate Haskell file. It must type check and compile when you
submit it.

Note, on windows, ghci -i./SOE/src doesn't work. 
I used ghci -iSOE/src to extend the ghci search path so it includes
the SOE libraries (where SOE is a subdirectory containing the
SOE libraries).

> import SOE
> import Control.Applicative
> import Animation hiding (planets, translate)
> import Picture

Part IV

This part of the homework involves creating a model solar system.

> translate :: (Float, Float) -> Picture -> Picture
> translate v p =
>     case p of
>       Region c r   -> Region c (Translate v r)
>       p1 `Over` p2 -> (translate v p1) `Over` (translate v p2)
>       EmptyPic     -> EmptyPic
>
> -- Translate a picture behavior by a given vector behavior
> translateB :: (Behavior Float, Behavior Float) -> 
>                Behavior Picture -> 
>                Behavior Picture
> translateB (x,y) p = lift2 translate (zipB (x,y)) p
>
> -- Convert a pair of behaviors into a pair behavior
> zipB :: (Behavior a, Behavior b) -> Behavior (a,b)
> zipB (Beh b1, Beh b2) = Beh (\t -> (b1 t, b2 t))
>
> -- Construct a circle behavior
> circ :: Behavior Float -> Behavior Shape
> circ r = ell r r
>
> sun :: Behavior Picture
> sun = reg (lift0 Yellow) (shape (circ 1))

The following define the main action of the solar system simulator. 
You'll want to replace the right-hand side of planets with your solar system.

> planets :: Behavior Picture
> planets = sun
>
> main :: IO()
> main = 
>   do animateB "Solar system" (orbit sun mercury 2.0 2.0 0.2)
       
It may be useful for you to use your applicative functor for Behaviors.  Feel
free to copy it in here and use it:

> instance Functor Behavior where
>   fmap f (Beh fn_returnsa) = Beh (\t -> f (fn_returnsa t))
> instance Applicative Behavior where
>   pure f = Beh (\t -> f)
>   (Beh f) <*> (Beh x) = Beh (\t -> f 0.5 (x t))

Next, use the provided function translateB to write a function
       
> orbit :: Behavior Picture -- the satellite
>       -> Behavior Picture -- the fixed body
>       -> Float            -- the frequency of the orbit
>       -> Float            -- the x-radius of the orbit
>       -> Float            -- the y-radius of the orbit
>       -> Behavior Picture
>
> --overB ::  Behavior Picture -> Behavior Picture -> Behavior Picture
> --overB a b = Beh (\t -> Over a b)
> overB = lift2 Over
> timefun :: Behavior Float
> timefun = Beh(\t -> t)
> cosB = lift1 cos
> --time2 = (*2) <*> timefun

>--- orbit p1 p2 freq xrad yrad = lift2 Over p1 p2
>---   where p3 = translateB ( lift0(xrad*cos((fromIntegral(time))*freq)), lift0(yrad*sin((fromIntegral(time))*freq))) p2

> orbit p1 p2 freq xrad yrad = overB (translateB (floatx, floaty) p2) p1
>      where floatx :: Behavior Float
>            floatx = Beh (\t -> xrad*cos (t*freq))
>            floaty :: Behavior Float
>            floaty = Beh (\t -> yrad*sin (t*freq))




that takes two picture behaviors and makes the first orbit around the second at the specified 
distance and with the specified radii. That is, the two pictures will be overlayed (using over) 
and, at each time t, the position of the satellite will be translated by xradius * cos(t * frequency) 
in the x dimension and by yradius * sin(t * frequency) in the y dimension.

> mercury :: Behavior Picture
> mercury = reg (lift0 Red) (shape (circ 0.1))

Test your function by creating another circle, mercury, colored red and with radius 0.1, and 
making it orbit around the sun with a frequency of 2.0, and with radii of 2.0 and 0.2 in the 
x and y axes, respectively.

> -- running this definition in ghci should create the appropriate animation
> orbitTest = do animateB "Solar system" (orbit sun mercury 2.0 2.0 0.2)

A problem you might have noticed is the overlay behavior of planets. For this part modify 
orbit to put planets over or under each other. 


> myanimateB :: Word32 -> Float -> IO ()

> -- running this definition in ghci should create the next animation
> orbitTest' = do
>    t0 <- timeGetTime
>    myanimateB t0 0.2


> myanimateB t0 freq = do
>       t <- timeGetTime
>       let ft = (fromInteger(toInteger(t-t0)) / 1000)
>       let myval = cos(ft*freq)
>       if (myval > 0)
>         then animateB "Solar system" (orbit sun mercury 2.0 2.0 freq)
>         else animateB "Solar system" (orbitBehind sun mercury 2.0 2.0 freq)

> orbitBehind :: Behavior Picture -- the satellite
>       -> Behavior Picture -- the fixed body
>       -> Float            -- the frequency of the orbit
>       -> Float            -- the x-radius of the orbit
>       -> Float            -- the y-radius of the orbit
>       -> Behavior Picture
>

> orbitBehind p1 p2 freq xrad yrad = overB p1 (translateB (floatx, floaty) p2)
>      where floatx :: Behavior Float
>            floatx = Beh (\t -> xrad*cos (t*freq))
>            floaty :: Behavior Float
>            floaty = Beh (\t -> yrad*sin (t*freq))

Modify your functions (and write any support functions that you find necessary) to make the orbital 
distances and planet sizes shrink and grow by some factor (you can pass this factor as parameter 
to the orbit function), according to how far the planets are from the observer. For example, the 
earth and moon should look a little smaller when they are going behind the sun, and the orbital 
distance of the moon from the earth should be less.

> -- running this definition in ghci should create the next animation
> orbitTest'' = error "define me"

Choose the scaling factor so that the solar system simulation looks good to you.
Optional: Add some other planets, perhaps with their own moons. If you like, feel 
free to adjust the parameters we gave above to suit your own aesthetic or astronomical 
tastes. Make sure, though, that the features requested in previous parts - growing, 
shrinking, occlusion, etc. - remain clearly visible.

