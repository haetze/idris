module Help 

export
even : Int -> Bool
even 0 = True
even n = odd (n - 1) where
       odd = not . even
                  
export 
odd : Int -> Bool
odd = not . even
