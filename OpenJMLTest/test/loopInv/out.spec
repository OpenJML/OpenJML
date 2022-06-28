func main()
{
  const Int [] x;
  const Int xlength;
  Int max = x[0];

  Int i = 1;

  while (i < xlength) {
    if (x[i] > max) {
      max = x[i];
    } else { skip; }
    i = i + 1;
  }
  
}
(assert-not
  (=>
    (and
      true
      (>
        xlength
        0
      )
      
    )
    
    (forall ((k Int))
      (=>
        (and
          (<=
            0
            k
          )
          
          (<
            k
            xlength
          )
          
        )
        
        (<=
          (x k)
          (max main_end)
        )
        
      )
    )
  )
)
