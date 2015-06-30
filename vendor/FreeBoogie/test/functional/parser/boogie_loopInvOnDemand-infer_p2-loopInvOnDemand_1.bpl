procedure M(N: int)
{
  var i : int, m : int, N$in : int;

  start:
    N$in := N;
    i := 0;
    m := 0;
    goto body, end;	

  body:			
    assume i < N;	
    goto then, else;	

    then:
      m := i;		 	
      goto join;

    else:		
      goto join;

    join:		
      i := i + 1;
      goto body, end, JoinCheck;	

    JoinCheck:
      assert i <= N && 0 <= m && 1 <= i && m < N;
      return;

  end:
    goto checkIfNgz, realEnd;		

  checkIfNgz:
     assume N > 0;  // = If N >0 then...
     assert 0<= m && m < N;
     goto realEnd;

  realEnd:
    return;
}