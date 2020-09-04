(* This library is an analogue to Haskell's ByteString library
*)

(* abstract viewtype, that describes Bytestring with capacity and size *)
absvt0ype Bytestring(n:int, cap: int) = ( void | (size_t, size_t, size_t, ptr))

(* bytestring, that can be empty *)
vtypedef
  Bytestring0 =
  [n,cap: nat | n >= 0]
  Bytestring(n,cap)

(* non-empty bytestring *)
vtypedef
  Bytestring1 =
  [n,cap: pos | n <= cap]
  Bytestring( n, cap)

prfun
  lemma_bytestring_param
  {n,cap:nat}
  ( v: !Bytestring(n, cap)
  ):
  [ n <= cap ] (* n should not exceed capacity *)
  void

(* creates an empty bytestring *)
fn
  empty
  (
  ):
  [cap:nat | cap >= 0]
  Bytestring(0,cap)

(* creates new bytestring with content of r appended to l. does not consumes l and r *)
fn
  append
  {l_n, r_n, l_cap, r_cap: nat}
  ( l: !Bytestring(l_n, l_cap)
  , r: !Bytestring(r_n, r_cap)
  ):
  [res_cap: nat | res_cap >= r_cap + l_cap]
  Bytestring( l_n+r_n, res_cap)

(* the same as append, but consumes arguments in order to make caller's code clear from bunch of val's and free()
 *)
fn
  appendC
  {l_n, r_n, l_cap, r_cap: nat}
  ( l: Bytestring(l_n, l_cap)
  , r: Bytestring(r_n, r_cap)
  ):
  [res_cap: nat | res_cap >= r_cap + l_cap]
  Bytestring( l_n+r_n, res_cap)

overload + with appendC
(* frees bytestring *)
fn
  free
  {n,cap: nat | cap >= n}
  ( v: Bytestring(n,cap)
  ): void
 
(* creates uninitialized bytestring with given capacity *) 
fn
  create
  {cap: pos}
  ( capacity: size_t(cap)
  ):
  Bytestring(0, cap)


fn
  pack_string
  {n:nat}
  ( s: string(n)
  ):
  [cap:nat | cap >= n]
  Bytestring(n,cap)

symintr pack
overload pack with pack_string
  
fn
  eq_bytestring_bytestring
  {l_n, r_n, l_cap, r_cap: nat}
  ( l: !Bytestring( l_n, l_cap)
  , r: !Bytestring( r_n, r_cap)
  ):<> bool

overload = with eq_bytestring_bytestring

fn
  neq_bytestring_bytestring
  {l_n, r_n, l_cap, r_cap: nat}
  ( l: !Bytestring( l_n, l_cap)
  , r: !Bytestring( r_n, r_cap)
  ):<> bool

overload <> with neq_bytestring_bytestring
overload != with neq_bytestring_bytestring