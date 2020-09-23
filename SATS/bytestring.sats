(* This library is an analogue to Haskell's ByteString library
*)

(* abstract viewtype, that describes Bytestring with capacity and size *)
absvt0ype Bytestring_vtype(n:int, cap: int) = ( void | (size_t, size_t, size_t, ptr))

vtypedef Bytestring(n:int) =
  [cap:nat | cap >= n]
  Bytestring_vtype( n, cap)

(* bytestring, that can be empty *)
vtypedef
  Bytestring0 =
  [n: nat | n >= 0]
  Bytestring(n)

(* non-empty bytestring *)
vtypedef
  Bytestring1 =
  [n: pos]
  Bytestring( n)

prfun
  lemma_bytestring_param
  {n,cap:nat}
  ( v: !Bytestring_vtype(n, cap)
  ):
  [ n <= cap ] (* n should not exceed capacity *)
  void

(* creates an empty bytestring *)
fn
  empty
  (
  ):<>
  Bytestring_vtype(0,0)

(* creates new bytestring with content of r appended to l. does not consumes l and r *)
fn
  append
  {l_n, r_n: nat}
  ( l: !Bytestring(l_n)
  , r: !Bytestring(r_n)
  ):
  Bytestring( l_n+r_n)

(* the same as append, but consumes arguments in order to make caller's code clear from bunch of val's and free()
 *)
fn
  appendC
  {l_n, r_n: nat}
  ( l: Bytestring(l_n)
  , r: Bytestring(r_n)
  ):
  Bytestring( l_n+r_n)

overload + with appendC
(* frees bytestring *)
fn
  free
  {n: nat}
  ( v: Bytestring(n)
  ): void
 
(* creates uninitialized bytestring with given capacity *) 
fn
  create
  {cap: pos}
  ( capacity: size_t(cap)
  ):
  Bytestring_vtype(0, cap)


(* TODO: this should not allocate *)
fn
  pack_string
  {n:nat}
  ( s: string(n)
  ):
  Bytestring(n)

fn
  pack_bytes
  {n:nat}{l:agz}
  ( !array_v( char, l, n)
  | i: ptr l
  , sz: size_t n
  ):
  Bytestring( n)

symintr pack
overload pack with pack_string
overload pack with pack_bytes

fn
  is_empty
  {n: nat}
  ( i: !Bytestring(n)
  ):<>
  bool (n==0)
fn
  isnot_empty
  {n: nat}
  ( i: !Bytestring(n)
  ):<>
  bool( n > 0)

fn
  eq_bytestring_bytestring
  {l_n, r_n: nat}
  ( l: !Bytestring( l_n)
  , r: !Bytestring( r_n)
  ):<>
  [r: bool | (l_n == r_n && r ) || (l_n != r_n || r == false)]
  bool(r)

overload = with eq_bytestring_bytestring

fn
  neq_bytestring_bytestring
  {l_n, r_n: nat}
  ( l: !Bytestring( l_n)
  , r: !Bytestring( r_n)
  ):<> bool

overload <> with neq_bytestring_bytestring
overload != with neq_bytestring_bytestring

fn
  ref_bs
  {n: nat}
  ( i: !Bytestring(n)
  ):<!wrt> Bytestring(n)

fn
  copy
  {n: nat}
  ( i: !Bytestring(n)
  ):
  Bytestring( n)

fn
  capacity
  {n,cap: nat | cap >= n}
  ( i: !Bytestring_vtype(n,cap)
  ):<> size_t(cap)

fn
  is_empty_capacity
  {n,cap:nat | cap >= n}
  ( i: !Bytestring_vtype(n,cap)
  ):<> bool(cap == 0)
fn
  isnot_empty_capacity
  {n,cap:nat | cap >= n}
  ( i: !Bytestring_vtype(n,cap)
  ):<> bool(cap > 0)

fn
  unused_capacity
  {len, capacity: nat | capacity >= len}
  ( i: !Bytestring_vtype(len, capacity)
  ):<>
  [unused_capacity: nat | unused_capacity < capacity]
  size_t(unused_capacity)

fn
  length_bs
  {n: nat}
  ( i: !Bytestring(n)
  ):<> size_t(n)
overload length with length_bs

fn
  bs2ptr
  {n: nat}
  ( i: !Bytestring(n)
  ):
  [l:addr]
  ptr l

fn
  drop
  {i,n: nat | n <= i }
  ( n: size_t n
  , i: !Bytestring(i)
  ):<!wrt>
  [ newn: nat | (i == 0 && newn == 0) || (i > 0 && newn == i - n)]
  Bytestring( newn)
fn
  dropC
  {i,n: nat | n <= i }
  ( n: size_t n
  , i: Bytestring(i)
  ):<!wrt>
  [ newn: nat | (i == 0 && newn == 0) || (i > 0 && newn == i - n)]
  Bytestring( newn)

fn
  take
  {i,n: nat | n <= i}
  ( n: size_t n
  , i: !Bytestring(i)
  ):<!wrt>
  [newn: nat | (i == 0 && newn == 0) || (i > 0 && newn == n) ]
  Bytestring( newn)

fn
  takeC
  {i,n: nat | n <= i}
  ( n: size_t n
  , i: Bytestring(i)
  ):<!wrt>
  [newn: nat | (i == 0 && newn == 0) || (i > 0 && newn == n) ]
  Bytestring( newn)

fn
  println
  {n: pos}
  ( i: !Bytestring(n)
  ): void
fn
  printlnC
  {n: pos}
  ( i: Bytestring(n)
  ): void
