(* This library is an analogue to Haskell's ByteString library
*)
#define ATS_PACKNAME "bytestring"
#define ATS_EXTERN_PREFIX "bytestring_"

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
  ):<>
  Bytestring(0,0)

(* creates new bytestring with content of r appended to l. does not consumes l and r *)
fn
  append
  {l_n, r_n, l_cap, r_cap: nat}
  ( l: !Bytestring(l_n, l_cap)
  , r: !Bytestring(r_n, r_cap)
  ):
  [res_cap: nat | res_cap >= l_n + r_n]
  Bytestring( l_n+r_n, res_cap)

(* the same as append, but consumes arguments in order to make caller's code clear from bunch of val's and free()
 *)
fn
  appendC
  {l_n, r_n, l_cap, r_cap: nat}
  ( l: Bytestring(l_n, l_cap)
  , r: Bytestring(r_n, r_cap)
  ):
  [res_cap: nat | res_cap >= l_n + r_n]
  Bytestring( l_n+r_n, res_cap)

overload + with appendC
(* frees bytestring *)
fn
  free
  {n,cap: nat}
  ( v: Bytestring(n,cap)
  ): void
 
(* creates uninitialized bytestring with given capacity *) 
fn
  create
  {cap: pos}
  ( capacity: size_t(cap)
  ):
  Bytestring(0, cap)


(* TODO: this should not allocate *)
fn
  pack_string
  {n:nat}
  ( s: string(n)
  ):
  [cap:nat | cap >= n]
  Bytestring(n,cap)

fn
  pack_bytes
  {n:nat}{l:agz}
  ( !array_v( char, l, n)
  | i: ptr l
  , sz: size_t n
  ):
  Bytestring( n, n)

symintr pack
overload pack with pack_string
overload pack with pack_bytes

fn
  is_empty
  {n, cap: nat | cap >= n}
  ( i: !Bytestring(n, cap)
  ):<>
  bool (n==0)
fn
  isnot_empty
  {n, cap: nat | cap >= n}
  ( i: !Bytestring(n, cap)
  ):<>
  bool( n > 0)

fn
  eq_bytestring_bytestring
  {l_n, r_n, l_cap, r_cap: nat}
  ( l: !Bytestring( l_n, l_cap)
  , r: !Bytestring( r_n, r_cap)
  ):<>
  [r: bool | (l_n == r_n && r ) || (l_n != r_n || r == false)]
  bool(r)

overload = with eq_bytestring_bytestring

fn
  neq_bytestring_bytestring
  {l_n, r_n, l_cap, r_cap: nat}
  ( l: !Bytestring( l_n, l_cap)
  , r: !Bytestring( r_n, r_cap)
  ):<> bool

overload <> with neq_bytestring_bytestring
overload != with neq_bytestring_bytestring

fn
  ref_bs
  {n, cap: nat | cap >= n}
  ( i: !Bytestring(n,cap)
  ):<!wrt> Bytestring(n,cap)

fn
  copy
  {n,cap: nat | cap >= n}
  ( i: !Bytestring(n,cap)
  ):
  Bytestring( n, cap)

fn
  capacity
  {n, cap: nat | cap >= n}
  ( i: !Bytestring(n,cap)
  ):<> size_t(cap)

fn
  is_empty_capacity
  {n,cap:nat | cap >= n}
  ( i: !Bytestring(n,cap)
  ):<> bool(cap == 0)
fn
  isnot_empty_capacity
  {n,cap:nat | cap >= n}
  ( i: !Bytestring(n,cap)
  ):<> bool(cap > 0)

fn
  unused_capacity
  {len, capacity: nat | capacity >= len}
  ( i: !Bytestring(len, capacity)
  ):<>
  [unused_capacity: nat | unused_capacity < capacity]
  size_t(unused_capacity)

fn
  length_bs
  {n, cap: nat | cap >= n}
  ( i: !Bytestring(n,cap)
  ):<> size_t(n)
overload length with length_bs

fn
  bs2ptr
  {n,cap: nat | cap > 0}
  ( i: !Bytestring(n,cap)
  ): [l:agz] ptr l

fn
  drop
  {i,n,cap: nat | n <= i }
  ( n: size_t n
  , i: !Bytestring(i,cap)
  ):<!wrt>
  [ newn: nat | (i == 0 && newn == 0) || (i > 0 && newn == i - n)]
  Bytestring( newn, cap)
fn
  dropC
  {i,n,cap: nat | n <= i }
  ( n: size_t n
  , i: Bytestring(i,cap)
  ):<!wrt>
  [ newn: nat | (i == 0 && newn == 0) || (i > 0 && newn == i - n)]
  Bytestring( newn, cap)

fn
  take
  {i,n,cap: nat}
  ( n: size_t n
  , i: !Bytestring(i, cap)
  ):<!wrt>
  [newn: nat | (n > i && newn == i) || (newn == n) ]
  Bytestring( newn, cap)

fn
  takeC
  {i,n,cap: nat}
  ( n: size_t n
  , i: Bytestring(i, cap)
  ):<!wrt>
  [newn: nat | (n > i && newn == i) || (newn == n) ]
  Bytestring( newn, cap)

fn
  println
  {n,cap: nat | n > 0}
  ( i: !Bytestring(n,cap)
  ): void
fn
  printlnC
  {n,cap: nat | n > 0}
  ( i: Bytestring(n,cap)
  ): void
