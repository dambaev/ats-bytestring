(* This library is an analogue to Haskell's ByteString library
*)
#define ATS_PACKNAME "bytestring"
#define ATS_EXTERN_PREFIX "bytestring_"

(* abstract viewtype, that describes Bytestring with capacity and size *)
absvt0ype
  Bytestring_vtype
  ( len:int (* size in bytes, which occupied by data *)
  , offset: int (* the offset from base pointer at which data of length len starts *)
  , cap: int (* capacity of the buffer *)
  , ucap: int (* how much unused bytes of buffer available after this bytestring *)
  , refcnt:int (* how many other bytestrings refer to this bytestring *)
  , dynamically_allocated: bool (* if false, then base pointer is statically allocated *)
  , base: addr (* base pointer *)
  ) = 
  ( void 
  | ( size_t (* len *)
    , size_t (* offset *)
    , size_t (* capacity *)
    , size_t (* available capacity *)
    , size_t (* refcnt *)
    , bool (* is dynamically allocated *)
    , ptr
    )
  )

(* bytestring, that can be empty *)
vtypedef
  Bytestring0 =
  [len,offset,cap,ucap,refcnt:nat][dynamically_allocated:bool][l:addr]
  Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamically_allocated,l)

(* non-empty bytestring *)
vtypedef
  Bytestring1 =
  [len: pos][offset,cap,ucap,refcnt:nat][dynamically_allocated:bool][l:agz]
  Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamically_allocated,l)

vtypedef
  Bytestring(len) =
  {len: nat}[offset,cap,ucap,refcnt:nat][dynamically_allocated:bool][l:agz]
  Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamically_allocated,l)

vtypedef
  BytestringNSH(len:int) =
  {len: nat}[offset,cap,ucap:nat][dynamically_allocated:bool][l:agz]
  Bytestring_vtype( len, offset, cap, ucap, 0, dynamically_allocated,l)
  
vtypedef
  BytestringNSH0 =
  [len: nat][offset,cap,ucap:nat][dynamically_allocated:bool][l:agz]
  Bytestring_vtype( len, offset, cap, ucap, 0, dynamically_allocated,l)

vtypedef
  BytestringNSH1 =
  [len: pos][offset,cap,ucap:nat][dynamically_allocated:bool][l:agz]
  Bytestring_vtype( len, offset, cap, ucap, 0, dynamically_allocated,l)

viewdef
  Bytestring_v(a:t0ype, len:int, offset:int, cap: int, ucap: int, refcnt:int, dynamically_allocated:bool, l:addr) = array_v( a, l, cap)

prfun
  lemma_bytestring_param
  {n,offset,cap,ucap,refcnt:nat}{dynamic:bool}{l:addr}
  ( v: !Bytestring_vtype(n, offset,cap,ucap,refcnt,dynamic,l)
  ):
  [ ( n > 0 && l > null); (cap > 0 && l > null); (l > null && n >= 0); n+offset <= cap; offset+n+ucap <= cap ] (* n should not exceed capacity *)
  void

(* creates an empty bytestring *)
fn
  empty
  (
  ):<>
  Bytestring_vtype(0,0,0,0,0,false,null)

fn
  pack_string
  {n:nat}
  ( s: string(n)
  ):
  [l:agz]
  Bytestring_vtype(n,0,n,0,0,false,l)

symintr pack
overload pack with pack_string

fn
  pack_chars_static
  {n,cap:nat | cap >= n}{l:agz}{a:t0ype}
  ( !array_v( a, l, cap) >> Bytestring_v(a, n, 0, cap, cap - n, 0, false, l)
  | i: ptr l
  , sz: size_t n
  , capacity: size_t cap
  ):
  Bytestring_vtype( n, 0, cap, cap - n, 0, false, l)

overload pack with pack_chars_static

fn
  pack_chars_dynamic
  {n,cap:nat | cap >= n}{l:agz}{a:t0ype}
  ( array_v( a, l, cap)
  , mfree_gc_v l
  | i: ptr l
  , sz: size_t n
  , capacity: size_t cap
  ):
  Bytestring_vtype( n, 0, cap, cap - n, 0, true, l)

overload pack with pack_chars_dynamic

fn
  free_static
  {len, offset, cap, ucap: nat}{l:addr}
  ( v: Bytestring_vtype(len, offset, cap, ucap, 0, false, l)
  ):<> void
fn
  free_dynamic
  {len, offset, cap, ucap: nat}{l:addr}
  ( v: Bytestring_vtype(len, offset, cap, ucap, 0, true, l)
  ):<!wrt> void

fn
  free_bs
  {len, offset, cap, ucap: nat}{dynamic:bool}{l:addr}
  ( i: Bytestring_vtype( len, offset, cap, ucap, 0, dynamic, l)
  ):<!wrt> void

symintr free
overload free with free_bs

fn
  free_static_array
  {a:t0ype}
  {len, offset, cap, ucap: nat}{l:addr}
  ( !Bytestring_v(a, len, offset, cap, ucap, 0, false, l) >> array_v( a, l, cap)
  | i: Bytestring_vtype( len, offset, cap, ucap, 0, false, l)
  ): void

overload free with free_static_array

fn
  unref_bs
  {r_len, r_offset, r_cap, r_ucap: nat}{r_dynamic:bool}{l:addr}
  {o_len, o_offset, o_cap, o_ucap: nat}{o_refcnt: nat | o_refcnt > 0}{o_dynamic:bool}{l:addr}
  ( r: Bytestring_vtype( r_len, r_offset, r_cap, r_ucap, 1, r_dynamic, l)
  , o: Bytestring_vtype( o_len, o_offset, o_cap, o_ucap, o_refcnt, o_dynamic, l)
  ):<!wrt>
  Bytestring_vtype( o_len, o_offset, o_cap, o_ucap, o_refcnt - 1, o_dynamic, l)
  

overload free with unref_bs

fn
  isnot_shared
  {len,offset,cap,ucap,refcnt:nat}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype(len,offset,cap,ucap,refcnt,dynamic,l)
  ):<> bool( refcnt == 0)

fn
  is_shared
  {len,offset,cap,ucap,refcnt:nat}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype(len,offset,cap,ucap,refcnt,dynamic,l)
  ):<> bool( refcnt > 0)

fn
  isnot_dynamic
  {len,offset,cap,ucap,refcnt:nat}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype(len,offset,cap,ucap,refcnt,dynamic,l)
  ):<> bool( dynamic == false)

fn
  eq_bytestring_bytestring
  {l_len, r_len, l_offset, r_offset, l_cap, r_cap, l_ucap, r_ucap, l_refcnt, r_refcnt: nat}
  {l_dynamic,r_dynamic:bool}
  {l_p,r_p: addr}
  ( l: !Bytestring_vtype( l_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: !Bytestring_vtype( r_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p)
  ):<>
  [r: bool | (l_len == r_len && r ) || (l_len != r_len || r == false)]
  bool(r)

overload = with eq_bytestring_bytestring

fn
  neq_bytestring_bytestring
  {l_len, l_offset, l_cap, l_ucap, l_refcnt: nat}{l_dynamic:bool}{l_p:addr}
  {r_len, r_offset, r_cap, r_ucap, r_refcnt: nat}{r_dynamic:bool}{r_p:addr}
  ( l: !Bytestring_vtype( l_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: !Bytestring_vtype( r_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p)
  ):<> bool

overload <> with neq_bytestring_bytestring
overload != with neq_bytestring_bytestring


(* creates new bytestring with content of r appended to l. does not consumes l and r 
  in case if 'l' has enough unused capacity to fit 'r', it will copy content of 'r' into this unused space, incrementing reference counter of l and result
*)
fn
  append
  {l_len, l_offset, l_cap, l_ucap, l_refcnt: nat}{l_dynamic:bool}{l_p:addr}
  {r_len, r_offset, r_cap, r_ucap, r_refcnt: nat}{r_dynamic:bool}{r_p:addr}
  ( l: Bytestring_vtype(l_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: Bytestring_vtype(r_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p)
  ):<!wrt>
  [rr_ucap: nat | (l_len == 0 && l_ucap < r_len && rr_ucap == 0) || ((l_len > 0 || l_ucap >= r_len) && rr_ucap == r_ucap)]
  [rr_refcnt:nat | (l_len == 0 && l_ucap < r_len && rr_refcnt == r_refcnt + 1) || ((l_len > 0 || l_ucap >= r_len) && rr_refcnt == r_refcnt )]
  [rl_ucap: nat | (l_ucap >= r_len && rl_ucap == 0) || (l_ucap < r_len && rl_ucap == l_ucap)]
  [rl_refcnt:nat | (l_ucap >= r_len && rl_refcnt == l_refcnt + 1) || (l_ucap < r_len && rl_refcnt == l_refcnt )]
  [offset:nat | (l_ucap >= r_len && offset == l_offset) || (l_len == 0 && l_ucap < r_len && offset == r_offset) || (l_ucap < r_len && offset == 0)]
  [cap:nat | ( l_ucap >= r_len && cap == l_cap) || (l_len == 0 && l_ucap < r_len && cap == r_cap) || (l_ucap < r_len && cap == l_len + r_len)]
  [ucap:nat | (l_ucap >= r_len && ucap == l_ucap - r_len) || (l_len == 0 && l_ucap < r_len && ucap == r_ucap) || (l_len > 0 && l_ucap < r_len && ucap == 0)]
  [refcnt:nat | (l_ucap >= r_len && refcnt == 1) || (l_len == 0 && l_ucap < r_len && refcnt == 1) || (l_len > 0 && l_ucap < r_len && refcnt == 0)]
  [dynamic:bool | (l_ucap >= r_len && dynamic == l_dynamic) || (l_len == 0 && l_ucap < r_len && dynamic == r_dynamic) || (l_len > 0 && l_ucap < r_len && dynamic == true) ]
  [l:addr | (l_ucap >= r_len && l == l_p) || (l_len == 0 && l_ucap < r_len && l == r_p) || (l_len > 0 && l_ucap < r_len && l > null) ]
  ( Bytestring_vtype( l_len, l_offset, l_cap, rl_ucap, rl_refcnt, l_dynamic, l_p)
  , Bytestring_vtype( r_len, r_offset, r_cap, rr_ucap, rr_refcnt, r_dynamic, r_p)
  , Bytestring_vtype( l_len+r_len, offset, cap, ucap, refcnt, dynamic, l)
  )

(* the same as append, but consumes arguments in order to make caller's code clear from bunch of val's and free()
 *)
fn
  appendC
  {l_len, l_offset, l_cap, l_ucap: nat}{l_dynamic:bool}{l_p:addr}
  {r_len, r_offset, r_cap, r_ucap: nat}{r_dynamic:bool}{r_p:addr}
  ( l: Bytestring_vtype(l_len, l_offset, l_cap, l_ucap, 0, l_dynamic, l_p)
  , r: Bytestring_vtype(r_len, r_offset, r_cap, r_ucap, 0, r_dynamic, r_p)
  ):<!wrt>
  [offset:nat | (l_ucap >= r_len && offset == l_offset) || (l_len == 0 && l_ucap < r_len && offset == r_offset) || (l_ucap < r_len && offset == 0)]
  [cap:nat | (l_ucap >= r_len && cap == l_cap) || (l_len == 0 && l_ucap < r_len && cap == r_cap) || (l_ucap < r_len && cap == l_len + r_len)]
  [ucap:nat | (l_ucap >= r_len && ucap == l_ucap - r_len) || (l_len == 0 && l_ucap < r_len && ucap == r_ucap) || (l_ucap < r_len && ucap == 0)]
  [dynamic:bool | (l_ucap >= r_len && dynamic == l_dynamic) || (l_len == 0 && l_ucap < r_len && dynamic == r_dynamic) || (l_ucap < r_len && dynamic == true) ]
  [l:addr | (l_ucap >= r_len && l == l_p) || (l_len == 0 && l_ucap < r_len && l == r_p) || (l_len > 0 && l_ucap < r_len && l > null) ]
  Bytestring_vtype( l_len+r_len, offset, cap, ucap, 0, dynamic, l)

overload + with appendC

fn
  capacity
  { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  ):<> size_t( cap)

fn
  unused_capacity
  { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  ):<> size_t( ucap)

fn
  length_bs
  { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  ):<> size_t(len)
overload length with length_bs

(*
  1. 
  val a = create(100)
  val b = a + pack "hello"
  val c = b + pack " world"
  2.
  val a = create(100)
  val b = a + pack "hello"
  val c = take 2 b
  val d = b + pack " world"
  3.
  val a = create(100)
  val b = a + pack "hello"
  val c = take 2 b
  val d = b + pack " world"
*)

fn
  ref_bs_child
  { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
  ( i: Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  ):<!wrt>
  ( Bytestring_vtype( len, offset, cap, 0, refcnt + 1, dynamic, l)
  , Bytestring_vtype( len, offset, cap, ucap, 1, dynamic, l)
  )
fn
  ref_bs_parent
  { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
  ( i: Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  ):<!wrt>
  ( Bytestring_vtype( len, offset, cap, ucap, refcnt + 1, dynamic, l)
  , Bytestring_vtype( len, offset, cap, 0, 1, dynamic, l)
  )


fn
  is_empty
  { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  ):<> bool( len == 0)

fn
  isnot_empty
  { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  ):<> bool( len > 0)

(* creates uninitialized bytestring with given capacity *) 
fn
  create
  {cap: pos}
  ( capacity: size_t(cap)
  ):<!wrt>
  [l:agz]
  Bytestring_vtype(0, 0, cap, cap, 0, true, l)

fn
  take
  {n:nat}
  {len, offset, cap, ucap, refcnt: nat}{dynamic:bool}{l:addr}
  ( n: size_t n
  , i: Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  ):<!wrt>
  [newl: nat | (n <= len && newl == n) || (n > len && newl == len)]
  ( Bytestring_vtype( len, offset, cap, ucap, refcnt + 1, dynamic, l)
  , Bytestring_vtype( newl, offset, cap, 0, 1, dynamic, l)
  )
  
fn
  takeC
  {n:nat}
  {len, offset, cap, ucap: nat}{dynamic:bool}{l:addr}
  ( n: size_t n
  , i: Bytestring_vtype( len, offset, cap, ucap, 0, dynamic, l)
  ):<!wrt>
  [newl: nat | (n <= len && newl == n) || (n > len && newl == len)]
  Bytestring_vtype( newl, offset, cap, 0, 0, dynamic, l)

fn
  drop
  {n:nat}
  {len, offset, cap, ucap, refcnt: nat}{dynamic:bool}{l:addr}
  ( n: size_t n
  , i: Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  ):<!wrt>
  [newl: nat | (n <= len && newl == len - n) || (n > len && newl == 0)]
  [newoffset: nat | (n <= len && newoffset == offset + n) || (n > len && newoffset == 0)  ]
  ( Bytestring_vtype( len, offset, cap, 0, refcnt + 1, dynamic, l)
  , Bytestring_vtype( newl, newoffset, cap, ucap, 1, dynamic, l)
  )
  
fn
  dropC
  {n:nat}
  {len, offset, cap, ucap: nat}{dynamic:bool}{l:addr}
  ( n: size_t n
  , i: Bytestring_vtype( len, offset, cap, ucap, 0, dynamic, l)
  ):<!wrt>
  [newl: nat | (n <= len && newl == len - n) || (n > len && newl == 0)]
  [newoffset: nat | (n <= len && newoffset == offset + n) || (n > len && newoffset == 0)  ]
  Bytestring_vtype( newl, newoffset, cap, ucap, 0, dynamic, l)

fn
  println
  ( i: !Bytestring1
  ): void

fn
  printlnC
  ( i: BytestringNSH1
  ): void

fn
  bs2bytes
  {n,offset,cap,ucap: nat | cap > 0; cap >= n}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype(n,offset,cap,ucap,0,dynamic,l) >> minus_vt( Bytestring_vtype(n,offset,cap,ucap,0,dynamic,l), bytes(n) @ l1)
  ):<>
  #[l1:agz]
  ( bytes(n) @ l1
  | ptr l1
  , size_t(n)
  )

(* 

 

fn
  pack_bytes
  {n:nat}{l:agz}
  ( !bytes(n) @ l
  | i: ptr l
  , sz: size_t n
  ):
  Bytestring( n, n)

overload pack with pack_chars

(*
  1.
  val s = $BS.pack "hello"
  val h = $BS.take( 1, s) (* R(s) = 1, R(h) = 0 *)
  val h1 = $BS.take(1, h) (* now R(s) = 1, R(h) = 1, R(h1) = 0*)
  val () = $BS.free( h1, h) (* h1 freed, R(h) = 0 *)
  val () = $BS.free( h, s) (* h freed, R(s) = 0 *)
  val () = $BS.free(s)
  2.
  val buf = create 1000 (* R(buf) = 0 *)
  val s = $BS.appendC( buf, $BS.pack "he") (* R(s) = 0 *)
  val s1 = s + $BS.pack "llo" (* R(s1) = 0 *)
  val $BS.free( s1)
  3.
  val buf = create 10 (* R(buf) = 0,U(buf) = 10 *)
  val he = $BS.pack "he" (* R(he) = 0, U(he)=0 *)
  val s = $BS.append( buf, he) (* R(s) = 0, U(s) = 8 (s is the tail of busy buffer)R(buf) = 1, U(buf) = 0(buf is not the tail of busy buffer), R(he) = 0 *)
  val s1 = $BS.append( s, he) (* R(s) = 1, U(s) = 0 (not tail), R(he) = 0, R(s1) = 0, U(s1) = 6 *)
  val s2 = $BS.append( s, he) (*creates new buffer, because R(s) > 0 *)
  (* val s3 = $BS.take( 2, s1) (* R(s1) = 1, R(s3) = 0 *)
    val s4 = $BS.append( s1, he)
  *)
  4.
  var buf @[bytes][1024] with buf_pf
  val sz = recvfrom( fd, addr@buf, 1024)
  val bs = $BS.pack( buf_pf | buf, sz)
  val () = handle_packet( bs)
  val () = $BS.free( buf_pf | buf, bs)
*)

fn
  copy
  {n,cap,refcnt: nat | cap >= n}
  ( i: !Bytestring(n,cap,refcnt)
  ):
  Bytestring( n, cap, 0)


fn
  bs2ptr
  {n,cap: nat | cap > 0}
  ( i: !Bytestring(n,cap)
  ): [l:agz] ptr l
fn
  bs2string
  {n,cap: nat | cap > 0}
  ( i: !Bytestring(n,cap)
  ): string(n)
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

*)