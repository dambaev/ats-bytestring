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
  BytestringSH(len:int) =
  {len: nat}[offset,cap,ucap,refcnt:nat][dynamically_allocated:bool][l:agz]
  Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamically_allocated,l)

vtypedef
  BytestringNSH(len:int) =
  {len: nat}[offset,cap,ucap:nat][dynamically_allocated:bool][l:agz]
  Bytestring_vtype( len, offset, cap, ucap, 0, dynamically_allocated,l)
  
vtypedef
  BytestringNSH0 =
  [len: nat][offset,cap,ucap:nat][dynamically_allocated:bool][l:addr]
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
  [ ( n > 0 && l > null)
  ; (cap > 0 && l > null)
  ; (l > null && n >= 0); n+offset <= cap
  ; offset+n+ucap == cap
  ; (ucap == cap - offset - n || ucap == 0)
  ] (* n should not exceed capacity *)
  void

(* O(1)
  creates an empty bytestring
 *)
fn
  empty
  (
  ):<>
  Bytestring_vtype(0,0,0,0,0,false,null)

(**
 * Packing functions
 *)

(* O(1)
 *)
fn
  pack_string
  {n:nat}
  ( s: string(n)
  ):<!wrt>
  [l:agz]
  Bytestring_vtype(n,0,n,0,0,false,l)

symintr pack
overload pack with pack_string

(* O(1)
 *)
fn
  pack_chars_static
  {n,cap:nat | cap >= n}{l:agz}{a:t0ype}
  ( !array_v( a, l, cap) >> Bytestring_v(a, n, 0, cap, cap - n, 0, false, l)
  | i: ptr l
  , sz: size_t n
  , capacity: size_t cap
  ):<!wrt>
  Bytestring_vtype( n, 0, cap, cap - n, 0, false, l)

overload pack with pack_chars_static

(* O(1)
 *)
fn
  pack_chars_dynamic
  {n,cap:nat | cap >= n}{l:agz}{a:t0ype}
  ( array_v( a, l, cap)
  , mfree_gc_v l
  | i: ptr l
  , sz: size_t n
  , capacity: size_t cap
  ):<!wrt>
  Bytestring_vtype( n, 0, cap, cap - n, 0, true, l)

overload pack with pack_chars_dynamic

(* O(1) *)
fn
  pack_char
  ( a: char
  ):<!wrt>
  [l:addr | l > null]
  Bytestring_vtype( 1, 0, 1, 0, 0, true, l)
overload pack with pack_char

(* O(1) *)
fn
  pack_double
  ( i: double
  ):<!wrt>
  [len,cap:pos | cap >= len][ucap:nat][l:addr | l > null]
  Bytestring_vtype( len, 0, cap, ucap, 0, true, l)
overload pack with pack_double

(* O(1) *)
fn
  pack_float
  ( i: float
  ):<!wrt>
  [len,cap:pos | cap >= len][ucap:nat][l:addr | l > null]
  Bytestring_vtype( len, 0, cap, ucap, 0, true, l)
overload pack with pack_float

(* O(1) *)
fn
  pack_int8
  ( i: int8
  ):<!wrt>
  [len,cap:pos | cap >= len][ucap:nat][l:addr | l > null]
  Bytestring_vtype( len, 0, cap, ucap, 0, true, l)
overload pack with pack_int8

(* O(1) *)
fn
  pack_uint8
  ( i: uint8
  ):<!wrt>
  [len,cap:pos | cap >= len][ucap:nat][l:addr | l > null]
  Bytestring_vtype( len, 0, cap, ucap, 0, true, l)
overload pack with pack_uint8

(* O(1) *)
fn
  pack_int16
  ( i: int16
  ):<!wrt>
  [len,cap:pos | cap >= len][ucap:nat][l:addr | l > null]
  Bytestring_vtype( len, 0, cap, ucap, 0, true, l)
overload pack with pack_int16

(* O(1) *)
fn
  pack_uint16
  ( i: uint16
  ):<!wrt>
  [len,cap:pos | cap >= len][ucap:nat][l:addr | l > null]
  Bytestring_vtype( len, 0, cap, ucap, 0, true, l)
overload pack with pack_uint16

(* O(1) *)
fn
  pack_int32
  ( i: int32
  ):<!wrt>
  [len,cap:pos | cap >= len][ucap:nat][l:addr | l > null]
  Bytestring_vtype( len, 0, cap, ucap, 0, true, l)
overload pack with pack_int32

(* O(1) *)
fn
  pack_uint32
  ( i: uint32
  ):<!wrt>
  [len,cap:pos | cap >= len][ucap:nat][l:addr | l > null]
  Bytestring_vtype( len, 0, cap, ucap, 0, true, l)
overload pack with pack_uint32

(* O(1) *)
fn
  pack_uint64
  ( i: uint64
  ):<!wrt>
  [len,cap:pos | cap >= len][ucap:nat][l:addr | l > null]
  Bytestring_vtype( len, 0, cap, ucap, 0, true, l)
overload pack with pack_uint64

(* O(1) *)
fn
  pack_int64
  ( i: int64
  ):<!wrt>
  [len,cap:pos | cap >= len][ucap:nat][l:addr | l > null]
  Bytestring_vtype( len, 0, cap, ucap, 0, true, l)
overload pack with pack_int64

(* O(1) *)
fn
  pack_bool
  ( i: bool
  ):<!wrt>
  [len,cap:pos | cap >= len][ucap:nat][l:addr | l > null]
  Bytestring_vtype( len, 0, cap, ucap, 0, true, l)
overload pack with pack_bool

(* O(1)
 *)
fn
  free_static
  {len, offset, cap, ucap: nat}{l:addr}
  ( v: Bytestring_vtype(len, offset, cap, ucap, 0, false, l)
  ):<> void

(* O(1)
 *)
fn
  free_dynamic
  {len, offset, cap, ucap: nat}{l:addr}
  ( v: Bytestring_vtype(len, offset, cap, ucap, 0, true, l)
  ):<!wrt> void

(* O(1)
 *)
fn
  free_bs
  {len, offset, cap, ucap: nat}{dynamic:bool}{l:addr}
  ( i: Bytestring_vtype( len, offset, cap, ucap, 0, dynamic, l)
  ):<!wrt> void

symintr free
overload free with free_bs

(* O(1)
 *)
fn
  free_static_array
  {a:t0ype}
  {len, offset, cap, ucap: nat}{l:addr}
  ( !Bytestring_v(a, len, offset, cap, ucap, 0, false, l) >> array_v( a, l, cap)
  | i: Bytestring_vtype( len, offset, cap, ucap, 0, false, l)
  ): void

overload free with free_static_array

(* O(1)
 *)
fn
  unref_bs
  {r_len, r_offset, r_cap, r_ucap: nat}{r_dynamic:bool}{l:addr}
  {o_len, o_offset, o_cap, o_ucap: nat}{o_refcnt: nat | o_refcnt > 0}{o_dynamic:bool}{l:addr}
  ( consume: Bytestring_vtype( r_len, r_offset, r_cap, r_ucap, 1, r_dynamic, l)
  , preserve: !Bytestring_vtype( o_len, o_offset, o_cap, o_ucap, o_refcnt, o_dynamic, l) >> Bytestring_vtype( o_len, o_offset, o_cap, o_ucap, o_refcnt - 1, o_dynamic, l)
  ):<!wrt>
  void
  

overload free with unref_bs

(* O(1)
 *)
fn
  isnot_dynamic
  {len,offset,cap,ucap,refcnt:nat}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype(len,offset,cap,ucap,refcnt,dynamic,l)
  ):<> bool( dynamic == false)

(* O(l_len + r_len)
 *)
fn
  eq_bytestring_bytestringC
  {l_len, r_len, l_offset, r_offset, l_cap, r_cap, l_ucap, r_ucap, l_refcnt: nat}
  {l_dynamic,r_dynamic:bool}
  {l_p,r_p: addr}
  ( l: !Bytestring_vtype( l_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: Bytestring_vtype( r_len, r_offset, r_cap, r_ucap, 0, r_dynamic, r_p)
  ):<!wrt>
  [r: bool | (l_len == r_len && r ) || (l_len != r_len || r == false)]
  bool(r)

(* O(l_len + r_len)
 *)
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

(* O(l_len + r_len)
 *)
fn
  neq_bytestring_bytestring
  {l_len, l_offset, l_cap, l_ucap, l_refcnt: nat}{l_dynamic:bool}{l_p:addr}
  {r_len, r_offset, r_cap, r_ucap, r_refcnt: nat}{r_dynamic:bool}{r_p:addr}
  ( l: !Bytestring_vtype( l_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: !Bytestring_vtype( r_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p)
  ):<> bool

(* O(l_len + r_len)
 *)
fn
  neq_bytestring_bytestringC
  {l_len, l_offset, l_cap, l_ucap, l_refcnt: nat}{l_dynamic:bool}{l_p:addr}
  {r_len, r_offset, r_cap, r_ucap: nat}{r_dynamic:bool}{r_p:addr}
  ( l: !Bytestring_vtype( l_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: Bytestring_vtype( r_len, r_offset, r_cap, r_ucap, 0, r_dynamic, r_p)
  ):<!wrt> bool

(* O(l_len + r_len) 
  creates new bytestring with content of r appended to l. does not consumes l and r 
  this function is always creates new Bytestring
*)
fn
  append_bs_bs
  {l_len, l_offset, l_cap, l_ucap, l_refcnt: nat | l_len > 0}{l_dynamic:bool}{l_p:agz}
  {r_len, r_offset, r_cap, r_ucap, r_refcnt: nat | r_len > 0}{r_dynamic:bool}{r_p:agz}
  ( l: !Bytestring_vtype(l_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: !Bytestring_vtype(r_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p)
  ):<!wrt>
  #[l:addr | l > null]
  Bytestring_vtype( l_len+r_len, 0, l_len+r_len, 0, 0, true, l)
overload append with append_bs_bs

(* O(l_len + r_len) 
  creates new bytestring with content of r appended to l. does not consumes l and r 
  this function is always creates new Bytestring
*)
fn
  append_bs_bsC
  {l_len, l_offset, l_cap, l_ucap, l_refcnt: nat | l_len > 0}{l_dynamic:bool}{l_p:agz}
  {r_len, r_offset, r_cap, r_ucap: nat | r_len > 0}{r_dynamic:bool}{r_p:agz}
  ( l: !Bytestring_vtype(l_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: Bytestring_vtype(r_len, r_offset, r_cap, r_ucap, 0, r_dynamic, r_p)
  ):<!wrt>
  #[l:addr | l > null]
  Bytestring_vtype( l_len+r_len, 0, l_len+r_len, 0, 0, true, l)
overload append with append_bs_bsC

(* O(l_len + r_len) 
  creates new bytestring with content of r appended to l. does not consumes l and r 
  this function is always creates new Bytestring
*)
fn
  append_bsC_bs
  {l_len, l_offset, l_cap, l_ucap: nat | l_len > 0}{l_dynamic:bool}{l_p:agz}
  {r_len, r_offset, r_cap, r_ucap, r_refcnt: nat | r_len > 0}{r_dynamic:bool}{r_p:agz}
  ( l: Bytestring_vtype(l_len, l_offset, l_cap, l_ucap, 0, l_dynamic, l_p)
  , r: !Bytestring_vtype(r_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p)
  ):<!wrt>
  #[l:addr | l > null]
  Bytestring_vtype( l_len+r_len, 0, l_len+r_len, 0, 0, true, l)
overload append with append_bsC_bs

(* O(n + 1)
   creates new Bytestring with appending given character into the end of it
*)
fn
  append_bs_char
  {len, offset, cap, ucap, refcnt: nat}{dynamic:bool}{p:addr}
  ( l: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, p)
  , a: char
  ):<!wrt>
  [r_p:addr | r_p > null]
  Bytestring_vtype(len + 1, 0, len + 1, 0, 0, true, r_p)
overload append with append_bs_char

(* O(n + 1)
   creates new Bytestring with appending given character into the end of it
*)
fn
  append_char_bs
  {len, offset, cap, ucap, refcnt: nat}{dynamic:bool}{p:addr}
  ( a: char
  , l: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, p)
  ):<!wrt>
  [r_p:addr | r_p > null]
  Bytestring_vtype(len + 1, 0, len + 1, 0, 0, true, r_p)
overload append with append_char_bs

(* the same as append, but consumes arguments in order to make caller's code clear from bunch of val's and free()
 *)
fn
  appendC_bs_bs
  {l_len, l_offset, l_cap, l_ucap: nat | l_len > 0}{l_dynamic:bool}{l_p:agz}
  {r_len, r_offset, r_cap, r_ucap: nat | r_len > 0}{r_dynamic:bool}{r_p:agz}
  ( l: Bytestring_vtype(l_len, l_offset, l_cap, l_ucap, 0, l_dynamic, l_p)
  , r: Bytestring_vtype(r_len, r_offset, r_cap, r_ucap, 0, r_dynamic, r_p)
  ):<!wrt>
  [l:addr | l > null]
  Bytestring_vtype( l_len+r_len, 0, l_len+r_len, 0, 0, true, l)
overload appendC with appendC_bs_bs

(* O(n + 1)
   creates new Bytestring with appending given character into the end of it
*)
fn
  appendC_bs_char
  {len, offset, cap, ucap: nat}{dynamic:bool}{p:addr}
  ( l: Bytestring_vtype( len, offset, cap, ucap, 0, dynamic, p)
  , a: char
  ):<!wrt>
  [r_p:addr | r_p > null]
  Bytestring_vtype(len + 1, 0, len + 1, 0, 0, true, r_p)
overload appendC with appendC_bs_char

(* O(n + 1)
   creates new Bytestring with appending given character into the end of it
*)
fn
  appendC_char_bs
  {len, offset, cap, ucap: nat}{dynamic:bool}{p:addr}
  ( a: char
  , l: Bytestring_vtype( len, offset, cap, ucap, 0, dynamic, p)
  ):<!wrt>
  [r_p:addr | r_p > null]
  Bytestring_vtype(len + 1, 0, len + 1, 0, 0, true, r_p)
overload appendC with appendC_char_bs

(* O(r_len)
 this function appends 'r' at the end of 'l''s unused buffer.
 See test17 for example of usage.\
 this usage does not perform allocation, but does consumes 'r', so it will call 'free' in case if 'r' had been dynamically allocated.
 *)
fn
  growC 
  {r_len, r_offset, r_cap, r_ucap, l_refcnt: nat | r_len > 0}{r_dynamic:bool}{r_p:agz}
  {l_len, l_offset, l_cap, l_ucap: nat | l_ucap >= r_len }{l_dynamic:bool}{l_p:agz}
  ( l: Bytestring_vtype(l_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: Bytestring_vtype(r_len, r_offset, r_cap, r_ucap, 0, r_dynamic, r_p)
  ):<!wrt>
  Bytestring_vtype( l_len+r_len, l_offset, l_cap, l_ucap - r_len, l_refcnt, l_dynamic, l_p)

(* O(1)
 *)
fn
  capacity
  { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  ):<> size_t( cap)

(* O(1)
 *)
fn
  length_bs
  { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  ):<> size_t(len)

(* O(1)
 *)
fn
  ref_bs_child
  { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l) >> Bytestring_vtype( len, offset, cap, 0, refcnt + 1, dynamic, l)
  ):<!wrt>
  Bytestring_vtype( len, offset, cap, ucap, 1, dynamic, l)

(* O(1)
 *)
fn
  ref_bs_parent
  { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l) >> Bytestring_vtype( len, offset, cap, ucap, refcnt + 1, dynamic, l)
  ):<!wrt>
  Bytestring_vtype( len, offset, cap, 0, 1, dynamic, l)


(* O(1)
 *)
fn
  is_empty
  { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  ):<> bool( len == 0)

(* O(1)
 *)
fn
  isnot_empty
  { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  ):<> bool( len > 0 && l > null)

(* O(1)
 *)
(* creates uninitialized bytestring with given capacity *) 
fn
  create
  {cap: pos}
  ( capacity: size_t(cap)
  ):<!wrt>
  [l:agz]
  Bytestring_vtype(0, 0, cap, cap, 0, true, l)

(* O(1)
 *)
fn
  take
  {n:nat}
  {len, offset, cap, ucap, refcnt: nat | len >= n}{dynamic:bool}{l:addr}
  ( n: size_t n
  , i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l) >> Bytestring_vtype( len, offset, cap, ucap, refcnt + 1, dynamic, l)
  ):<!wrt>
  Bytestring_vtype( n, offset, cap, 0, 1, dynamic, l)
  
(* O(1)
 *)
fn
  takeC
  {n:nat}
  {len, offset, cap, ucap, refcnt: nat | len >= n}{dynamic:bool}{l:addr}
  ( n: size_t n
  , i: Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  ):<!wrt>
  [newucap: nat | (n == len && newucap == ucap) || (n < len && newucap == 0)]
  Bytestring_vtype( n, offset, cap, newucap, refcnt, dynamic, l)

(* O(1)
 *)
fn
  drop
  {n:nat}
  {len, offset, cap, ucap, refcnt: nat | len >= n}{dynamic:bool}{l:addr}
  ( n: size_t n
  , i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l) >> Bytestring_vtype( len, offset, cap, 0, refcnt + 1, dynamic, l)
  ):<!wrt>
  Bytestring_vtype( len - n, offset + n, cap, ucap, 1, dynamic, l)
  
(* O(1)
 *)
fn
  dropC
  {n:nat}
  {len, offset, cap, ucap, refcnt: nat | len >= n}{dynamic:bool}{l:addr}
  ( n: size_t n
  , i: Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  ):<!wrt>
  Bytestring_vtype( len - n, offset + n, cap, ucap, refcnt, dynamic, l)

(* O(n)
 *)
fn
  println
  ( i: !Bytestring1
  ): void

(* O(n)
 *)
fn
  eprintln
  ( i: !Bytestring1
  ): void

(* O(n)
 *)
fn
  eprintlnC
  ( i: BytestringNSH1
  ): void

(* O(n)
 *)
fn
  printlnC
  ( i: BytestringNSH1
  ): void

(* O(1)
 *)
fn
  bs2bytes
  {len,offset,cap,ucap,refcnt: nat | cap > 0}{dynamic:bool}{l:agz}
  ( i: !Bytestring_vtype(len,offset,cap,ucap,refcnt,dynamic,l) >> minus_vt( Bytestring_vtype(len,offset,cap,ucap,refcnt,dynamic,l), array_v(char, l+offset*sizeof(char), len))
  ):<>
  [ l+offset*sizeof(char) > null]
  ( array_v(char, l+offset*sizeof(char), len)
  | ptr (l+offset*sizeof(char))
  , size_t(len)
  )

(* O(1)
 *)
praxi
  bytes_addback
  {len,offset,cap,ucap,refcnt: nat | cap > 0}{dynamic:bool}{l:addr}
  ( array_v(char, l+offset*sizeof(char), len)
  | i: !minus_vt( Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l), array_v(char, l+offset*sizeof(char), len)) >> Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  ):<>
  void

(* O(1) *)
fn
  bs2unused_bytes
  {len,offset,cap,refcnt: nat | cap - offset - len > 0}{dynamic:bool}{l:agz}
  ( i: !Bytestring_vtype(len,offset,cap,cap - offset - len,refcnt,dynamic,l) >> minus_vt( Bytestring_vtype(len,offset,cap,cap - offset - len,refcnt,dynamic,l), array_v(char, l+(offset+len)*sizeof(char), cap - offset - len))
  ):<>
  [ (l + (offset+len)*sizeof(char)) > null]
  ( array_v(char, l+(offset+len)*sizeof(char), cap - offset - len)
  | ptr (l+(offset+len)*sizeof(char))
  , size_t(cap - offset - len)
  )

(* O(1) *)
fn
  unused_bytes_addback
  {len,offset,cap,ucap,refcnt,used_bytes: nat | ucap > 0; used_bytes <= ucap}{dynamic:bool}{l:agz}
  ( array_v(char, l+(offset+len)*sizeof(char), ucap)
  | i: &minus_vt( Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l), array_v(char, l+(offset+len)*sizeof(char), ucap)) >> Bytestring_vtype( len + used_bytes, offset, cap, ucap - used_bytes, refcnt, dynamic, l)
  , used_bytes: size_t( used_bytes)
  ):<!wrt>
  void

(* O(1)
 *)
fn
  take1
  {len,offset,cap,ucap,refcnt,n: nat}{dynamic:bool}{l:addr}
  ( n: size_t n
  , i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l) >> Bytestring_vtype(len, offset, cap, ucap, refcnt + 1, dynamic, l)
  ):<!wrt>
  [newlen: nat | (n >= len && newlen == len) || (n < len && newlen == n)]
  Bytestring_vtype( newlen, offset, cap, 0, 1, dynamic, l)

(* O(1)
 *)
fn
  decref_bs
  {c_len,c_offset,cap,c_ucap: nat}{dynamic:bool}{l:addr}
  {p_len,p_offset,p_ucap,p_refcnt: nat | p_refcnt > 0}
  ( consume: Bytestring_vtype( c_len, c_offset, cap, c_ucap, 1, dynamic, l)
  , preserve: !Bytestring_vtype( p_len, p_offset, cap, p_ucap, p_refcnt, dynamic, l) >> Bytestring_vtype( p_len, p_offset, cap, p_ucap, p_refcnt - 1, dynamic, l)
  ):<!wrt>
  void
  
(* O(1) *)
fn
  get_byte_at_uint
  {n,len,offset,cap,ucap,refcnt: nat | n < len}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  , n: size_t n
  ):<>
  char

(* O(1) *)
fn
  get_byte_at_int
  {n,len,offset,cap,ucap,refcnt: nat | n < len}{dynamic:bool}{l:agz}
  ( i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  , n: int n
  ):<>
  char

(* O(1) *)
fn
  get_char_at_uint
  {n,len,offset,cap,ucap,refcnt: nat | n < len}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  , n: size_t n
  ):<>
  char

(* O(1) *)
fn
  get_char_at_int
  {n,len,offset,cap,ucap,refcnt: nat | n < len}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  , n: int n
  ):<>
  char

(* O(1) *)
fn
  split_on
  {len,offset,cap,ucap,refcnt: nat}{dynamic:bool}{l:addr}
  ( delim: char
  , i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l) >> Bytestring_vtype( len, offset, cap, ucap, refcnt + cnt, dynamic, l)
  ):<!wrt>
  #[cnt:nat]
  list_vt( [olen, ooffset:nat] Bytestring_vtype( olen, ooffset, cap, 0, 1, dynamic, l), cnt)

(* O(olen) *)
fn
  {env:viewt0ype}
  take_while
  {len, offset, cap, ucap, refcnt: nat}{dynamic:bool}{l:addr}
  ( env: !env >> _
  , f: (!env, char)-<> bool
  , i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l) >> Bytestring_vtype( len, offset, cap, ucap, refcnt + 1, dynamic, l)
  ):<!wrt>
  [olen, ooffset: nat]
  Bytestring_vtype( olen, ooffset, cap, 0, 1, dynamic, l)
 
(* O(len) *)
fn
  copy
  {len,offset,cap,ucap,refcnt: nat | len > 0}{dynamic:bool}{l:agz}
  ( i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l) 
  ):<!wrt>
  [l1:agz]
  Bytestring_vtype( len, 0, len, 0, 0, true, l1)

(* O(len) *)
fn
  parse_uint32
  {len,offset,cap,ucap,refcnt: nat}{dynamic:bool}{l:addr}
  ( i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  ):<!wrt>
  Option_vt( uint32)

(* create a copy of the given bytestring with reversed content
  for usage, see test19
*)
(* O(len) *)
fn
  reverse
  {len,offset,cap,ucap,refcnt: nat | len > 0}{dynamic:bool}{l:agz}
  ( i: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  ):<!wrt>
  [l1:agz]
  Bytestring_vtype( len, 0, len, 0, 0, true, l1)

(* reverses the content of the string in-place. Requires the bytestring to be dynamically allocated, as writing to the statically allocated memory will cause a SEGFAULT
  for usage, see test19
*)
(* O(len), theta(len / 2) *)
fn
  reverseC
  {len,offset,cap,ucap: nat | len  > 0}{l:agz}
  ( i: Bytestring_vtype( len, offset, cap, ucap, 0, true, l)
  ):<!wrt>
  Bytestring_vtype( len, offset, cap, ucap, 0, true, l)