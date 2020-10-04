#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
#define ATS_PACKNAME "bytestring"
#define ATS_EXTERN_PREFIX "bytestring_"

staload "./../SATS/bytestring.sats"
staload UN = "prelude/SATS/unsafe.sats"
//staload "prelude/SATS/array.sats"

%{^
#include "unistd.h"
%}


typedef Bytestring_impl(len:int, offset: int, capacity: int, ucapacity: int, refcnt:int, dynamic: bool, l:addr) =
  @( size_t(len)
   , size_t(offset) (* offset from the base pointer of length len *)
   , size_t(capacity) (* size of buffer, starting from base pointer *)
   , size_t(ucapacity) (* size of buffer, unused by current bytestring *)
   , size_t(refcnt)
   , bool(dynamic)
   , ptr(l) (* pointer to base pointer *)
   )

absvtype Bs_minus_struct(n:int, offset:int, cap: int, ucap: int, refcnt:int, dynamic:bool, l:addr)

dataview result_vb(c:bool, a:view+,b: view+) =
  | fail_vb(false, a, b) of a
  | succ_vb(true, a, b) of b

extern castfn
  bs_explode
  {n,offset,cap,ucap,refcnt:nat}{dynamic:bool}{l:addr}
  ( bs: Bytestring_vtype(n,offset,cap,ucap,refcnt,dynamic,l)
  ):<>
  ( result_vb( l > null, void, (array_v(byte, l, cap), mfree_gc_v l))
  | Bytestring_impl(n, offset, cap, ucap, refcnt, dynamic, l)
  )

extern castfn
  bs_build
  {n,offset,cap,ucap,refcnt:nat}{dynamic:bool}{l:addr}
  ( result_vb( l > null, void, (array_v(byte, l, cap), mfree_gc_v l))
  | bs: Bytestring_impl(n, offset, cap, ucap, refcnt, dynamic, l)
  ):<> Bytestring_vtype(n,offset,cap,ucap,refcnt,dynamic,l)

extern castfn
  bs_takeout_struct
  {n,offset,cap,ucap,refcnt:nat}{dynamic:bool}{l:addr}
  ( bs: !Bytestring_vtype(n,offset,cap,ucap,refcnt,dynamic,l) >> Bs_minus_struct( n, offset, cap, ucap, refcnt, dynamic, l)
  ):<>
  ( result_vb( l > null, void, (array_v(byte, l, cap), mfree_gc_v l))
  | Bytestring_impl(n, offset, cap, ucap, refcnt, dynamic, l)
  )

extern praxi
  bs_takeback_struct
  {n,offset,cap,ucap,refcnt: nat}{l:addr}{dynamic:bool}
  ( result_vb( l > null, void, (array_v(byte,l,cap), mfree_gc_v l))
  | bs: !Bs_minus_struct( n, offset, cap, ucap, refcnt, dynamic, l) >> Bytestring_vtype( n, offset, cap, ucap, refcnt, dynamic, l)
  ):<> void

extern fn
  append_impl
  {l_len, l_offset, l_cap, l_ucap, l_refcnt: nat}{l_dynamic:bool}{l_p:addr}
  {r_len, r_offset, r_cap, r_ucap, r_refcnt: nat}{r_dynamic:bool}{r_p:addr}
  ( l: &Bytestring_vtype(l_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p) >> Bytestring_vtype( l_len, l_offset, l_cap, rl_ucap, rl_refcnt, l_dynamic, l_p)
  , r: &Bytestring_vtype(r_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p) >>Bytestring_vtype( r_len, r_offset, r_cap, rr_ucap, rr_refcnt, r_dynamic, r_p)
  ):<!wrt>
  #[rr_ucap: nat | (l_len == 0 && l_ucap < r_len && rr_ucap == 0) || ((l_len > 0 || l_ucap >= r_len) && rr_ucap == r_ucap)]
  #[rr_refcnt:nat | (l_len == 0 && l_ucap < r_len && rr_refcnt == r_refcnt + 1) || ((l_len > 0 || l_ucap >= r_len) && rr_refcnt == r_refcnt )]
  #[rl_ucap: nat | (l_ucap >= r_len && rl_ucap == 0) || (l_ucap < r_len && rl_ucap == l_ucap)]
  #[rl_refcnt:nat | (l_ucap >= r_len && rl_refcnt == l_refcnt + 1) || (l_ucap < r_len && rl_refcnt == l_refcnt )]
  #[offset:nat | (l_ucap >= r_len && offset == l_offset) || (l_len == 0 && l_ucap < r_len && offset == r_offset) || (l_ucap < r_len && offset == 0)]
  #[cap:nat | ( l_ucap >= r_len && cap == l_cap) || (l_len == 0 && l_ucap < r_len && cap == r_cap) || (l_ucap < r_len && cap == l_len + r_len)]
  #[ucap:nat | (l_ucap >= r_len && ucap == l_ucap - r_len) || (l_len == 0 && l_ucap < r_len && ucap == r_ucap) || (l_len > 0 && l_ucap < r_len && ucap == 0)]
  #[refcnt:nat | (l_ucap >= r_len && refcnt == 1) || (l_len == 0 && l_ucap < r_len && refcnt == 1) || (l_len > 0 && l_ucap < r_len && refcnt == 0)]
  #[dynamic:bool | (l_ucap >= r_len && dynamic == l_dynamic) || (l_len == 0 && l_ucap < r_len && dynamic == r_dynamic) || (l_len > 0 && l_ucap < r_len && dynamic == true) ]
  #[l:addr | (l_ucap >= r_len && l == l_p) || (l_len == 0 && l_ucap < r_len && l == r_p) || (l_len > 0 && l_ucap < r_len && l > null) ]
  Bytestring_vtype( l_len+r_len, offset, cap, ucap, refcnt, dynamic, l)

(* the same as append, but consumes arguments in order to make caller's code clear from bunch of val's and free()
 *)
extern fn
  appendC_impl
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

extern fn
  take_impl
  {n:nat}
  {len, offset, cap, ucap, refcnt: nat}{dynamic:bool}{l:addr}
  ( n: size_t n
  , i: &Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l) >> Bytestring_vtype( len, offset, cap, ucap, refcnt + 1, dynamic, l)
  ):<!wrt>
  [newl: nat | (n <= len && newl == n) || (n > len && newl == len)]
  Bytestring_vtype( newl, offset, cap, 0, 1, dynamic, l)
  
extern fn
  takeC_impl
  {n:nat}
  {len, offset, cap, ucap: nat}{dynamic:bool}{l:addr}
  ( n: size_t n
  , i: Bytestring_vtype( len, offset, cap, ucap, 0, dynamic, l)
  ):<!wrt>
  [newl: nat | (n <= len && newl == n) || (n > len && newl == len)]
  Bytestring_vtype( newl, offset, cap, 0, 0, dynamic, l)

extern fn
  drop_impl
  {n:nat}
  {len, offset, cap, ucap, refcnt: nat}{dynamic:bool}{l:addr}
  ( n: size_t n
  , i: &Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l) >> Bytestring_vtype( len, offset, cap, 0, refcnt + 1, dynamic, l)
  ):<!wrt>
  #[newl: nat | (n <= len && newl == len - n) || (n > len && newl == 0)]
  #[newoffset: nat | (n <= len && newoffset == offset + n) || (n > len && newoffset == 0)  ]
  Bytestring_vtype( newl, newoffset, cap, ucap, 1, dynamic, l)
  
extern fn
  dropC_impl
  {n:nat}
  {len, offset, cap, ucap: nat}{dynamic:bool}{l:addr}
  ( n: size_t n
  , i: Bytestring_vtype( len, offset, cap, ucap, 0, dynamic, l)
  ):<!wrt>
  [newl: nat | (n <= len && newl == len - n) || (n > len && newl == 0)]
  [newoffset: nat | (n <= len && newoffset == offset + n) || (n > len && newoffset == 0)  ]
  Bytestring_vtype( newl, newoffset, cap, ucap, 0, dynamic, l)

implement empty() = believeme( () | ( i2sz(0), i2sz(0), i2sz(0), i2sz(0), i2sz(0), false, the_null_ptr)) where {
  extern castfn
    believeme
    {n,offset,cap,ucap,refcnt:nat}{dynamic:bool}{l:addr}
    ( void
    | ( size_t(n)
      , size_t(offset)
      , size_t(cap)
      , size_t(ucap)
      , size_t(refcnt)
      , bool(dynamic)
      , ptr(l)
      )
    ):<>
    Bytestring_vtype(n, offset, cap, ucap, refcnt, dynamic, l)
}

implement pack_string{n}(s) =
let
  val sz = length(s)
  extern castfn
    believeme
    {n,offset,cap,ucap,refcnt:nat}{dynamic:bool}{l:agz}
    ( void
    | ( size_t(n)
      , size_t(offset)
      , size_t(cap)
      , size_t(ucap)
      , size_t(refcnt)
      , bool(dynamic)
      , ptr(l)
      )
    ):<>
    Bytestring_vtype(n, offset, cap, ucap, refcnt, dynamic, l)
  extern castfn
    string2ptr_
    {n:nat}
    ( s: string(n)
    ):
    [l:agz]
    ptr l
  val p = string2ptr_ s
in
  believeme( () | (sz, i2sz(0), sz, i2sz(0), i2sz(0), false, p)) 
end

implement free_bs(i) =
  if isnot_dynamic i
  then free_static i
  else free_dynamic i
  
implement free_static(i) = {
  extern castfn
    takeout
    {len, offset, cap, ucap: nat}{dynamic:bool}{l:addr}
    ( i: Bytestring_vtype( len, offset, cap, ucap, 0, false, l)
    ):<> Bytestring_impl( len, offset, cap, ucap, 0, false, l)
  val impl = takeout( i)
}

implement free_dynamic(i) = {
  extern castfn
    takeout
    {len, offset, cap, ucap: nat}{dynamic:bool}{l:addr}
    ( i: Bytestring_vtype( len, offset, cap, ucap, 0, true, l)
    ):<>
    [n:nat]
    ( array_v(byte,l,cap), mfree_gc_v l | Bytestring_impl( len, offset, cap, ucap, 0, true, l))
  val (pf , fpf | (len, offset, cap, _, _, _, ptr)) = takeout( i)
  val () = array_ptr_free( pf, fpf | ptr)
}

implement isnot_dynamic(i) = dynamic = false where {
  prval () = lemma_bytestring_param(i)
  val ( rpf | impl) = bs_takeout_struct( i)
  val (_, _,_,_,_, dynamic, _) = impl
  prval () = bs_takeback_struct( rpf | i)
}

implement isnot_shared(i) = refcnt = 0 where {
  val ( rpf | impl) = bs_takeout_struct( i)
  val (_, _,_,_, refcnt, _, _) = impl
  prval () = bs_takeback_struct( rpf | i)
}

implement is_shared(i) = refcnt > 0 where {
  val ( rpf | impl) = bs_takeout_struct( i)
  val (_, _,_,_, refcnt, _, _) = impl
  prval () = bs_takeback_struct( rpf | i)
}

extern fn
  memcmp
  {a:t0ype}
  { sizeof(a) == sizeof(char) || sizeof(a) == sizeof(byte)}
  { n,cap1,cap2:pos
  | n <= cap1 && n <= cap2
  }
  { l1,l2:agz}
  ( !array_v(a, l1, cap1)
  , !array_v(a, l2, cap2)
  | lp: ptr l1
  , rp: ptr l2
  , ln: size_t n
  ):<> int = "mac#"

fn
  {a:viewt0ype}
  ptr1_add_sz
  {l:agz}{n:nat}{sizeof(a) == sizeof(char) || sizeof(a) == sizeof(byte)}
  ( i: ptr l
  , n: size_t n
  ):<>
  [newl: agz | newl == l+n*sizeof(a)]
  ptr newl =
let
  val ret = ptr_add<a>(i, n)
  extern castfn
    believeme
    {l:addr}
    ( p: ptr l
    ):<>
    [l1:agz | l == l1]
    ptr l1
  
in
  believeme(ret)
end

implement eq_bytestring_bytestring {l_len, r_len, l_offset, r_offset, l_cap, r_cap, l_ucap, r_ucap, l_refcnt, r_refcnt}{l_dynamic,r_dynamic}{l_p,r_p}( l, r) =
let
  prval () = lemma_bytestring_param(l)
  prval () = lemma_bytestring_param(r)
  val ( r_rpf | (r_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p)) = bs_takeout_struct( r)
  val ( l_rpf | (l_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)) = bs_takeout_struct( l)
in
  ifcase
  | ptr_is_null r_p * ptr_is_null l_p => true where {
    prval _ = prop_verify {r_p == null } ()
    prval _ = prop_verify {l_p == null } ()
    prval () = bs_takeback_struct( r_rpf | r)
    prval () = bs_takeback_struct( l_rpf | l)
  }
  | r_len != l_len => false where {
    prval () = bs_takeback_struct( r_rpf | r)
    prval () = bs_takeback_struct( l_rpf | l)
  }
  | r_len = 0 => true where {
    prval () = bs_takeback_struct( r_rpf | r)
    prval () = bs_takeback_struct( l_rpf | l)
  }
  | sizeof<byte> <= 0 => false where {
    prval () = bs_takeback_struct( r_rpf | r)
    prval () = bs_takeback_struct( l_rpf | l)
  }
  | _ => ret where {
    val r_ptr = ptr1_add_sz<byte>( r_p, r_offset)
    val l_ptr = ptr1_add_sz<byte>( l_p, l_offset)
    prval succ_vb( rpf ) = r_rpf
    prval (r_pf, r_fpf) = rpf
    prval (r_pf1, r_pf2) = array_v_split_at( r_pf | r_offset)
    prval (r_pf21, r_pf22) = array_v_split_at( r_pf2 | r_len)
    prval succ_vb( lpf) = l_rpf
    prval (l_pf, l_fpf) = lpf
    prval (l_pf1, l_pf2) = array_v_split_at( l_pf | l_offset)
    prval (l_pf21, l_pf22) = array_v_split_at( l_pf2 | l_len)
    val ret = 
      if memcmp( r_pf21, l_pf21 | r_ptr, l_ptr, r_len) = 0
      then true
      else false
    prval () = r_pf := array_v_unsplit( r_pf1, array_v_unsplit( r_pf21, r_pf22))
    prval () = l_pf := array_v_unsplit( l_pf1, array_v_unsplit( l_pf21, l_pf22))
    prval () = r_rpf := succ_vb( (r_pf, r_fpf))
    prval () = l_rpf := succ_vb( (l_pf, l_fpf))
    prval () = bs_takeback_struct( r_rpf | r)
    prval () = bs_takeback_struct( l_rpf | l)
  }
  
end

implement pack_chars_static{n,cap}{l}{a}( pf | i, sz, capacity) =
let
  extern castfn
    believeme
    {offset,ucap,refcnt:nat}{dynamic:bool}{l:agz}
    ( !array_v( a, l, cap) >> Bytestring_v(a, n, offset, cap, ucap, refcnt, dynamic, l)
    | ( size_t(n)
      , size_t(offset)
      , size_t(cap)
      , size_t(ucap)
      , size_t(refcnt)
      , bool(dynamic)
      , ptr(l)
      )
    ):<>
    Bytestring_vtype(n, offset, cap, ucap, refcnt, dynamic, l)
in
  believeme( pf | (sz, i2sz 0, capacity, capacity - sz, i2sz 0, false, i))
end

implement free_static_array{a}{len,offset,cap,ucap}{l}( pf | i) = {
  prval () = lemma_bytestring_param( i)
  extern castfn
    believeme
    {refcnt:nat}{dynamic:bool}
    ( !Bytestring_v( a, len, offset, cap, ucap, refcnt, dynamic, l) >> array_v( a, l, cap)
    | i: Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
    ):<>
    ( size_t(len)
    , size_t(offset)
    , size_t(cap)
    , size_t(ucap)
    , size_t(refcnt)
    , bool(dynamic)
    , ptr(l)
    )
  val _ = believeme( pf | i) 
}

implement pack_chars_dynamic{n,cap}{l}{a}(pf, fpf | p, sz, capacity) =
let
  extern castfn
    believeme
    {offset,ucap,refcnt:nat}{dynamic:bool}{l:agz}
    ( array_v( a, l, cap)
    , mfree_gc_v l
    | ( size_t(n)
      , size_t(offset)
      , size_t(cap)
      , size_t(ucap)
      , size_t(refcnt)
      , bool(dynamic)
      , ptr(l)
      )
    ):<>
    Bytestring_vtype(n, offset, cap, ucap, refcnt, true, l)
in
  believeme( pf, fpf | (sz, i2sz 0, capacity, capacity - sz, i2sz 0, true, p))
end
  
implement 
  appendC_impl
  {l_len, l_offset, l_cap, l_ucap}{l_dynamic}{l_p}
  {r_len, r_offset, r_cap, r_ucap}{r_dynamic}{r_p}
  ( vl, vr) =
let
  var l: Bytestring0?
  var r: Bytestring0?
  val () = l := vl
  val () = r := vr
  val l_ucap = unused_capacity l
  val l_len = length l
  val r_len = length r
  var res: Bytestring0?
  val () = res := append_impl( l, r)
in
  ifcase
  | (l_len = 0) * (l_ucap < r_len) => res where {
    val () = free( r, res)
    val () = free l
  }
  | (l_ucap < r_len) => res where {
    prval _ = prop_verify {l_ucap < r_len}()
    val () = free r
    val () = free l
  }
  | _ => res where {
    val () = free r
    val () = free( l, res) 
  }
end

implement capacity(i) = cap where {
  prval () = lemma_bytestring_param( i)
  val ( rpf | (_, _, cap, _, _, _, _)) = bs_takeout_struct( i)
  prval () = bs_takeback_struct( rpf | i)
}

implement unused_capacity(i) = ucap where {
  prval () = lemma_bytestring_param( i)
  val ( rpf | (_, _, _, ucap, _, _, _)) = bs_takeout_struct( i)
  prval () = bs_takeback_struct( rpf | i)
}

implement length_bs(i) = len where {
  prval () = lemma_bytestring_param( i)
  val ( rpf | (len, _, _, _, _, _, _)) = bs_takeout_struct( i)
  prval () = bs_takeback_struct( rpf | i)
}

implement unref_bs( r, o) = {
  extern castfn
    explode
    {n,offset,cap,ucap,refcnt:nat}{dynamic:bool}{l:addr}
    ( bs: Bytestring_vtype(n,offset,cap,ucap,refcnt,dynamic,l)
    ):<>
    Bytestring_impl(n, offset, cap, ucap, refcnt, dynamic, l)
  prval () = lemma_bytestring_param( r)
  prval () = lemma_bytestring_param( o)
  val _ = explode( r) (* we know, that r is just reference to o. r should not survive and o should survive *)
  val ( rpf | impl ) = bs_explode( o)
  val ( len, offset, cap, ucap, refcnt, dynamic, l) = impl
  val () = o := bs_build( rpf | (len, offset, cap, ucap, refcnt - i2sz 1, dynamic, l))
}

extern fn
  memcpy
  {a:t0ype}{b:t0ype}
  {n,n1,n2:pos | n >= n1; n2 >= n1 }{l,l1:addr}
  ( !array_v(a?, l, n) >> array_v(a,l,n)
  , !array_v(b, l1, n2)
  | dst: ptr l
  , src: ptr l1
  , sz: size_t n1
  ):<!wrt> void = "mac#memcpy"

implement append_impl
  {l_len, l_offset, l_cap, l_ucap, l_refcnt}{l_dynamic}{l_p}
  {r_len, r_offset, r_cap, r_ucap, r_refcnt}{r_dynamic}{r_p}
  (l, r) =
let
  prval () = lemma_bytestring_param( l)
  prval () = lemma_bytestring_param( r)
  val r_len = length r
  val l_len = length l
  extern castfn
    explode
    { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
    ( i: Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
    ):<>
    ( size_t(len)
    , size_t(offset)
    , size_t(cap)
    , size_t(ucap)
    , size_t(refcnt)
    , bool(dynamic)
    , ptr(l)
    )
  extern castfn
    build
    { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
    ( void
    | ( size_t(len)
      , size_t(offset)
      , size_t(cap)
      , size_t(ucap)
      , size_t(refcnt)
      , bool(dynamic)
      , ptr(l)
      )
    ):<> Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
in
  ifcase
  | is_empty l * (unused_capacity l < r_len) => res where {
    val res = ref_bs_child r
  }
  | is_empty r => res where {
    val res = ref_bs_child l
  }
  (* create new buffer *)
  | unused_capacity l < r_len => res where {
    val res = create( l_len + r_len)
    val (res_rpf | impl) = bs_takeout_struct( res )
    val (res_len, res_offset, res_cap, res_ucap, res_refcnt, res_dynamic, res_p) = impl
    prval succ_vb( res_pf ) = res_rpf
    prval ( res_pf0, res_fpf) = res_pf
    prval (res_pf1, res_pf2) = array_v_split_at( res_pf0 | l_len)
    val (l_rpf | impl) = bs_takeout_struct( l )
    val (l_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p) = impl
    prval succ_vb( l_pf ) = l_rpf
    prval ( l_pf0, l_fpf) = l_pf
    prval (l_pf1, l_pf2) = array_v_split_at( l_pf0 | l_offset)
    prval (l_pf21, l_pf22) = array_v_split_at( l_pf2 | l_len)
    val l_ptr = ptr1_add_sz<byte>( l_p, l_offset)

    val () = memcpy( res_pf1, l_pf21 | res_p, l_ptr, l_len)
    
    prval () = l_pf2 := array_v_unsplit( l_pf21, l_pf22)
    prval () = l_pf0 := array_v_unsplit( l_pf1, l_pf2)
    prval () = l_rpf := succ_vb( (l_pf0, l_fpf))
    prval () = bs_takeback_struct( l_rpf | l)
    
    val res_ptr = ptr1_add_sz<byte>( res_p, l_len)
    
    val (r_rpf | impl) = bs_takeout_struct( r)
    val (r_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p) = impl
    val r_ptr = ptr1_add_sz<byte>( r_p, r_offset)
    prval succ_vb( r_pf) = r_rpf
    prval (r_pf0, r_fpf) = r_pf
    prval (r_pf1, r_pf2) = array_v_split_at( r_pf0 | r_offset)
    prval (r_pf21, r_pf22) = array_v_split_at( r_pf2 | r_len)
    
    val () = memcpy( res_pf2, r_pf21 | res_ptr, r_ptr, r_len)
  
    prval () = res_pf0 := array_v_unsplit( res_pf1, res_pf2)
    prval () = res_rpf := succ_vb( ( res_pf0, res_fpf))
  
    prval () = bs_takeback_struct( res_rpf | res)
    
    prval () = r_pf2 := array_v_unsplit( r_pf21, r_pf22)
    prval () = r_pf0 := array_v_unsplit( r_pf1, r_pf2)
    prval () = r_rpf := succ_vb( (r_pf0, r_fpf))
    
    prval () = bs_takeback_struct( r_rpf | r)
    
    val (res_len, res_offset, res_cap, res_ucap, res_refcnt, res_dynamic, res_l) = explode( res)
    val res = build( () | ( l_len + r_len, res_offset, res_cap, res_ucap - l_len - r_len, res_refcnt, res_dynamic, res_l))
  }
  (* reuse l's unused capacity *)
  | _ => res where {
    prval () = prop_verify {l_ucap >= r_len}()
    val res = ref_bs_child l
    val ( rpf | impl) = bs_takeout_struct( res)
    val (res_len, res_offset, res_cap, res_ucap, res_refcnt, res_dynamic, res_p) = impl
    prval succ_vb( rpf0 ) = rpf
    prval (pf, fpf) = rpf0
    prval (pf1, pf2) = array_v_split_at( pf | res_offset)
    prval (pf21, pf22) = array_v_split_at( pf2 | res_len)
    prval (pf221, pf222) = array_v_split_at( pf22 | r_len)
    val res_ptr = ptr1_add_sz<byte>( res_p, res_offset + res_len)
    
    val (r_rpf | r_impl) = bs_takeout_struct( r)
    val (r_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p) = r_impl
    
    prval succ_vb( r_pf0) = r_rpf
    prval ( r_pf, r_fpf) = r_pf0
    prval ( r_pf1, r_pf2) = array_v_split_at( r_pf |  r_offset)
    prval ( r_pf21, r_pf22) = array_v_split_at( r_pf2 | r_len)
    val r_ptr = ptr1_add_sz<byte>( r_p, r_offset)
    
    val () = memcpy( pf221, r_pf21 | res_ptr, r_ptr, r_len)
    
    prval () = r_pf2 := array_v_unsplit( r_pf21, r_pf22)
    prval () = r_pf := array_v_unsplit( r_pf1, r_pf2)
    
    prval () = pf22 := array_v_unsplit( pf221, pf222)
    prval () = pf2 := array_v_unsplit( pf21, pf22)
    prval () = pf := array_v_unsplit( pf1, pf2)
    
    prval () = bs_takeback_struct( succ_vb( (r_pf, r_fpf)) | r)
    prval () = bs_takeback_struct( succ_vb( (pf, fpf)) | res)
    val (res_len, res_offset, res_cap, res_ucap, res_refcnt, res_dynamic, res_p) = explode( res)
    val res = build( () | (res_len + r_len, res_offset, res_cap, res_ucap - r_len, res_refcnt, res_dynamic, res_p))
  }
end

implement ref_bs_child( i) = res where {
  extern castfn
    explode
    { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
    ( i: Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
    ):<>
    ( size_t(len)
    , size_t(offset)
    , size_t(cap)
    , size_t(ucap)
    , size_t(refcnt)
    , bool(dynamic)
    , ptr(l)
    )
  extern castfn
    build
    { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
    ( void
    | ( size_t(len)
      , size_t(offset)
      , size_t(cap)
      , size_t(ucap)
      , size_t(refcnt)
      , bool(dynamic)
      , ptr(l)
      )
    ):<> Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  val (i_len, i_offset, i_cap, i_ucap, i_refcnt, i_dynamic, i_p) = explode( i)
  val res = build( () | (i_len, i_offset, i_cap, i_ucap, i2sz 1, i_dynamic, i_p))
  val () = i := build( () | (i_len, i_offset, i_cap, i2sz 0, i_refcnt + i2sz 1, i_dynamic, i_p))
}
implement ref_bs_parent( i) = res where {
  extern castfn
    explode
    { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
    ( i: Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
    ):<>
    ( size_t(len)
    , size_t(offset)
    , size_t(cap)
    , size_t(ucap)
    , size_t(refcnt)
    , bool(dynamic)
    , ptr(l)
    )
  extern castfn
    build
    { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
    ( void
    | ( size_t(len)
      , size_t(offset)
      , size_t(cap)
      , size_t(ucap)
      , size_t(refcnt)
      , bool(dynamic)
      , ptr(l)
      )
    ):<> Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  val (i_len, i_offset, i_cap, i_ucap, i_refcnt, i_dynamic, i_p) = explode(i)
  val res = build( () | (i_len, i_offset, i_cap, i2sz 0, i2sz 1, i_dynamic, i_p))
  val () = i := build( () | (i_len, i_offset, i_cap, i_ucap, i_refcnt + i2sz 1, i_dynamic, i_p))
}

implement create{cap}(cap) =
let
  val ( pf, fpf | p) = array_ptr_alloc<char>(cap)
  extern castfn
    build
    { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
    ( array_v(char?,l,cap)
    , mfree_gc_v l
    | ( size_t(len)
      , size_t(offset)
      , size_t(cap)
      , size_t(ucap)
      , size_t(refcnt)
      , bool(dynamic)
      , ptr(l)
      )
    ):<> Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)

in
  build( pf, fpf | (i2sz 0, i2sz 0, cap, cap, i2sz 0, true, p))
end

implement is_empty(v) = let
  prval () = lemma_bytestring_param(v)
  prval () = lemma_bytestring_param( v)
  val ( rpf | impl) = bs_takeout_struct(v)
  val (n, _, _, _, _, _, _) = impl
  prval () = bs_takeback_struct( rpf | v)
in
  if n = 0
  then true
  else false
end

implement isnot_empty(v) = not( is_empty(v))

implement neq_bytestring_bytestring(l, r) = not( l = r)
  
  
implement drop_impl(n, i) =
let
  val res = ref_bs_child i
  val (rpf | impl) = bs_explode( res)
  val (len, offset, cap, ucap, refcnt, dynamic, p) = impl
in
  if n > len
  then res where {
    val res = bs_build( rpf | (i2sz 0, i2sz 0, cap, ucap, refcnt, dynamic, p))
  }
  else res where {
    val res = bs_build( rpf | ( len - n, offset + n, cap, ucap, refcnt, dynamic, p))
  }
end
  
  
implement dropC_impl( n, i) = res where {
  val i_len = length i
  var res: Bytestring0?
  var vi: Bytestring0?
  val () = vi := i
  val () = res := drop_impl( n, vi)
  val () = free( vi, res)
}

implement take_impl(n, i) =
let
  val res = ref_bs_parent i
  val (rpf | impl) = bs_explode( res)
  val (len, offset, cap, ucap, refcnt, dynamic, p) = impl
in
  if n > len
  then res where {
    val res = bs_build( rpf | (len, offset, cap, ucap, refcnt, dynamic, p))
  }
  else res where {
    val res = bs_build( rpf | ( n, offset, cap, ucap, refcnt, dynamic, p))
  }
end
  
  
implement takeC_impl( n, i) = res where {
  val i_len = length i
  var res: Bytestring0?
  var vi: Bytestring0?
  val () = vi := i
  val () = res := take_impl( n, vi)
  val () = free( vi, res)
}

implement println(i) = {
  prval () = lemma_bytestring_param(i)
  val ( rpf | impl) = bs_takeout_struct(i)
  val (len, offset, cap, ucap, refcnt, dynamic, p) = impl
  val ptr = ptr_add<char>( p, offset)
  val _ = $extfcall( int, "write", 1, ptr, len)
  val _ = $extfcall( int, "write", 1, "\n", 1)
  prval () = bs_takeback_struct( rpf | i)
}
implement printlnC(i) = {
  prval () = lemma_bytestring_param(i)
  val () = println(i)
  val () = free( i)
}

implement bs2bytes{n,offset,cap,ucap}{dynamic}{l}(i) = ret where {
  prval () = lemma_bytestring_param(i)
  val (rpf | impl) = bs_takeout_struct(i)
  val (len, offset, cap, ucap, refcnt, dynamic, p) = impl
  prval succ_vb( pf0) = rpf
  prval (pf, fpf) = pf0
  val ptr = ptr1_add_sz<char>( p, offset)
  prval () = rpf := succ_vb( (pf, fpf))

  prval () = bs_takeback_struct( rpf | i)
  extern prfun
    believeme
    {l1:agz}
    ( i: !Bytestring_vtype(n,offset,cap,ucap,0,dynamic,l) >> minus_vt( Bytestring_vtype(n,offset,cap,ucap,0,dynamic,l), bytes(n) @ l1)
    , ptr l1
    ): ( bytes(n) @ l1)
  val ret = ( believeme(i, ptr) | ptr, len)
}

implement take1(n, i) =
let
  extern castfn
    build
    { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
    ( void
    | ( size_t(len)
      , size_t(offset)
      , size_t(cap)
      , size_t(ucap)
      , size_t(refcnt)
      , bool(dynamic)
      , ptr(l)
      )
    ):<> Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
  val ( rpf | (len, offset,cap,ucap, refcnt, dynamic, p)) = bs_explode( i)
  val () = i := bs_build( rpf | (len, offset, cap, ucap, refcnt + i2sz 1, dynamic, p))
in
   if n >= len
   then build( () | (len, offset, cap, i2sz 0, i2sz 1, dynamic, p))
   else build( () | (n, offset, cap, i2sz 0, i2sz 1, dynamic, p))
end

implement decref_bs( consume, preserve) = {
  extern castfn
    explode
    { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
    ( i: Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
    ):<>
    ( ( size_t(len)
      , size_t(offset)
      , size_t(cap)
      , size_t(ucap)
      , size_t(refcnt)
      , bool(dynamic)
      , ptr(l)
      )
    )
  val _ = explode( consume)
  val (rpf | impl) = bs_explode( preserve)
  val (len, offset, cap, ucap, refcnt, dynamic, p) = impl
  val () = preserve := bs_build( rpf | (len, offset, cap, ucap, refcnt - 1, dynamic, p))
}
implement deref( i) = res where {
  extern castfn
    deinit
    { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
    ( i: &Bs_minus_struct( len, offset, cap, ucap, refcnt, dynamic, l) >> Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)?
    ):<>
    void
  val (rpf | impl) = bs_takeout_struct( i)
  val res = bs_build( rpf | impl)
  prval () = deinit( i)
}
implement init( i, v) = {
  extern castfn
    explode
    { len, offset, cap, ucap, refcnt:nat}{dynamic:bool}{l:addr}
    ( i: Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
    ):<>
    ( ( size_t(len)
      , size_t(offset)
      , size_t(cap)
      , size_t(ucap)
      , size_t(refcnt)
      , bool(dynamic)
      , ptr(l)
      )
    )
  val (rpf | impl) = bs_explode( v)
  val _ = explode( i)
  val () = i := bs_build( rpf | impl)
}

implement append(l, r) = res where {
  prval () = lemma_bytestring_param( l)
  prval () = lemma_bytestring_param( r)
  val res = append_impl( l, r)
}

implement appendC(l, r) = res where {
  prval () = lemma_bytestring_param( l)
  prval () = lemma_bytestring_param( r)
  val res = appendC_impl( l, r)
}

implement take( n, i) = take_impl( n, i)

implement takeC(n, i) = takeC_impl( n, i)

implement drop(n, i) = drop_impl( n, i)

implement dropC(n, i) = dropC_impl( n, i)

(*
  
fn
  string2pfptr
  {n:pos}
  ( s: string(n)
  ):
  [l: agz]
  ( array_v( char, l, n)
  , array_v( char, l, n) -<prf> void
  | ptr l
  ) = (pf, fpf | ret) where {
  extern prfun
    string2pf
    {n:pos}{l:agz}
    ( s: string(n)
    , ptr l
    ):
    ( array_v( char, l, n)
    , array_v( char, l, n) -<prf> void
    )
  val ret = string2ptr(s)
  prval (pf, fpf) = string2pf(s, ret)
}


implement bs2ptr(i) = ret where {
  prval () = lemma_bytestring_param(i)
  val (rpf | impl) = bs_takeout_struct(i)
  val (_, offset, _, tuple) = impl
  prval succ_vb( pf) = rpf
  prval (tuple_pf, t_fpf, pf, fpf) = pf
  val (unused_offset, recfnt, p) = !tuple
  val ret = ptr_add<char>( p, offset)
  prval () = rpf := succ_vb( (tuple_pf, t_fpf, pf, fpf))
  
  prval () = bs_takeback_struct( rpf | i)
  val () = assertloc( ptr_isnot_null ret)
}

implement bs2string{n,cap}(i) = ret where {
  prval () = lemma_bytestring_param(i)
  val (rpf | impl) = bs_takeout_struct(i)
  prval () = lemma_bytestring_impl_param(impl)
  val (_, offset, _, tuple) = impl
  prval succ_vb( pf) = rpf
  prval (tuple_pf, t_fpf, pf, fpf) = pf
  val (unused_offset, recfnt, p) = !tuple
  extern castfn believeme{l:addr}( i: ptr l): string(n)
  val ret = believeme(ptr_add<char>(p, offset))
  prval () = rpf := succ_vb( (tuple_pf, t_fpf, pf, fpf))
  
  prval () = bs_takeback_struct( rpf | i)
}


*)