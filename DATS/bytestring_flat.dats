#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
#define ATS_PACKNAME "bytestring"
#define ATS_EXTERN_PREFIX "bytestring_"

#include "./../HATS/bytestring.hats"
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
  ( result_vb( l > null, void, (array_v(uchar, l, cap), mfree_gc_v l))
  | Bytestring_impl(n, offset, cap, ucap, refcnt, dynamic, l)
  )

extern castfn
  bs_build
  {n,offset,cap,ucap,refcnt:nat}{dynamic:bool}{l:addr}
  ( result_vb( l > null, void, (array_v(uchar, l, cap), mfree_gc_v l))
  | bs: Bytestring_impl(n, offset, cap, ucap, refcnt, dynamic, l)
  ):<> Bytestring_vtype(n,offset,cap,ucap,refcnt,dynamic,l)

extern castfn
  bs_takeout_struct
  {n,offset,cap,ucap,refcnt:nat}{dynamic:bool}{l:addr}
  ( bs: !Bytestring_vtype(n,offset,cap,ucap,refcnt,dynamic,l) >> Bs_minus_struct( n, offset, cap, ucap, refcnt, dynamic, l)
  ):<>
  ( result_vb( l > null, void, (array_v(uchar, l, cap), mfree_gc_v l))
  | Bytestring_impl(n, offset, cap, ucap, refcnt, dynamic, l)
  )

extern praxi
  bs_takeback_struct
  {n,offset,cap,ucap,refcnt: nat}{l:addr}{dynamic:bool}
  ( result_vb( l > null, void, (array_v(uchar,l,cap), mfree_gc_v l))
  | bs: !Bs_minus_struct( n, offset, cap, ucap, refcnt, dynamic, l) >> Bytestring_vtype( n, offset, cap, ucap, refcnt, dynamic, l)
  ):<> void

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
    ):<>
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
    ( array_v(uchar,l,cap), mfree_gc_v l | Bytestring_impl( len, offset, cap, ucap, 0, true, l))
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
  { sizeof(a) == sizeof(char) || sizeof(a) == sizeof(byte) || sizeof(a) == sizeof(uchar)}
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
  {l:agz}{n:nat}{sizeof(a) == sizeof(char) || sizeof(a) == sizeof(byte) || sizeof(a) == sizeof(uchar)}
  ( i: ptr l
  , n: size_t n
  ):<>
  [l+n*sizeof(a) > null]
  ptr (l+n*sizeof(a)) =
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
  | sizeof<uchar> <= 0 => false where {
    prval () = bs_takeback_struct( r_rpf | r)
    prval () = bs_takeback_struct( l_rpf | l)
  }
  | _ => ret where {
    val r_ptr = ptr1_add_sz<uchar>( r_p, r_offset)
    val l_ptr = ptr1_add_sz<uchar>( l_p, l_offset)
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
  appendC_bs_bs
  {l_len, l_offset, l_cap, l_ucap}{l_dynamic}{l_p}
  {r_len, r_offset, r_cap, r_ucap}{r_dynamic}{r_p}
  ( l, r) = res where {
  var res: Bytestring0?
  val () = res := append_bs_bs( l, r)
  val () = free r
  val () = free l
}

implement reference_count(i) = refcnt where {
  prval () = lemma_bytestring_param( i)
  val ( rpf | (_, _, _, _, refcnt, _, _)) = bs_takeout_struct( i)
  prval () = bs_takeback_struct( rpf | i)
}

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

implement append_bs_bs
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
  (* create new buffer *)
  res where {
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
    val l_ptr = ptr1_add_sz<uchar>( l_p, l_offset)

    val () = memcpy( res_pf1, l_pf21 | res_p, l_ptr, l_len)
    
    prval () = l_pf2 := array_v_unsplit( l_pf21, l_pf22)
    prval () = l_pf0 := array_v_unsplit( l_pf1, l_pf2)
    prval () = l_rpf := succ_vb( (l_pf0, l_fpf))
    prval () = bs_takeback_struct( l_rpf | l)
    
    val res_ptr = ptr1_add_sz<uchar>( res_p, l_len)
    
    val (r_rpf | impl) = bs_takeout_struct( r)
    val (r_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p) = impl
    val r_ptr = ptr1_add_sz<uchar>( r_p, r_offset)
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

implement isnot_empty(v) = ((n > 0) * ptr_isnot_null(l)) where {
  prval () = lemma_bytestring_param( v)
  val (rpf | impl) = bs_takeout_struct(v)
  val (n, _, _, _, _, _, l) = impl
  prval () = bs_takeback_struct( rpf | v)
}

implement neq_bytestring_bytestring(l, r) = not( l = r)
implement eq_bytestring_bytestringC(l, r) = res where {
  val res = l = r
  val () = free( r)
}
implement neq_bytestring_bytestringC(l, r) = not( eq_bytestring_bytestringC( l, r))
  
  
implement drop(n, i) =
let
  val res = ref_bs_child i
  val (rpf | impl) = bs_explode( res)
  val (len, offset, cap, ucap, refcnt, dynamic, p) = impl
in
  bs_build( rpf | ( len - n, offset + n, cap, ucap, refcnt, dynamic, p))
end
  
  
implement dropC( n, i) =
let
  val (rpf | (len, offset, cap, ucap, refcnt, dynamic, p)) = bs_explode( i)
in
  bs_build( rpf | ( len - n, offset + n, cap, ucap, refcnt, dynamic, p)) 
end

implement take(n, i) =
let
  val res = ref_bs_parent i
  val (rpf | impl) = bs_explode( res)
  val (len, offset, cap, ucap, refcnt, dynamic, p) = impl
in
  bs_build( rpf | ( n, offset, cap, ucap, refcnt, dynamic, p))
end
  
  
implement takeC( n, i) =
let
  val ( rpf | (len, offset, cap, ucap, refcnt, dynamic, p)) = bs_explode( i)
in
  if n = len
  then bs_build( rpf | (n, offset, cap, ucap, refcnt, dynamic, p))
  else bs_build( rpf | (n, offset, cap, i2sz 0, refcnt, dynamic, p))
end

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

implement bs2bytes{a}{n,offset,cap,ucap,refcnt}{dynamic}{l}(i) = ret where {
  prval () = lemma_bytestring_param(i)
  val (rpf | impl) = bs_takeout_struct(i)
  val (len, offset, cap, ucap, refcnt, dynamic, p) = impl
  prval succ_vb( pf0) = rpf
  prval (pf, fpf) = pf0
  val ptr = ptr1_add_sz<a>( p, offset)
  prval () = rpf := succ_vb( (pf, fpf))

  prval () = bs_takeback_struct( rpf | i)
  extern prfun
    believeme
    {l1:agz}
    ( i: !Bytestring_vtype(n,offset,cap,ucap,refcnt,dynamic,l) >> minus_vt( Bytestring_vtype(n,offset,cap,ucap,refcnt,dynamic,l), array_v(a, l1, n))
    , ptr l1
    ): ( array_v(a, l1, n))
  val ret = ( believeme(i, ptr) | ptr, len)
}

implement bs2unused_bytes{a}{n,offset,cap,ucap,refcnt}{dynamic}{l}(i) = ret where {
  prval () = lemma_bytestring_param(i)
  val (rpf | impl) = bs_takeout_struct(i)
  val (len, offset, cap, ucap, refcnt, dynamic, p) = impl
  prval succ_vb( pf0) = rpf
  prval (pf, fpf) = pf0
  val ptr = ptr1_add_sz<a>( p, offset + len)
  prval () = rpf := succ_vb( (pf, fpf))

  prval () = bs_takeback_struct( rpf | i)
  extern prfun
    believeme
    {l1:agz}
    ( i: !Bytestring_vtype(n,offset,cap,ucap,refcnt,dynamic,l) >> minus_vt( Bytestring_vtype(n,offset,cap,ucap,refcnt,dynamic,l), array_v(a,l1,ucap))
    , ptr l1
    ): ( array_v(a,l1,ucap))
  val ret = ( believeme(i, ptr) | ptr, ucap)
}

implement unused_bytes_addback{a}{n,offset,cap,ucap,refcnt,used_bytes}{dynamic}{l,l1}( pf | i, used_bytes) = {
  extern prfun
    believeme
    ( pf: array_v(a,l1,ucap)
    | i: !minus_vt( Bytestring_vtype(n,offset,cap,ucap,refcnt,dynamic,l), array_v(a,l1,ucap)) >> Bytestring_vtype( n, offset, cap, ucap, refcnt, dynamic, l)
    ):<> void
  prval () = believeme( pf | i)
  val (pf | impl) = bs_explode( i)
  val (len, offset, cap, ucap, refcnt, dynamic, p) = impl
  val () = i := bs_build( pf | (len + used_bytes, offset, cap, ucap - used_bytes, refcnt, dynamic, p))
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

implement growC(l, r) = res where {
  prval () = lemma_bytestring_param( l)
  prval () = lemma_bytestring_param( r)
  val ( lpf | l_impl) = bs_explode( l)
  val ( rpf | r_impl) = bs_takeout_struct( r)
  val (l_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p) = l_impl
  val (r_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p) = r_impl
  (* now actually copy the data to the end of l's buffer *)
  prval succ_vb( l_rpf) = lpf
  prval (l_pf, l_fpf) = l_rpf
  prval (l_pf1, l_pf2) = array_v_split_at( l_pf | l_offset + l_len)
  prval (l_pf21, l_pf22) = array_v_split_at( l_pf2 | r_len) (* l_pf21 is the start of destination buffer *)
  
  prval succ_vb( r_rpf ) = rpf
  prval (r_pf, r_fpf) = r_rpf
  prval (r_pf1, r_pf2)= array_v_split_at( r_pf | r_offset)
  prval (r_pf21, r_pf22) = array_v_split_at( r_pf2 | r_len) (* r_pf21 contains the data *)
  
  val l_ptr = ptr1_add_sz<uchar>(l_p, l_offset + l_len) (* the end of data contains unused memory *)
  val r_ptr = ptr1_add_sz<uchar>(r_p, r_offset) (* the start of the right buffer *)
  val () = memcpy( l_pf21, r_pf21 | l_ptr, r_ptr, r_len) (* now actually copy memory *)
  (* and bring back the proofs *)
  prval () = r_pf2 := array_v_unsplit( r_pf21, r_pf22)
  prval () = r_pf := array_v_unsplit( r_pf1, r_pf2)
  prval () = rpf := succ_vb( (r_pf, r_fpf))
  
  prval () = l_pf2 := array_v_unsplit( l_pf21, l_pf22)
  prval () = l_pf := array_v_unsplit( l_pf1, l_pf2)
  prval () = lpf := succ_vb( (l_pf, l_fpf))

  val res = bs_build( lpf | (l_len+r_len, l_offset, l_cap, l_ucap - r_len, l_refcnt, l_dynamic, l_p))
  (* cleanup *)
  prval () = bs_takeback_struct( rpf | r)
  val () = free r
}

implement get_char_at_uint( i, n) = uc2c res where {
  prval () = lemma_bytestring_param( i)
  val (rpf | impl) = bs_takeout_struct( i)
  val (len,offset,cap,ucap,refcnt,dynamic,p) = impl
  prval succ_vb( pf0) = rpf
  prval (pf, fpf) = pf0
  prval (pf1, pf2) = array_v_split_at( pf | offset + n)
  prval (pf21, pf22) = array_v_uncons( pf2)
  val ptr = ptr_add<uchar>( p, offset + n)
  val res = !ptr
  prval () = pf2 := array_v_cons( pf21, pf22)
  prval () = pf := array_v_unsplit( pf1, pf2)
  prval () = bs_takeback_struct( succ_vb((pf, fpf)) | i)
}

implement get_char_at_int( i, n) = uc2c res where {
  prval () = lemma_bytestring_param( i)
  val (rpf | impl) = bs_takeout_struct( i)
  val (len,offset,cap,ucap,refcnt,dynamic,p) = impl
  prval succ_vb( pf0) = rpf
  prval (pf, fpf) = pf0
  prval (pf1, pf2) = array_v_split_at( pf | offset + n)
  prval (pf21, pf22) = array_v_uncons( pf2)
  val ptr = ptr_add<uchar>( p, offset + n)
  val res = !ptr
  prval () = pf2 := array_v_cons( pf21, pf22)
  prval () = pf := array_v_unsplit( pf1, pf2)
  prval () = bs_takeback_struct( succ_vb((pf, fpf)) | i)
}
implement get_byte_at_uint( i, n) = res where {
  prval () = lemma_bytestring_param( i)
  val (rpf | impl) = bs_takeout_struct( i)
  val (len,offset,cap,ucap,refcnt,dynamic,p) = impl
  prval succ_vb( pf0) = rpf
  prval (pf, fpf) = pf0
  prval (pf1, pf2) = array_v_split_at( pf | offset + n)
  prval (pf21, pf22) = array_v_uncons( pf2)
  val ptr = ptr_add<uchar>( p, offset + n)
  val res = !ptr
  prval () = pf2 := array_v_cons( pf21, pf22)
  prval () = pf := array_v_unsplit( pf1, pf2)
  prval () = bs_takeback_struct( succ_vb((pf, fpf)) | i)
}

implement get_byte_at_int( i, n) = res where {
  prval () = lemma_bytestring_param( i)
  val (rpf | impl) = bs_takeout_struct( i)
  val (len,offset,cap,ucap,refcnt,dynamic,p) = impl
  prval succ_vb( pf0) = rpf
  prval (pf, fpf) = pf0
  prval (pf1, pf2) = array_v_split_at( pf | offset + n)
  prval (pf21, pf22) = array_v_uncons( pf2)
  val ptr = ptr_add<uchar>( p, offset + n)
  val res = !ptr
  prval () = pf2 := array_v_cons( pf21, pf22)
  prval () = pf := array_v_unsplit( pf1, pf2)
  prval () = bs_takeback_struct( succ_vb((pf, fpf)) | i)
}


implement {env}take_while(env, f, i) = result where {
  fun
    loop
    {len, offset, cap, ucap, refcnt, n: nat | n <= len}{dynamic:bool}{l:addr}
    .<len - n>.
    ( i: size_t n
    , sz: size_t len
    , s: !Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
    , env: !env
    ):<!wrt>
    [on: nat | on <=len]
    size_t(on) =
  if i = sz
  then i where {
    prval () = prop_verify {len == n}()
  }
  else
    if not (f( env, s[i]))
    then i
    else loop( i + i2sz 1, sz, s, env)
  val idx = loop( i2sz 0, length i, i, env)
  val result = take( idx, i)
}

implement split_on( delim, i) = result where {
  fun
    loop
    {len, offset, cap, ucap, refcnt: nat}{dynamic:bool}{l:addr}
    {n,ln: nat}
    .<n>.
    ( i: size_t n
    , acc: list_vt( [llen, loffset:nat] Bytestring_vtype(llen, loffset, cap, 0, 1, dynamic,l), ln)
    , s: &Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l) >> Bytestring_vtype( olen, ooffset, cap, ucap, refcnt + (oln - ln), dynamic, l)
    ):<!wrt>
    #[olen,ooffset,oln: nat]
    list_vt([olen1, ooffset1:nat] Bytestring_vtype(olen1, ooffset1, cap, 0, 1, dynamic, l), oln) =
  let
    val s_sz = length s
    val head = take_while<uchar>( delim, lam (env, x) =<> x != env, s)
    val head_sz = length head
  in
    if i = i2sz 0
    then acc where {
      val () = free( head, s)
    }
    else 
      ifcase
      | head_sz > s_sz => acc where { (* should not happen, but need to prove, that head <= s *)
        val () = free( head, s)
      }
      | s_sz = 0 => list_vt_cons( head, acc)
      | head_sz = s_sz => list_vt_cons( head, acc) where {
        val () = s := dropC( head_sz, s)
      }
      | _ => loop( i - i2sz 1, list_vt_cons( head, acc), s) where {
        val () = s := dropC( head_sz + i2sz 1, s)
      }
  end
  val ( rpf | impl) = bs_takeout_struct( i)
  val (len, offset, cap, ucap, refcnt, dynamic, p) = impl
  prval () = bs_takeback_struct( rpf | i)
  val result = list_vt_reverse( loop( length i, list_vt_nil(), i)) 
  val ( rpf | impl) = bs_explode( i)
  val () = i := bs_build( rpf | (len, offset, cap, ucap, refcnt + length result, dynamic, p))
}

implement copy( i) =
let
  prval () = lemma_bytestring_param( i)
in
  if capacity i = 0
  then empty()
  else result where {
    val ( i_pf | i_p, i_sz) = bs2bytes( i)
    val ( pf, fpf | p) = array_ptr_alloc<uchar>(i_sz)
    val () = memcpy( pf, i_pf | p, i_p, i_sz)
    prval () = bytes_addback( i_pf | i)
    val result = pack( pf, fpf | p, i_sz, i_sz)
  }
end

implement append_char_bs(a, l) =
let
  prval () = lemma_bytestring_param( l)
  val sz = length l
in
  if sz = i2sz 0
  then pack a
  else result where {
    var result: Bytestring0?
    val a1 = $UN.cast{byte} a
    val () = result := create (sz + 1)
    val ( r_pf | r_ptr, r_sz) = bs2unused_bytes{byte}( result)
    val ( l_pf | l_ptr, l_sz) = bs2bytes{byte}( l)
    val () = array_set_at_guint<byte>( !r_ptr, i2sz 0, a1)
    prval (pf1, pf2) = array_v_split_at( r_pf | i2sz 1)
    val r_ptr1 = ptr1_add_sz<byte>( r_ptr, i2sz 1)
    val () = memcpy{byte}{byte}( pf2, l_pf | r_ptr1, l_ptr, l_sz) (* copy l into result *)
    prval () = r_pf := array_v_unsplit( pf1, pf2)
    val () = unused_bytes_addback( r_pf | result, sz + 1)
    prval () = bytes_addback( l_pf | l)
  }
end
implement append_bs_char(l, a) =
let
  prval () = lemma_bytestring_param( l)
  val sz = length l
in
  if sz = i2sz 0
  then pack a
  else result where {
    var result: Bytestring0?
    val a1 = $UN.cast{byte} a
    val () = result := create (sz + 1)
    val ( r_pf | r_ptr, r_sz) = bs2unused_bytes{byte}( result)
    val ( l_pf | l_ptr, l_sz) = bs2bytes{byte}( l)
    val () = memcpy{byte}{byte}( r_pf, l_pf | r_ptr, l_ptr, l_sz) (* copy l into result *)
    (* now result[l_sz] should have value of a *)
    val () = array_set_at_guint( !r_ptr, sz, a1)
    val () = unused_bytes_addback( r_pf | result, sz + 1)
    prval () = bytes_addback( l_pf | l)
  }
end

implement appendC_bs_char(l, a) = result where {
  val result = append_bs_char( l, a)
  val () = free l
}

implement appendC_char_bs(a, l) = result where {
  val result = append_char_bs( a, l)
  val () = free l
}

implement pack_char(a) = result where {
  var result: Bytestring0?
  val a1 = $UN.cast{byte} a
  val () = result := create (i2sz 1)
  val ( r_pf | r_ptr, r_sz) = bs2unused_bytes{byte}( result)
  (* now result[l_sz] should have value of a *)
  val () = array_set_at_guint( !r_ptr, i2sz 0, a1)
  val () = unused_bytes_addback( r_pf | result, i2sz 1)
}