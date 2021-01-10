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
#include "inttypes.h"
%}


typedef Bytestring_impl(len:int, offset: int, capacity: int, ucapacity: int, refcnt:int, dynamic: bool, l:addr) =
  @( size_t(len)
   , size_t(offset) (* offset from the base pointer of length len *)
   , size_t(capacity) (* size of buffer, starting from base pointer *)
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
  ( result_vb( l > null, void, (array_v(char, l, cap), mfree_gc_v l))
  | Bytestring_impl(n, offset, cap, ucap, refcnt, dynamic, l)
  )

extern castfn
  bs_build
  {n,offset,cap,ucap,refcnt:nat}{dynamic:bool}{l:addr}
  ( result_vb( l > null, void, (array_v(char, l, cap), mfree_gc_v l))
  | bs: Bytestring_impl(n, offset, cap, ucap, refcnt, dynamic, l)
  ):<> Bytestring_vtype(n,offset,cap,ucap,refcnt,dynamic,l)

extern castfn
  bs_takeout_struct
  {n,offset,cap,ucap,refcnt:nat}{dynamic:bool}{l:addr}
  ( bs: !Bytestring_vtype(n,offset,cap,ucap,refcnt,dynamic,l) >> Bs_minus_struct( n, offset, cap, ucap, refcnt, dynamic, l)
  ):<>
  ( result_vb( l > null, void, (array_v(char, l, cap), mfree_gc_v l))
  | Bytestring_impl(n, offset, cap, ucap, refcnt, dynamic, l)
  )

extern praxi
  bs_takeback_struct
  {n,offset,cap,ucap,refcnt: nat}{l:addr}{dynamic:bool}
  ( result_vb( l > null, void, (array_v(char,l,cap), mfree_gc_v l))
  | bs: !Bs_minus_struct( n, offset, cap, ucap, refcnt, dynamic, l) >> Bytestring_vtype( n, offset, cap, ucap, refcnt, dynamic, l)
  ):<> void

extern praxi bs_decref (* decrease refcnt *)
  {len,offset,cap,ucap,refcnt,dec_refcnt:nat | refcnt >= dec_refcnt}{dynamic:bool}{l:addr}
  (i: !Bytestring_vtype(len, offset, cap, ucap, refcnt, dynamic, l) >> Bytestring_vtype( len, offset, cap, ucap, refcnt - dec_refcnt, dynamic, l)
  , dec: int(dec_refcnt)
  ): void

extern praxi bs_incref (* decrease refcnt *)
  {len,offset,cap,ucap,refcnt,add_refcnt:nat}{dynamic:bool}{l:addr}
  (i: !Bytestring_vtype(len, offset, cap, ucap, refcnt, dynamic, l) >> Bytestring_vtype( len, offset, cap, ucap, refcnt + add_refcnt, dynamic, l)
  , add: int(add_refcnt)
  ): void

extern praxi
  bs_swap_ucap
  {l_len,l_offset,cap,l_ucap,l_refcnt:nat}{dynamic:bool}{l:addr}
  {r_len,r_offset,r_refcnt:nat}
  ( l: !Bytestring_vtype( l_len, l_offset, cap, l_ucap, l_refcnt, dynamic, l) >> Bytestring_vtype( l_len, l_offset, cap, 0, l_refcnt, dynamic, l)
  , r: !Bytestring_vtype( r_len, r_offset, cap, 0, r_refcnt, dynamic, l) >> Bytestring_vtype( r_len, r_offset, cap, l_ucap, r_refcnt, dynamic, l)
  ): void

implement empty() = believeme( () | ( i2sz(0), i2sz(0), i2sz(0), false, the_null_ptr)) where {
  extern castfn
    believeme
    {n,offset,cap:nat}{dynamic:bool}{l:addr}
    ( void
    | ( size_t(n)
      , size_t(offset)
      , size_t(cap)
      , bool(dynamic)
      , ptr(l)
      )
    ):<>
    Bytestring_vtype(n, offset, cap, 0, 0, dynamic, l)
}

implement pack_string{n}(s) =
let
  val sz = length(s)
  extern castfn
    believeme
    {n,offset,cap:nat}{dynamic:bool}{l:agz}
    ( void
    | ( size_t(n)
      , size_t(offset)
      , size_t(cap)
      , bool(dynamic)
      , ptr(l)
      )
    ):<>
    Bytestring_vtype(n, offset, cap, 0, 0, dynamic, l)
  extern castfn
    string2ptr_
    {n:nat}
    ( s: string(n)
    ):<>
    [l:agz]
    ptr l
  val p = string2ptr_ s
in
  believeme( () | (sz, i2sz(0), sz, false, p)) 
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
    ( array_v(char,l,cap), mfree_gc_v l | Bytestring_impl( len, offset, cap, ucap, 0, true, l))
  val (pf , fpf | (len, offset, cap, _, ptr)) = takeout( i)
  val () = array_ptr_free( pf, fpf | ptr)
}

implement isnot_dynamic(i) = dynamic = false where {
  prval () = lemma_bytestring_param(i)
  val ( rpf | impl) = bs_takeout_struct( i)
  val (_, _,_, dynamic, _) = impl
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
  val ( r_rpf | (r_len, r_offset, r_cap, r_dynamic, r_p)) = bs_takeout_struct( r)
  val ( l_rpf | (l_len, l_offset, l_cap, l_dynamic, l_p)) = bs_takeout_struct( l)
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
  | sizeof<char> <= 0 => false where {
    prval () = bs_takeback_struct( r_rpf | r)
    prval () = bs_takeback_struct( l_rpf | l)
  }
  | _ => ret where {
    val r_ptr = ptr1_add_sz<char>( r_p, r_offset)
    val l_ptr = ptr1_add_sz<char>( l_p, l_offset)
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
    {offset:nat}{dynamic:bool}{l:agz}
    ( !array_v( a, l, cap) >> Bytestring_v(a, n, offset, cap, cap - offset - n, 0, dynamic, l)
    | ( size_t(n)
      , size_t(offset)
      , size_t(cap)
      , bool(dynamic)
      , ptr(l)
      )
    ):<>
    Bytestring_vtype(n, offset, cap, cap - offset - n, 0, dynamic, l)
in
  believeme( pf | (sz, i2sz 0, capacity, false, i))
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
    {offset:nat}{dynamic:bool}{l:agz}
    ( array_v( a, l, cap)
    , mfree_gc_v l
    | ( size_t(n)
      , size_t(offset)
      , size_t(cap)
      , bool(dynamic)
      , ptr(l)
      )
    ):<>
    Bytestring_vtype(n, offset, cap, cap - offset - n, 0, true, l)
in
  believeme( pf, fpf | (sz, i2sz 0, capacity, true, p))
end
  
implement 
  appendC_bs_bs
  {l_len, l_offset, l_cap, l_ucap}{l_dynamic}{l_p}
  {r_len, r_offset, r_cap, r_ucap}{r_dynamic}{r_p}
  ( l, r) = res where {
  val res = append_bs_bs( l, r)
  val () = free r
  val () = free l
}

implement capacity(i) = cap where {
  prval () = lemma_bytestring_param( i)
  val ( rpf | (_, _, cap, _, _)) = bs_takeout_struct( i)
  prval () = bs_takeback_struct( rpf | i)
}

implement length_bs(i) = len where {
  prval () = lemma_bytestring_param( i)
  val ( rpf | (len, _, _, _, _)) = bs_takeout_struct( i)
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
  prval () = bs_decref( o, 1)
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
in
  (* create new buffer *)
  res where {
    var res: BytestringNSH0?
    val () = res := create( l_len + r_len)
    val (res_pf | res_ptr, res_sz) = bs2unused_bytes( res )
    prval (res_pf1, res_pf2) = array_v_split_at( res_pf | l_len)
    val (l_pf | l_ptr, l_len) = bs2bytes( l )

    val () = memcpy( res_pf1, l_pf | res_ptr, l_ptr, l_len)
    
    prval () = bytes_addback( l_pf | l)
    
    val res_ptr = ptr1_add_sz<char>( res_ptr, l_len)
    
    val (r_pf | r_ptr, r_len) = bs2bytes( r)
    
    val () = memcpy( res_pf2, r_pf | res_ptr, r_ptr, r_len)
  
    prval () = bytes_addback( r_pf | r)
    
    prval () = res_pf := array_v_unsplit( res_pf1, res_pf2)
    val () = unused_bytes_addback( res_pf | res, l_len+r_len)
  }
end

implement ref_bs_child( i) = res where {
  val ( pf | impl) = bs_takeout_struct( i)
  prval r_pf = clone( pf) where {
    extern praxi
      clone
      {cap:nat}{l:addr}
      ( i: !result_vb( l > null, void, (array_v(char, l, cap), mfree_gc_v l))
      ): result_vb( l > null, void, (array_v(char, l, cap), mfree_gc_v l))
  }
  prval () = bs_takeback_struct( pf | i)
  prval () = bs_incref( i, 1)
  val res = bs_build( r_pf | impl) where {
    extern castfn bs_build
      {len,offset,cap:nat}{refcnt,ucap:int}{dynamic:bool}{l:addr}
      ( result_vb( l > null, void, (array_v(char, l, cap), mfree_gc_v l))
      | bs: Bytestring_impl( len, offset, cap, ucap, refcnt, dynamic, l)
      ):<> Bytestring_vtype( len, offset, cap, 0, 1, dynamic, l)
  }
  prval () = bs_swap_ucap( i, res)
}
implement ref_bs_parent( i) = res where {
  val ( pf | impl) = bs_takeout_struct( i)
  prval r_pf = clone( pf) where {
    extern praxi
      clone
      {cap:nat}{l:addr}
      ( i: !result_vb( l > null, void, (array_v(char, l, cap), mfree_gc_v l))
      ): result_vb( l > null, void, (array_v(char, l, cap), mfree_gc_v l))
  }
  prval () = bs_takeback_struct( pf | i)
  prval () = bs_incref( i, 1)
  val res = bs_build( r_pf | impl) where {
    extern castfn bs_build
      {len,offset,cap:nat}{refcnt,ucap:int}{dynamic:bool}{l:addr}
      ( result_vb( l > null, void, (array_v(char, l, cap), mfree_gc_v l))
      | bs: Bytestring_impl( len, offset, cap, ucap, refcnt, dynamic, l)
      ):<> Bytestring_vtype( len, offset, cap, 0, 1, dynamic, l)
  }
}

implement create{cap}(cap) =
let
  val ( pf, fpf | p) = array_ptr_alloc<char>(cap)
  extern castfn
    build
    { len, offset, cap:nat}{dynamic:bool}{l:addr}
    ( array_v(char?,l,cap)
    , mfree_gc_v l
    | ( size_t(len)
      , size_t(offset)
      , size_t(cap)
      , bool(dynamic)
      , ptr(l)
      )
    ):<> Bytestring_vtype( len, offset, cap, cap, 0, dynamic, l)

in
  build( pf, fpf | (i2sz 0, i2sz 0, cap, true, p))
end

implement is_empty(v) = let
  prval () = lemma_bytestring_param(v)
  prval () = lemma_bytestring_param( v)
  val ( rpf | impl) = bs_takeout_struct(v)
  val (n, _, _, _, _) = impl
  prval () = bs_takeback_struct( rpf | v)
in
  if n = 0
  then true
  else false
end

implement isnot_empty(v) = ((n > 0) * ptr_isnot_null(l)) where {
  prval () = lemma_bytestring_param( v)
  val (rpf | impl) = bs_takeout_struct(v)
  val (n, _, _, _, l) = impl
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
  val (len, offset, cap, dynamic, p) = impl
in
  bs_build( rpf | ( len - n, offset + n, cap, dynamic, p))
end
  
  
implement dropC( n, i) =
let
  val (rpf | (len, offset, cap, dynamic, p)) = bs_explode( i)
in
  bs_build( rpf | ( len - n, offset + n, cap, dynamic, p)) 
end

implement take(n, i) =
let
  val res = ref_bs_parent i
  val (rpf | impl) = bs_explode( res)
  val (len, offset, cap, dynamic, p) = impl
in
  bs_build( rpf | ( n, offset, cap, dynamic, p))
end
  
  
implement takeC{n}{len,offset,cap,ucap,refcnt}{dynamic}{l}( n, i) =
let
  val ( rpf | (len, offset, cap, dynamic, p)) = bs_explode( i)
in
  if n = len
  then bs_build( rpf | (n, offset, cap, dynamic, p)) where {
    extern castfn bs_build
      ( result_vb( l > null, void, (array_v(char, l, cap), mfree_gc_v l))
      | bs: ( size_t( n)
            , size_t(offset)
            , size_t(cap)
            , bool(dynamic)
            , ptr l
            )
      ):<> Bytestring_vtype( n, offset, cap, ucap, refcnt, dynamic, l)
  }
  else bs_build( rpf | (n, offset, cap, dynamic, p)) where {
    extern castfn bs_build
      ( result_vb( l > null, void, (array_v(char, l, cap), mfree_gc_v l))
      | bs: ( size_t( n)
            , size_t(offset)
            , size_t(cap)
            , bool(dynamic)
            , ptr l
            )
      ):<> Bytestring_vtype( n, offset, cap, 0, refcnt, dynamic, l)
  }
end

implement println(i) = {
  prval () = lemma_bytestring_param(i)
  val ( rpf | impl) = bs_takeout_struct(i)
  val (len, offset, cap, dynamic, p) = impl
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

implement eprintln(i) = {
  prval () = lemma_bytestring_param(i)
  val ( rpf | impl) = bs_takeout_struct(i)
  val (len, offset, cap, dynamic, p) = impl
  val ptr = ptr_add<char>( p, offset)
  val _ = $extfcall( int, "write", 2, ptr, len)
  val _ = $extfcall( int, "write", 2, "\n", 1)
  prval () = bs_takeback_struct( rpf | i)
}
implement eprintlnC(i) = {
  prval () = lemma_bytestring_param(i)
  val () = eprintln(i)
  val () = free( i)
}

implement bs2bytes{n,offset,cap,ucap,refcnt}{dynamic}{l}(i) = ret where {
  prval () = lemma_bytestring_param(i)
  val (rpf | impl) = bs_takeout_struct(i)
  val (len, offset, cap, dynamic, p) = impl
  prval succ_vb( pf0) = rpf
  prval (pf, fpf) = pf0
  val ptr = ptr1_add_sz<char>( p, offset)
  prval () = rpf := succ_vb( (pf, fpf))

  prval () = bs_takeback_struct( rpf | i)
  extern prfun
    believeme
    {l1:agz}
    ( i: !Bytestring_vtype(n,offset,cap,ucap,refcnt,dynamic,l) >> minus_vt( Bytestring_vtype(n,offset,cap,ucap,refcnt,dynamic,l), array_v(char, l1, n))
    , ptr l1
    ): ( array_v(char, l1, n))
  val ret = ( believeme(i, ptr) | ptr, len)
}

implement bs2unused_bytes{n,offset,cap,refcnt}{dynamic}{l}(i) = ret where {
  prval () = lemma_bytestring_param(i)
  val (rpf | impl) = bs_takeout_struct(i)
  val (len, offset, cap, dynamic, p) = impl
  prval succ_vb( pf0) = rpf
  prval (pf, fpf) = pf0
  val ptr = ptr1_add_sz<char>( p, offset + len)
  prval () = rpf := succ_vb( (pf, fpf))

  prval () = bs_takeback_struct( rpf | i)
  extern prfun
    believeme
    ( i: !Bytestring_vtype( n,offset,cap,cap - offset - n, refcnt,dynamic,l) >> minus_vt( Bytestring_vtype(n,offset,cap,cap - offset - n,refcnt,dynamic,l), array_v(char,l+(offset+n)*sizeof(char),cap - offset - n))
    , ptr (l + (offset + n)*sizeof(char))
    ): ( array_v(char,l+(offset+n)*sizeof(char),cap - offset - n))
  val ret = ( believeme(i, ptr) | ptr, cap - offset - len)
}

implement unused_bytes_addback{len,offset,cap,ucap,refcnt,used_bytes}{dynamic}{l}( pf | i, used_bytes) = {
  extern prfun
    believeme
    ( pf: array_v(char,l+(offset+len)*sizeof(char),ucap)
    | i: !minus_vt( Bytestring_vtype(len,offset,cap,ucap,refcnt,dynamic,l), array_v(char,l+(len+offset)*sizeof(char),ucap)) >> Bytestring_vtype( len, offset, cap, ucap, refcnt, dynamic, l)
    ):<> void
  prval () = believeme( pf | i)
  val (pf | impl) = bs_explode( i)
  val (len, offset, cap, dynamic, p) = impl
  val () = i := bs_build( pf | (len + used_bytes, offset, cap, dynamic, p))
}

implement take1{len,offset,cap,ucap,refcnt,n}{dynamic}{l}(n, i) =
let
  extern castfn
    build
    {newlen,newoffset: nat}
    ( void
    | ( size_t(newlen)
      , size_t(newoffset)
      , size_t(cap)
      , bool(dynamic)
      , ptr(l)
      )
    ):<> Bytestring_vtype( newlen, newoffset, cap, 0, 1, dynamic, l)
  val ( rpf | impl) = bs_takeout_struct( i)
  val (len, offset,cap, dynamic, p) = impl
  prval () = bs_takeback_struct( rpf | i)
  prval () = bs_incref( i, 1)
in
   if n >= len
   then build( () | (len, offset, cap, dynamic, p))
   else build( () | (n, offset, cap, dynamic, p))
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
      , bool(dynamic)
      , ptr(l)
      )
    )
  val _ = explode( consume)
  prval () = bs_decref( preserve, 1)
}

implement growC(l, r) = vl where {
  prval () = lemma_bytestring_param( l)
  prval () = lemma_bytestring_param( r)
  var vl: Bytestring0?
  val () = vl := l
  val ( l_pf | l_ptr, l_sz) = bs2unused_bytes( vl)
  val ( r_pf | r_ptr, r_len) = bs2bytes( r)

  val () = memcpy( l_pf, r_pf | l_ptr, r_ptr, r_len) (* now actually copy memory *)
  
  (* and bring back the proofs *)
  prval () = bytes_addback( r_pf | r)
  val () = unused_bytes_addback( l_pf | vl, r_len)
  
  val () = free r
}

implement get_char_at_uint( i, n) = res where {
  prval () = lemma_bytestring_param( i)
  val (rpf | impl) = bs_takeout_struct( i)
  val (len,offset,cap,dynamic,p) = impl
  prval succ_vb( pf0) = rpf
  prval (pf, fpf) = pf0
  prval (pf1, pf2) = array_v_split_at( pf | offset + n)
  prval (pf21, pf22) = array_v_uncons( pf2)
  val ptr = ptr_add<char>( p, offset + n)
  val res = !ptr
  prval () = pf2 := array_v_cons( pf21, pf22)
  prval () = pf := array_v_unsplit( pf1, pf2)
  prval () = bs_takeback_struct( succ_vb((pf, fpf)) | i)
}

implement get_char_at_int( i, n) = res where {
  prval () = lemma_bytestring_param( i)
  val (rpf | impl) = bs_takeout_struct( i)
  val (len,offset,cap,dynamic,p) = impl
  prval succ_vb( pf0) = rpf
  prval (pf, fpf) = pf0
  prval (pf1, pf2) = array_v_split_at( pf | offset + n)
  prval (pf21, pf22) = array_v_uncons( pf2)
  val ptr = ptr_add<char>( p, offset + n)
  val res = !ptr
  prval () = pf2 := array_v_cons( pf21, pf22)
  prval () = pf := array_v_unsplit( pf1, pf2)
  prval () = bs_takeback_struct( succ_vb((pf, fpf)) | i)
}
implement get_byte_at_uint( i, n) = res where {
  prval () = lemma_bytestring_param( i)
  val (rpf | impl) = bs_takeout_struct( i)
  val (len,offset,cap,dynamic,p) = impl
  prval succ_vb( pf0) = rpf
  prval (pf, fpf) = pf0
  prval (pf1, pf2) = array_v_split_at( pf | offset + n)
  prval (pf21, pf22) = array_v_uncons( pf2)
  val ptr = ptr_add<char>( p, offset + n)
  val res = !ptr
  prval () = pf2 := array_v_cons( pf21, pf22)
  prval () = pf := array_v_unsplit( pf1, pf2)
  prval () = bs_takeback_struct( succ_vb((pf, fpf)) | i)
}

implement get_byte_at_int( i, n) = res where {
  prval () = lemma_bytestring_param( i)
  val (rpf | impl) = bs_takeout_struct( i)
  val (len,offset,cap,dynamic,p) = impl
  prval succ_vb( pf0) = rpf
  prval (pf, fpf) = pf0
  prval (pf1, pf2) = array_v_split_at( pf | offset + n)
  prval (pf21, pf22) = array_v_uncons( pf2)
  val ptr = ptr_add<char>( p, offset + n)
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
    val head = take_while<char>( delim, lam (env, x) =<> x != env, s)
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
  var tmp: Bytestring0?
  val () = tmp := ref_bs_parent i
  val result = list_vt_reverse( loop( length tmp, list_vt_nil(), tmp)) 
  prval () = bs_decref( tmp, length result)
  val () = free( tmp, i)
  prval () = bs_incref( i, length result)
}

implement copy( i) =
let
  prval () = lemma_bytestring_param( i)
in
  result where {
    val ( i_pf | i_p, i_sz) = bs2bytes( i)
    val ( pf, fpf | p) = array_ptr_alloc<char>(i_sz)
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
    var result: BytestringNSH0?
    val () = result := create (sz + 1)
    val ( r_pf | r_ptr, r_sz) = bs2unused_bytes( result)
    val ( l_pf | l_ptr, l_sz) = bs2bytes( l)
    val () = array_set_at_guint<char>( !r_ptr, i2sz 0, a)
    prval (pf1, pf2) = array_v_split_at( r_pf | i2sz 1)
    val r_ptr1 = ptr1_add_sz<char>( r_ptr, i2sz 1)
    val () = memcpy{char}{char}( pf2, l_pf | r_ptr1, l_ptr, l_sz) (* copy l into result *)
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
    var result: BytestringNSH0?
    val () = result := create (sz + 1)
    val ( r_pf | r_ptr, r_sz) = bs2unused_bytes( result)
    val ( l_pf | l_ptr, l_sz) = bs2bytes( l)
    val () = memcpy{char}{char}( r_pf, l_pf | r_ptr, l_ptr, l_sz) (* copy l into result *)
    (* now result[l_sz] should have value of a *)
    val () = array_set_at_guint( !r_ptr, sz, a)
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
  var result: BytestringNSH0?
  val () = result := create (i2sz 1)
  val ( r_pf | r_ptr, r_sz) = bs2unused_bytes( result)
  (* now result[l_sz] should have value of a *)
  val () = array_set_at_guint( !r_ptr, i2sz 0, a)
  val () = unused_bytes_addback( r_pf | result, i2sz 1)
}

implement append_bsC_bs( l, r) = result where {
  val result = append_bs_bs(l, r)
  val () = free l
}

implement append_bs_bsC( l, r) = result where {
  val result = append_bs_bs( l, r)
  val () = free r
}

implement pack_int64(i) =
let
  val PRI_fmt_bs = pack PRI_fmt where {
    macdef PRI_fmt0 = $extval( string, "PRIi64")
    val PRI_sz = g1ofg0( length PRI_fmt0)
    val PRI_fmt = believeme( PRI_fmt0, PRI_sz) where {
      extern castfn believeme{n:nat}( i: string, sz: size_t(n)):<> [n > 0; n < 9] string(n)
    }
  }
  var format_bs = create(length PRI_fmt_bs + 2) ++ $BS.pack '%' ++ PRI_fmt_bs
  val (fmt_pf | fmt_p, fmt_sz) = bs2unused_bytes( format_bs)
  val () = array_set_at_guint( !fmt_p, i2sz 0, $UN.cast{char} 0)
  val () = unused_bytes_addback( fmt_pf | format_bs, i2sz 0)
  val ( format_pf | format_p, _) = $BS.bs2bytes( format_bs)
  var bs: BytestringNSH0?
  val () = bs := $BS.create(i2sz 21) // -9223372036854775807 - min int64 value + NULL
  val (pf | p, sz) = $BS.bs2unused_bytes( bs)
  val (rendered:(int)) = g1ofg0( $extfcall( int, "snprintf", p, i2sz 21, format_p, i))
  prval () = $BS.bytes_addback( format_pf | format_bs)
  val () = free format_bs
in
  ifcase
  | rendered <= 0 => bs where {
    val () = array_set_at_guint( !p, i2sz 0, '0')
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 1)
  }
  | rendered > 21 => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 21)
  }
  | _ => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz rendered)
  }
end

implement pack_uint64(i) =
let
  val PRI_fmt_bs = pack PRI_fmt where {
    macdef PRI_fmt0 = $extval( string, "PRIu64")
    val PRI_sz = g1ofg0( length PRI_fmt0)
    val PRI_fmt = believeme( PRI_fmt0, PRI_sz) where {
      extern castfn believeme{n:nat}( i: string, sz: size_t(n)):<> [n > 0; n < 9] string(n)
    }
  }
  var format_bs = create(length PRI_fmt_bs + 2) ++ $BS.pack '%' ++ PRI_fmt_bs
  val (fmt_pf | fmt_p, fmt_sz) = bs2unused_bytes( format_bs)
  val () = array_set_at_guint( !fmt_p, i2sz 0, $UN.cast{char} 0)
  val () = unused_bytes_addback( fmt_pf | format_bs, i2sz 0)
  val ( format_pf | format_p, _) = $BS.bs2bytes( format_bs)
  var bs: BytestringNSH0?
  val () = bs := $BS.create(i2sz 21) // 18,446,744,073,709,551,615 - max int64 value + NULL
  val (pf | p, sz) = $BS.bs2unused_bytes( bs)
  val (rendered:(int)) = g1ofg0( $extfcall( int, "snprintf", p, i2sz 21, format_p, i))
  prval () = $BS.bytes_addback( format_pf | format_bs)
  val () = free format_bs
in
  ifcase
  | rendered <= 0 => bs where {
    val () = array_set_at_guint( !p, i2sz 0, '0')
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 1)
  }
  | rendered > 21 => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 21)
  }
  | _ => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz rendered)
  }
end

implement pack_int32(i) =
let
  val PRI_fmt_bs = pack PRI_fmt where {
    macdef PRI_fmt0 = $extval( string, "PRIi32")
    val PRI_sz = g1ofg0( length PRI_fmt0)
    val PRI_fmt = believeme( PRI_fmt0, PRI_sz) where {
      extern castfn believeme{n:nat}( i: string, sz: size_t(n)):<> [n > 0; n < 9] string(n)
    }
  }
  var format_bs = create(length PRI_fmt_bs + 2) ++ $BS.pack '%' ++ PRI_fmt_bs
  val (fmt_pf | fmt_p, fmt_sz) = bs2unused_bytes( format_bs)
  val () = array_set_at_guint( !fmt_p, i2sz 0, $UN.cast{char} 0)
  val () = unused_bytes_addback( fmt_pf | format_bs, i2sz 0)
  val ( format_pf | format_p, _) = $BS.bs2bytes( format_bs)
  var bs: BytestringNSH0?
  val () = bs := $BS.create(i2sz 12) // -2,147,483,647 - min int32 value + NULL
  val (pf | p, sz) = $BS.bs2unused_bytes( bs)
  val (rendered:(int)) = g1ofg0( $extfcall( int, "snprintf", p, i2sz 12, format_p, i))
  prval () = $BS.bytes_addback( format_pf | format_bs)
  val () = free format_bs
in
  ifcase
  | rendered <= 0 => bs where {
    val () = array_set_at_guint( !p, i2sz 0, '0')
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 1)
  }
  | rendered > 12 => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 12)
  }
  | _ => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz rendered)
  }
end

implement pack_uint32(i) =
let
  val PRI_fmt_bs = pack PRI_fmt where {
    macdef PRI_fmt0 = $extval( string, "PRIu32")
    val PRI_sz = g1ofg0( length PRI_fmt0)
    val PRI_fmt = believeme( PRI_fmt0, PRI_sz) where {
      extern castfn believeme{n:nat}( i: string, sz: size_t(n)):<> [n > 0; n < 9] string(n)
    }
  }
  var format_bs = create(length PRI_fmt_bs + 2) ++ $BS.pack '%' ++ PRI_fmt_bs
  val (fmt_pf | fmt_p, fmt_sz) = bs2unused_bytes( format_bs)
  val () = array_set_at_guint( !fmt_p, i2sz 0, $UN.cast{char} 0)
  val () = unused_bytes_addback( fmt_pf | format_bs, i2sz 0)
  val ( format_pf | format_p, _) = $BS.bs2bytes( format_bs)
  var bs: BytestringNSH0?
  val () = bs := $BS.create(i2sz 11) // 4294967295 - max int32 value + NULL
  val (pf | p, sz) = $BS.bs2unused_bytes( bs)
  val (rendered:(int)) = g1ofg0( $extfcall( int, "snprintf", p, i2sz 11, format_p, i))
  prval () = $BS.bytes_addback( format_pf | format_bs)
  val () = free format_bs
in
  ifcase
  | rendered <= 0 => bs where {
    val () = array_set_at_guint( !p, i2sz 0, '0')
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 1)
  }
  | rendered > 11 => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 11)
  }
  | _ => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz rendered)
  }
end

implement pack_double(i) =
let
  var bs: BytestringNSH0?
  val () = bs := $BS.create(i2sz 48) // hard to guess, as depending on platform size in range of 80-128 bits, so the size is quite random
  val (pf | p, sz) = $BS.bs2unused_bytes( bs)
  val (rendered:(int)) = g1ofg0( $extfcall( int, "snprintf", p, i2sz 48, "%f\0", i))
in
  ifcase
  | rendered <= 0 => bs where {
    val () = array_set_at_guint( !p, i2sz 0, '0')
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 1)
  }
  | rendered > 48 => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 48)
  }
  | _ => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz rendered)
  }
end

implement pack_float(i) =
let
  var bs: BytestringNSH0?
  val () = bs := $BS.create(i2sz 48) // hard to guess, as depending on platform size in range of 80-128 bits, so the size is quite random
  val (pf | p, sz) = $BS.bs2unused_bytes( bs)
  val (rendered:(int)) = g1ofg0( $extfcall( int, "snprintf", p, i2sz 48, "%f\0", i))
in
  ifcase
  | rendered <= 0 => bs where {
    val () = array_set_at_guint( !p, i2sz 0, '0')
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 1)
  }
  | rendered > 48 => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 48)
  }
  | _ => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz rendered)
  }
end

implement pack_int8(i) =
let
  val PRI_fmt_bs = pack PRI_fmt where {
    macdef PRI_fmt0 = $extval( string, "PRIi8")
    val PRI_sz = g1ofg0( length PRI_fmt0)
    val PRI_fmt = believeme( PRI_fmt0, PRI_sz) where {
      extern castfn believeme{n:nat}( i: string, sz: size_t(n)):<> [n > 0; n < 9] string(n)
    }
  }
  var format_bs = create(length PRI_fmt_bs + 2) ++ $BS.pack '%' ++ PRI_fmt_bs
  val (fmt_pf | fmt_p, fmt_sz) = bs2unused_bytes( format_bs)
  val () = array_set_at_guint( !fmt_p, i2sz 0, $UN.cast{char} 0)
  val () = unused_bytes_addback( fmt_pf | format_bs, i2sz 0)
  val ( format_pf | format_p, _) = $BS.bs2bytes( format_bs)
  var bs: BytestringNSH0?
  val () = bs := $BS.create(i2sz 5) // -127 - min int8 value + NULL
  val (pf | p, sz) = $BS.bs2unused_bytes( bs)
  val (rendered:(int)) = g1ofg0( $extfcall( int, "snprintf", p, i2sz 5, format_p, i))
  prval () = $BS.bytes_addback( format_pf | format_bs)
  val () = free format_bs
in
  ifcase
  | rendered <= 0 => bs where {
    val () = array_set_at_guint( !p, i2sz 0, '0')
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 1)
  }
  | rendered > 5 => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 5)
  }
  | _ => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz rendered)
  }
end

implement pack_uint8(i) =
let
  val PRI_fmt_bs = pack PRI_fmt where {
    macdef PRI_fmt0 = $extval( string, "PRIu8")
    val PRI_sz = g1ofg0( length PRI_fmt0)
    val PRI_fmt = believeme( PRI_fmt0, PRI_sz) where {
      extern castfn believeme{n:nat}( i: string, sz: size_t(n)):<> [n > 0; n < 9] string(n)
    }
  }
  var format_bs = create(length PRI_fmt_bs + 2) ++ $BS.pack '%' ++ PRI_fmt_bs
  val (fmt_pf | fmt_p, fmt_sz) = bs2unused_bytes( format_bs)
  val () = array_set_at_guint( !fmt_p, i2sz 0, $UN.cast{char} 0)
  val () = unused_bytes_addback( fmt_pf | format_bs, i2sz 0)
  val ( format_pf | format_p, _) = $BS.bs2bytes( format_bs)
  var bs: BytestringNSH0?
  val () = bs := $BS.create(i2sz 4) // 255 - max int8 value + NULL
  val (pf | p, sz) = $BS.bs2unused_bytes( bs)
  val (rendered:(int)) = g1ofg0( $extfcall( int, "snprintf", p, i2sz 4, format_p, i))
  prval () = $BS.bytes_addback( format_pf | format_bs)
  val () = free format_bs
in
  ifcase
  | rendered <= 0 => bs where {
    val () = array_set_at_guint( !p, i2sz 0, '0')
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 1)
  }
  | rendered > 4 => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 4)
  }
  | _ => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz rendered)
  }
end

implement pack_int16(i) =
let
  val PRI_fmt_bs = pack PRI_fmt where {
    macdef PRI_fmt0 = $extval( string, "PRIi16")
    val PRI_sz = g1ofg0( length PRI_fmt0)
    val PRI_fmt = believeme( PRI_fmt0, PRI_sz) where {
      extern castfn believeme{n:nat}( i: string, sz: size_t(n)):<> [n > 0; n < 9] string(n)
    }
  }
  var format_bs = create(length PRI_fmt_bs + 2) ++ $BS.pack '%' ++ PRI_fmt_bs
  val (fmt_pf | fmt_p, fmt_sz) = bs2unused_bytes( format_bs)
  val () = array_set_at_guint( !fmt_p, i2sz 0, $UN.cast{char} 0)
  val () = unused_bytes_addback( fmt_pf | format_bs, i2sz 0)
  val ( format_pf | format_p, _) = $BS.bs2bytes( format_bs)
  var bs: BytestringNSH0?
  val () = bs := $BS.create(i2sz 7) // -32678 - min int32 value + NULL
  val (pf | p, sz) = $BS.bs2unused_bytes( bs)
  val (rendered:(int)) = g1ofg0( $extfcall( int, "snprintf", p, i2sz 7, format_p, i))
  prval () = $BS.bytes_addback( format_pf | format_bs)
  val () = free format_bs
in
  ifcase
  | rendered <= 0 => bs where {
    val () = array_set_at_guint( !p, i2sz 0, '0')
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 1)
  }
  | rendered > 7 => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 7)
  }
  | _ => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz rendered)
  }
end

implement pack_uint16(i) =
let
  val PRI_fmt_bs = pack PRI_fmt where {
    macdef PRI_fmt0 = $extval( string, "PRIu16")
    val PRI_sz = g1ofg0( length PRI_fmt0)
    val PRI_fmt = believeme( PRI_fmt0, PRI_sz) where {
      extern castfn believeme{n:nat}( i: string, sz: size_t(n)):<> [n > 0; n < 9] string(n)
    }
  }
  var format_bs = create(length PRI_fmt_bs + 2) ++ $BS.pack '%' ++ PRI_fmt_bs
  val (fmt_pf | fmt_p, fmt_sz) = bs2unused_bytes( format_bs)
  val () = array_set_at_guint( !fmt_p, i2sz 0, $UN.cast{char} 0)
  val () = unused_bytes_addback( fmt_pf | format_bs, i2sz 0)
  val ( format_pf | format_p, _) = $BS.bs2bytes( format_bs)
  var bs: BytestringNSH0?
  val () = bs := $BS.create(i2sz 6) // 65535 - max int32 value + NULL
  val (pf | p, sz) = $BS.bs2unused_bytes( bs)
  val (rendered:(int)) = g1ofg0( $extfcall( int, "snprintf", p, i2sz 6, format_p, i))
  prval () = $BS.bytes_addback( format_pf | format_bs)
  val () = free format_bs
in
  ifcase
  | rendered <= 0 => bs where {
    val () = array_set_at_guint( !p, i2sz 0, '0')
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 1)
  }
  | rendered > 6 => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz 6)
  }
  | _ => bs where {
    val () = $BS.unused_bytes_addback( pf | bs, i2sz rendered)
  }
end

implement parse_uint32( i) = Some_vt( $UN.cast{uint32} v) where {
  prval _ = lemma_bytestring_param(i)
  val (pf | p, sz) = bs2bytes( i)
  val v = $extfcall(int, "atoi", p)
  prval _ = bytes_addback( pf | i)
}

implement reverse{len,offset,cap,ucap,refcnt}{dynamic}( i) = result where {
  prval () = lemma_bytestring_param i
  val i_sz = length i
  var result: BytestringNSH0?
  val () = result := create( i_sz)
  val (r_pf | r_p, r_sz) = bs2unused_bytes( result)
  val (i_pf | i_p, i_sz) = bs2bytes( i)
  val () = loop( r_pf, i_pf | i2sz 0, r_p, i_p) where {
    fun
      loop
      {n:nat | n <= len}{l,l1:agz}
      .<len-n>.
      ( dst_pf: !array_v(char, l1, len)
      , src_pf: !array_v(char, l, len)
      | i: size_t n
      , dst: ptr l1
      , src: ptr l
      ):<!wrt>
      void =
    if i = i_sz
    then ()
    else loop( dst_pf, src_pf | i + i2sz 1, dst, src) where {
      val () = array_set_at_guint( !dst, i, array_get_at_guint( !src, i_sz - i - 1))
    }
  }
  val () = unused_bytes_addback( r_pf | result, i_sz)
  prval () = bytes_addback( i_pf | i)
}

implement reverseC{len,offset,cap,ucap}{dynamic}( i) = i where {
  prval () = lemma_bytestring_param i
  val i_sz = length i
  val half_i_sz = i_sz / (i2sz 2)
  val (i_pf | i_p, i_sz) = bs2bytes( i)
  val () = loop( i_pf | i2sz 0, i_p) where {
    fun
      loop
      {n:nat | n <= len / 2}{l:agz}
      .<len-n>.
      ( dst_pf: !array_v(char, l, len)
      | i: size_t n
      , dst: ptr l
      ):<!wrt>
      void =
    if i = half_i_sz
    then ()
    else loop( dst_pf | i + i2sz 1, dst) where {
      val first = array_get_at_guint( !dst, i)
      val second = array_get_at_guint( !dst, i_sz - i - 1)
      val () = array_set_at_guint( !dst, i, second)
      val () = array_set_at_guint( !dst, i_sz - i - 1, first)
    }
  }
  prval () = bytes_addback( i_pf | i)
}