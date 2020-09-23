#include "share/atspre_staload.hats"
#define ATS_PACKNAME "bytestring_flag"

#define ATS_DYNLOADFLAG 0
#define ATS_EXTERN_PREFIX "bytestring"

staload "./../SATS/bytestring.sats"
staload UN = "prelude/SATS/unsafe.sats"
//staload "prelude/SATS/array.sats"

%{^
#include "unistd.h"
%}


typedef Bytestring_impl(len:int, offset: int, capacity: int, l:addr) =
  @( size_t(len)
   , size_t(offset) (* offset from the base pointer of length len *)
   , size_t(capacity) (* size of buffer, starting from base pointer *)
   , ptr(l) (* pointer to (unused_offset, refcnt, base buffer pointer) *)
   )

absvtype Bs_minus_struct(n:int, offset:int, cap: int, l:addr)

extern
prfun
  lemma_bytestring_impl_param
  {len,offset,cap:nat}{l:addr}
  ( v: !Bytestring_impl(len, offset, cap, l)
  ):
  [ (cap == 0 && l == null) || (cap > 0 && l > null); offset + len <= cap ] (* n should not exceed capacity *)
  void

dataview result_vb(c:bool, a:view+,b: view+) =
  | fail_vb(false, a, b) of a
  | succ_vb(true, a, b) of b

extern castfn
  bs_takeout_struct
  {a:viewt0ype}{n,cap:nat}
  ( bs: !Bytestring_vtype(n,cap) >> Bs_minus_struct( n, offset, cap, l)
  ):<>
  #[l,l1:addr]
  #[offset: nat]
  ( result_vb( cap > 0, void, ( (size_t, size_t, ptr l1) @ l, mfree_gc_v l, array_v(char, l1, cap), mfree_gc_v l1) )
  | Bytestring_impl(n, offset, cap, l)
  )

extern praxi
  bs_takeback_struct
  {a:viewt0ype}{n,offset,cap: nat}{l,l1:addr}
  ( result_vb( cap > 0, void, ( (size_t, size_t, ptr l1) @ l, mfree_gc_v l, array_v(char, l1, cap), mfree_gc_v l1))
  | bs: !Bs_minus_struct( n, offset, cap, l) >> Bytestring_vtype( n, cap)
  ):<> void

implement empty() =
let
in
  $UN.castvwtp0{Bytestring_vtype(0,0)} ( ( () | (i2sz(0), i2sz(0), i2sz(0), the_null_ptr)) )
end

extern fn
  memcpy
  {n,n1,n2:pos | n >= n1; n2 >= n1 }{l,l1:addr}
  ( !array_v(char?, l, n) >> array_v(char,l,n)
  , !array_v(char, l1, n2)
  | dst: ptr l
  , src: ptr l1
  , sz: size_t n1
  ): void = "mac#"
  
extern fn
  memcmp
  { n,cap1,cap2:pos
  | n <= cap1 && n <= cap2
  }
  { l1,l2:addr}
  ( !array_v(char, l1, cap1)
  , !array_v(char, l2, cap2)
  | lp: ptr l1
  , rp: ptr l2
  , ln: size_t n
  ):<> int = "mac#"

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

implement pack_string{n}(s) =
let
  val sz = length(s)
in
  if sz = 0
  then empty()
  else
    let
      val (s_pf, s_fpf | src) = string2pfptr s
      val (pf, fpf | ptr) = array_ptr_alloc<char>(sz)
      val () = memcpy( pf, s_pf | ptr, src, sz)
      prval () = s_fpf s_pf
      val (t_pf, t_fpf | p) = ptr_alloc<(size_t, size_t, ptr)>()
      val () = !p := (sz, i2sz(0), ptr)
    in
      $UN.castvwtp0{Bytestring_vtype(n,n)} ( ( (t_pf, t_fpf, pf, fpf) | (sz, i2sz(0), sz, p)) )
    end
end

implement pack_bytes{n}{l}(i_pf | i, sz) =
if sz = 0
then empty()
else
  let
    val (pf, fpf | ptr) = array_ptr_alloc<char>(sz)
    val () = memcpy( pf, i_pf | ptr, i, sz)
    val (t_pf, t_fpf | p) = ptr_alloc<(size_t, size_t, ptr)>()
    val () = !p := (sz, i2sz(0), ptr)
  in
    $UN.castvwtp0{Bytestring_vtype(n,n)} ( ( (t_pf, t_fpf, pf, fpf) | (sz, i2sz(0), sz, p)) )
  end
  
implement free{n}(v) =
let
  prval () = lemma_bytestring_param(v)
  val ( rpf | impl) = bs_takeout_struct(v)
  prval () = lemma_bytestring_impl_param(impl)
  val (n, offset, cap, tuple) = impl
  extern castfn __free{vt:viewt0ype}(x: vt): void
in
  if cap = 0
  then
    let
      prval fail_vb(pf) = rpf
      prval () = pf
      val () = __free(v)
    in
      ()
    end
  else
    let
      prval succ_vb( pf1 ) = rpf
      prval (tuple_pf, tuple_fpf, pf, fpf) = pf1
      val (unused_offset, refcnt, ptr) = !tuple
      val () = 
        if refcnt > 0
        then () where {
          val () = !tuple := (unused_offset, refcnt - i2sz(1), ptr) 
          extern prfn ___free{v:view}(x: v): void
          prval () = ___free( (tuple_pf, tuple_fpf, pf, fpf) )
        }
        else {
          val () = array_ptr_free( pf, fpf | ptr)
          val () = ptr_free( tuple_fpf, tuple_pf | tuple)
        }
      val () = __free(v)
    in
      ()
    end
end

implement create{cap}(sz) =
let
  val ( pf, fpf | p) = array_ptr_alloc<char>(sz)
  val ( t_pf, t_fpf | ptr) = ptr_alloc<(size_t, size_t, ptr)>()
  val () = !ptr := (i2sz(0), i2sz(0), p)
in
  $UN.castvwtp0 {Bytestring_vtype(0,cap)} (( (t_pf, t_fpf, pf, fpf) | (i2sz(0), i2sz 0, sz, ptr) ))
end

implement eq_bytestring_bytestring{l_n,r_n} ( l, r) =
let
  prval () = lemma_bytestring_param( l)
  prval () = lemma_bytestring_param( r)
  val (rl_pf | li) = bs_takeout_struct(l)
  val (rr_pf | ri) = bs_takeout_struct(r)
  prval () = lemma_bytestring_impl_param( li)
  prval () = lemma_bytestring_impl_param( ri)
  val ( ln, loffset, lcap, lt) = li
  val ( rn, roffset, rcap, rt) = ri
  val ret =
    ifcase
    | ln != rn => false 
    | ln = 0 => true
    | _ =>
      let
        prval succ_vb( lpf ) = rl_pf
        prval ( lt_pf, lt_fpf, l_pf, l_fpf ) = lpf
        prval succ_vb( rpf ) = rr_pf
        prval ( rt_pf, rt_fpf, r_pf, r_fpf ) = rpf
        prval (l_pf1, l_pf2) = array_v_split_at( l_pf | loffset)
        prval (r_pf1, r_pf2) = array_v_split_at( r_pf | roffset)
        val (_, _, lp) = !lt
        val (_,_, rp) = !rt
        val lptr = ptr_add( lp, loffset)
        val rptr = ptr_add( rp, roffset)
        val ret = memcmp( l_pf2, r_pf2 | lptr, rptr, ln)
        prval () = l_pf := array_v_unsplit( l_pf1, l_pf2)
        prval () = r_pf := array_v_unsplit( r_pf1, r_pf2)
        prval () = rl_pf := succ_vb( (lt_pf, lt_fpf, l_pf, l_fpf))
        prval () = rr_pf := succ_vb( (rt_pf, rt_fpf, r_pf, r_fpf))
      in
        if eq_g0int_int(ret, 0)
        then true
        else false
      end
  prval () = bs_takeback_struct( rl_pf | l)
  prval () = bs_takeback_struct( rr_pf | r)
in
  ret
end

implement neq_bytestring_bytestring( l, r) = not( eq_bytestring_bytestring( l, r))

extern
prfun
  {v:view+}
  clone_v
  ( i: !v
  ):<> v

implement append{l_n, r_n}(l, r) =
let
  prval () = lemma_bytestring_param( l)
  prval () = lemma_bytestring_param( r)
in
  ifcase
  | is_empty_capacity l => ref_bs r (* if l is an actually empty and has no buffer *)
  | is_empty r => ref_bs l
  | _ =>
    let
      val (rl_pf | li) = bs_takeout_struct(l)
      val (rr_pf | ri) = bs_takeout_struct(r)
      prval () = lemma_bytestring_impl_param( li)
      prval () = lemma_bytestring_impl_param( ri)
      val ( ln, loffset, lcap, lt) = li
      val ( rn, roffset, rcap, rt) = ri
      prval succ_vb( lpf) = rl_pf
      prval succ_vb( rpf) = rr_pf
      prval (lt_pf, lt_fpf, l_pf, l_fpf) = lpf
      val (lunused_offset1, lrefcnt, lp) = !lt
      val lunused_offset = g1ofg0 lunused_offset1
      prval (rt_pf, rt_fpf, r_pf, r_fpf) = rpf
      val ( _, _, rp) = !rt
      val () = assertloc( lunused_offset <= lcap)
      val () = assertloc( ln <= lunused_offset)
    in
      ifcase
      | ln + loffset != lunused_offset => result2 where {
        prval () = rl_pf := succ_vb((lt_pf, lt_fpf, l_pf, l_fpf))
        prval () = bs_takeback_struct( rl_pf | l)
        prval () = rr_pf := succ_vb((rt_pf, rt_fpf, r_pf, r_fpf))
        prval () = bs_takeback_struct( rr_pf | r)
        val result = create(ln + rn)
        val result1 = append( result, l)
        val result2 = append( result1, r)
        val () = free( result)
        val () = free( result1)
      }
      | lcap < rn + lunused_offset => result2 where {
        prval () = rl_pf := succ_vb((lt_pf, lt_fpf, l_pf, l_fpf))
        prval () = bs_takeback_struct( rl_pf | l)
        prval () = rr_pf := succ_vb((rt_pf, rt_fpf, r_pf, r_fpf))
        prval () = bs_takeback_struct( rr_pf | r)
        val result = create(ln + rn)
        val result1 = append( result, l)
        val result2 = append( result1, r)
        val () = free( result)
        val () = free( result1)
      }
      | _ => (* just use available space *)
        $UN.castvwtp0{Bytestring(l_n+r_n)}(( () | (ln + rn, loffset, lcap, lt ))) where {
          prval (l_pf1, l_pf2) = array_v_split_at( l_pf | lunused_offset)
          prval (r_pf1, r_pf2) = array_v_split_at( r_pf | roffset)
          val ldata = ptr_add( lp, lunused_offset)
          val () = memcpy( l_pf2, r_pf2 | ldata, ptr_add(rp, roffset), rn)
          prval () = l_pf := array_v_unsplit( l_pf1, l_pf2)
          prval () = r_pf := array_v_unsplit( r_pf1, r_pf2)
          val () = !lt := (lunused_offset + rn, lrefcnt + 1, lp)
          prval () = rl_pf := succ_vb( (lt_pf, lt_fpf, l_pf, l_fpf))
          prval () = rr_pf := succ_vb( (rt_pf, rt_fpf, r_pf, r_fpf))
          prval () = bs_takeback_struct( rl_pf | l)
          prval () = bs_takeback_struct( rr_pf | r)
        }
    end
end

implement is_empty_capacity{n,cap}(v) = let
  prval () = lemma_bytestring_param(v)
  val ( rpf | impl) = bs_takeout_struct(v)
  prval () = lemma_bytestring_impl_param( impl)
  val (_, _, cap, _) = impl
  prval () = bs_takeback_struct( rpf | v)
in
  if cap = 0
  then true
  else false
end

implement isnot_empty_capacity(v) = not( is_empty_capacity(v))

implement is_empty{n}(v) = let
  prval () = lemma_bytestring_param(v)
  val ( rpf | impl) = bs_takeout_struct(v)
  prval () = lemma_bytestring_impl_param( impl)
  val (n, _, _, _) = impl
  prval () = bs_takeback_struct( rpf | v)
in
  if n = 0
  then true
  else false
end

implement isnot_empty(v) = not( is_empty(v))

implement ref_bs{n}(i) =
if is_empty_capacity i
then empty()
else $UN.castvwtp0{Bytestring(n)}((( () | impl))) where {
  prval () = lemma_bytestring_param(i)
  val ( rpf | impl ) = bs_takeout_struct( i)
  prval succ_vb( pf) = rpf
  prval (t_pf, t_fpf, pf, fpf) = pf
  val (unused_offset, refcnt, p) = !(impl.3)
  val () = !(impl.3) := (unused_offset, refcnt + 1, p)
  prval () = rpf := succ_vb( (t_pf, t_fpf, pf, fpf))
  prval () = bs_takeback_struct( rpf | i)
}

implement appendC(l,r) = result where {
  prval () = lemma_bytestring_param(l)
  prval () = lemma_bytestring_param(r)
  val result = append( l, r)
  val () = free( l)
  val () = free( r)
}

implement bs2ptr(i) =
let
  prval () = lemma_bytestring_param(i)
  val (rpf | impl) = bs_takeout_struct(i)
  val (_, offset, cap, tuple) = impl
in
  if cap = 0
  then the_null_ptr where {
    prval () = bs_takeback_struct( rpf | i)
  }
  else ret where {
    prval succ_vb( pf) = rpf
    prval (tuple_pf, t_fpf, pf, fpf) = pf
    val (unused_offset, recfnt, p) = !tuple
    val ret = ptr_add<char>( p, offset)
    prval () = rpf := succ_vb( (tuple_pf, t_fpf, pf, fpf))

    prval () = bs_takeback_struct( rpf | i)
  }
end
  
implement drop{i,n}(n, i) =
let
  prval () = lemma_bytestring_param(i)
  val ( rpf | impl) = bs_takeout_struct(i)
  prval () = lemma_bytestring_impl_param(impl)
  val (len, offset, cap, tuple) = impl
in
  if len = 0
  then ref_bs i where {
    prval () = bs_takeback_struct( rpf | i)
  }
  else result where {
    prval succ_vb( pf) = rpf
    prval (t_pf, t_fpf, b_pf, b_fpf) = pf
    val (unused_offset, refcnt, p) = !tuple
    val () = !tuple := (unused_offset, refcnt + 1, p)
    val result = $UN.castvwtp0{Bytestring(i-n)} (( () | (len-n, offset+n, cap, tuple) )) (* TODO: we are cheating here by providing void proof, ideally we should clone view, but this looks like cheating as well, just more verbose *)
    prval () = rpf := succ_vb( (t_pf, t_fpf, b_pf, b_fpf))
    prval () = bs_takeback_struct( rpf | i)
  }
end

implement dropC{i,n}(n, i) =
let
  prval () = lemma_bytestring_param(i)
  val ( rpf | impl) = bs_takeout_struct(i)
  prval () = lemma_bytestring_impl_param(impl)
  val (len, offset, cap, tuple) = impl
in
  if len = 0
  then i where {
    prval () = bs_takeback_struct( rpf | i)
  }
  else result where {
    prval succ_vb( pf) = rpf
    prval (t_pf, t_fpf, b_pf, b_fpf) = pf
    val (unused_offset, refcnt, p) = !tuple
    val () = !tuple := (unused_offset, refcnt + 1, p)
    val result = $UN.castvwtp0{Bytestring(i-n)} (( () | (len-n, offset+n, cap, tuple) )) (* TODO: we are cheating here by providing void proof, ideally we should clone view, but this looks like cheating as well, just more verbose *)
    prval () = rpf := succ_vb( (t_pf, t_fpf, b_pf, b_fpf))
    prval () = bs_takeback_struct( rpf | i)
    extern castfn _free{vt:viewt0ype+}( i: vt):<> void
    val () = _free( i)
  }
end

implement take{i,n}(n, i) =
let
  prval () = lemma_bytestring_param(i)
  val ( rpf | impl) = bs_takeout_struct(i)
  prval () = lemma_bytestring_impl_param(impl)
  val (len, offset, cap, tuple) = impl
in
  if len = 0
  then ref_bs i where {
    prval () = bs_takeback_struct( rpf | i)
  }
  else result where {
    prval succ_vb( pf) = rpf
    prval (t_pf, t_fpf, b_pf, b_fpf) = pf
    val (unused_offset, refcnt, p) = !tuple
    val () = !tuple := (unused_offset, refcnt + 1, p)
    val result = $UN.castvwtp0{Bytestring(n)} (( () | (n, offset, cap, tuple) )) (* TODO: we are cheating here by providing void proof, ideally we should clone view, but this looks like cheating as well, just more verbose *)
    prval () = rpf := succ_vb( (t_pf, t_fpf, b_pf, b_fpf))
    prval () = bs_takeback_struct( rpf | i)
  }
end

implement takeC{i,n}(n, i) =
let
  prval () = lemma_bytestring_param(i)
  val ( rpf | impl) = bs_takeout_struct(i)
  prval () = lemma_bytestring_impl_param(impl)
  val (len, offset, cap, tuple) = impl
in
  if len = 0
  then i where {
    prval () = bs_takeback_struct( rpf | i)
  }
  else result where {
    prval succ_vb( pf) = rpf
    prval (t_pf, t_fpf, b_pf, b_fpf) = pf
    val (unused_offset, refcnt, p) = !tuple
    val () = !tuple := (unused_offset, refcnt + 1, p)
    val result = $UN.castvwtp0{Bytestring(n)} (( () | (n, offset, cap, tuple) )) (* TODO: we are cheating here by providing void proof, ideally we should clone view, but this looks like cheating as well, just more verbose *)
    prval () = rpf := succ_vb( (t_pf, t_fpf, b_pf, b_fpf))
    prval () = bs_takeback_struct( rpf | i)
    extern castfn _free{vt:viewt0ype+}( i: vt):<> void
    val () = _free( i)
  }
end

implement println(i) = {
  prval () = lemma_bytestring_param(i)
  val ( rpf | impl) = bs_takeout_struct(i)
  prval () = lemma_bytestring_impl_param(impl)
  val (len, offset, cap, tuple) = impl
  prval succ_vb( pf) = rpf
  prval (t_pf, t_fpf, b_pf, b_fpf) = pf
  val (unused_offset, refcnt, p) = !tuple
  val ptr = ptr_add<char>( p, offset)
  val _ = $extfcall( int, "write", 1, ptr, len)
  val _ = $extfcall( int, "write", 1, "\n", 1)
  prval () = rpf := succ_vb( (t_pf, t_fpf, b_pf, b_fpf))
  prval () = bs_takeback_struct( rpf | i)
}
implement printlnC(i) = {
  prval () = lemma_bytestring_param(i)
  val () = println(i)
  val () = free( i)
}