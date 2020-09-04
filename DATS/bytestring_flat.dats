#include "share/atspre_staload.hats"
#define ATS_PACKNAME "bytestring_flag"

#define ATS_DYNLOADFLAG 0
#define ATS_EXTERN_PREFIX "bytestring"

staload "SATS/bytestring.sats"
staload UN = "prelude/SATS/unsafe.sats"
//staload "prelude/SATS/array.sats"


typedef Bytestring_impl(n:int, cap: int, l:addr) =
  @( size_t(n)
   , size_t(cap)
   , size_t
   , ptr(l)
   )

absvtype Bs_minus_struct(n:int, cap: int, l:addr)

extern
prfun
  lemma_bytestring_impl_param
  {n,cap:nat}{l:addr}
  ( v: !Bytestring_impl(n, cap, l)
  ):
  [ n <= cap; (cap == 0 && l == null) || (cap > 0 && l > null) ] (* n should not exceed capacity *)
  void

dataview result_vb(c:bool, a:view+,b: view+) =
  | fail_vb(false, a, b) of a
  | succ_vb(true, a, b) of b

extern castfn
  bs_takeout_struct
  {a:viewt0ype}{n,cap: nat}{l:addr}
  ( bs: !Bytestring(n,cap) >> Bs_minus_struct( n, cap, l)
  ):<>
  #[l:addr]
  ( result_vb( cap > 0, void, (array_v(char, l, cap), mfree_gc_v l) )
  | Bytestring_impl(n,cap,l)
  )

extern praxi
  bs_takeback_struct
  {a:viewt0ype}{n,cap: nat}{l:addr}
  ( result_vb( cap > 0, void, (array_v(char, l, cap), mfree_gc_v l))
  | bs: !Bs_minus_struct( n, cap, l) >> Bytestring( n, cap)
  ):<> void

implement empty() =
let
in
  $UN.castvwtp0{Bytestring(0,0)} ( ( () | (i2sz(0), i2sz(0), i2sz(0), the_null_ptr)) )
end

extern fn
  memcpy
  {n,n1:pos | n >= n1 }{l,l1:agz}
  ( !array_v(char?, l, n) >> array_v(char,l,n)
  | dst: ptr l
  , src: ptr l1
  , sz: size_t n1
  ): void = "mac#"
  
extern fn
  memcmp
  {n,cap,cap1:pos }{l,l1:agz}
  ( !array_v(char, l, cap)
  , !array_v(char, l1, cap1)
  | lp: ptr l
  , rp: ptr l1
  , ln: size_t n
  ):<> int = "mac#"
  
implement pack_string{n}(s) =
let
  val sz = length(s)
in
  if sz = 0
  then empty()
  else
    let
      val src = string2ptr s
      val (pf, fpf | ptr) = array_ptr_alloc<char>(sz)
      val () = memcpy( pf | ptr, src, sz)
    in
      $UN.castvwtp0{Bytestring(n,n)} ( ( (pf, fpf) | (sz, sz, i2sz(0), ptr)) )
    end
end
  
implement free{n,cap}(v) =
let
  prval () = lemma_bytestring_param(v)
  val ( rpf | impl) = bs_takeout_struct(v)
  val (n, cap, refcnt, ptr) = impl
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
      prval (pf, fpf) = pf1
      val () = 
        if refcnt > 1
        then refcnt := refcnt - 1
        else
          array_ptr_free( pf, fpf | ptr)
      val () = __free(v)
    in
      ()
    end
end

implement create{cap}(sz) =
let
  val ( pf, fpf | p) = array_ptr_alloc<char>(sz)
in
  $UN.castvwtp0 {Bytestring(0,cap)} (( (pf, fpf) | (i2sz(0), sz, i2sz(0), p) ))
end

implement eq_bytestring_bytestring{l_n,r_n,l_cap,r_cap} ( l, r) =
let
  prval () = lemma_bytestring_param( l)
  prval () = lemma_bytestring_param( r)
  val (rl_pf | li) = bs_takeout_struct(l)
  val (rr_pf | ri) = bs_takeout_struct(r)
  prval () = lemma_bytestring_impl_param( li)
  prval () = lemma_bytestring_impl_param( ri)
  val ( ln, lcap, _, lp) = li
  val ( rn, rcap, _, rp) = ri
  val ret =
    ifcase
    | ln != rn => false 
    | ln = 0 => true
    | _ =>
      let
        prval succ_vb( lpf ) = rl_pf
        prval ( l_pf, l_fpf ) = lpf
        prval succ_vb( rpf ) = rr_pf
        prval ( r_pf, r_fpf ) = rpf
        val ret = 0 = memcmp( l_pf, r_pf | lp, rp, ln)
        prval () = rl_pf := succ_vb( (l_pf, l_fpf))
        prval () = rr_pf := succ_vb( (r_pf, r_fpf))
      in
        ret
      end
  prval () = bs_takeback_struct( rl_pf | l)
  prval () = bs_takeback_struct( rr_pf | r)
in
  ret
end

implement neq_bytestring_bytestring( l, r) = not( eq_bytestring_bytestring( l, r))

implement append(l, r) =
let
  prval () = lemma_bytestring_param( l)
  prval () = lemma_bytestring_param( r)
in
  ifcase
  | l = empty() => r
  | r = empty() => l
  | _ => 
    let
      val (rl_pf | li) = bs_takeout_struct(l)
      val (rr_pf | ri) = bs_takeout_struct(r)
      prval () = lemma_bytestring_impl_param( li)
      prval () = lemma_bytestring_impl_param( ri)
      val ( ln, lcap, _, lp) = li
      val ( rn, rcap, _, rp) = ri
      val ret =
        let
          prval succ_vb( lpf ) = rl_pf
          prval ( l_pf, l_fpf ) = lpf
          prval succ_vb( rpf ) = rr_pf
          prval ( r_pf, r_fpf ) = rpf
          val ret =
            ifcase
            | lcap - ln >= rn => 
            | _ =>
          prval () = rl_pf := succ_vb( (l_pf, l_fpf))
          prval () = rr_pf := succ_vb( (r_pf, r_fpf))
        in
          ret
        end
      prval () = bs_takeback_struct( rl_pf | l)
      prval () = bs_takeback_struct( rr_pf | r)
    in
      ret
    end
 end