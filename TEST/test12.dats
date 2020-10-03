#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
staload BS="SATS/bytestring.sats"
staload "DATS/bytestring_flat.dats"

fn
  test(): $BS.BytestringNSH0 = bs where {
  val (pf, fpf | p) = array_ptr_alloc<char>( i2sz 100)
  val bs = $BS.pack ( pf, fpf | p, i2sz 0, i2sz 100)
}

implement main0() = {
  val s = test()
  val () = $BS.free( s)
}