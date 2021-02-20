#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
#include "HATS/bytestring.hats"
staload BS="SATS/bytestring.sats"

implement main0() = {
  val s1 = $BS.create( i2sz 20)
  val s2 = s1 ++ $BS.pack "hello"
  prval () = $BS.lemma_bytestring_param( s2)
  val ( bytes_pf | bs1, bs_sz) = $BS.bs2bytes_ro( s2)
  val () = assertloc( bs_sz = i2sz 5)
  val s2 = minus_addback( bytes_pf| s2)
  val () = $BS.free(s2)
}