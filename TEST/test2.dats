#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
#include "HATS/bytestring.hats"
staload BS="SATS/bytestring.sats"

implement main0() = {
  val s = $BS.create(i2sz(1024))
  val () = free(s)
}