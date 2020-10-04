#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
staload BS="SATS/bytestring.sats"

implement main0() = {
  val s = $BS.empty()
  val () = $BS.free(s)
}