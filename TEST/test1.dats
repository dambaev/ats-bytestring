#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
staload BS="SATS/bytestring.sats"
staload "DATS/bytestring_flat.dats"

implement main0() = {
  val s = $BS.empty()
  val () = $BS.free(s)
}