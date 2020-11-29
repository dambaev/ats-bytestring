#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
  
#include "HATS/bytestring.hats"
staload BS="SATS/bytestring.sats"

fn
  test(): void = {
  var buf with buf_pf = @[char]('h', 'e','l','l','o')
  val bs = $BS.pack ( buf_pf | addr@buf, i2sz 5, i2sz 5)
  val () = $BS.free( buf_pf | bs)
}

implement main0() = {
  val () = test()
}