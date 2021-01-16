(* this module should contain ONLY generic template implementations, that are
   intended to be staloaded into a caller's DATS file. Otherwise, compiler will not
   be able to generate a resolved template's code
*)
#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
#define ATS_PACKNAME "bytestring"
#define ATS_EXTERN_PREFIX "bytestring_"

#include "./../HATS/bytestring_operators.hats" (* operators are needed *)
staload "./../SATS/bytestring.sats"

implement {env} take_while(env, f, i) = result where {
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
