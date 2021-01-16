(* this file's goal is to be included in order to introduce infix operators and overloads *)

(* staload the SATS file *)
staload BS="./../SATS/bytestring.sats"
staload "./../DATS/bytestring_flat_templates.dats" (* template definitions *)
#include "./../HATS/bytestring_operators.hats" (* operator definitions *)
