module Proto2
open FStar.UInt
open FStar.Int.Cast.Full
open FStar.Mul

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module B = FStar.Bytes 
module Seq = FStar.Seq
module Set = FStar.Set 
module List = FStar.List.Tot 

let vint64 = n:nat{n < pow2 64}
let vint32 = n:nat{n < pow2 32}

unopteq 
type proto_msg_descriptor : Type = {
  name: string;
  reserved: Set.set nat;
}

type proto_decorator : Type = 
| IMPLICIT
| OPTIONAL 
| REPEATED

type proto_field_descriptor (#t:Type) (dec : proto_decorator) (name : string) (id : nat) : Type = 
| FIELD : t -> proto_field_descriptor #t dec name id

let f1 : proto_field_descriptor IMPLICIT "field1" 0 = FIELD 5
let f2 : proto_field_descriptor OPTIONAL "field2" 0 = FIELD "test"

let discriminate #t1 #d1 #n1 #id1 #t2 #d2 #n2 #id2 
  (f1:proto_field_descriptor #t1 d1 n1 id1) (f2:proto_field_descriptor #t2 d2 n2 id2) = (id1 = id2)

let test_dis = discriminate f1 f2

let discriminate_type #t #d #s #id (ty:Type) = 


let test_dis_type = discriminate_type (proto_field_descriptor #(int) IMPLICIT "field3" 4)
