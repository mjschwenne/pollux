open Stdio
open Proto.Everything

let test : Everything.t =
  Everything.make ~i32i:3 ~i64o:(-1) ~u32r:[ 1; 2; 3 ] ~u64i:0 ?s32o:None
    ~s64r:[ -1 ] ~f32i:1024l ~f64o:3668L ~sf32r:[ -19l ] ~sf64i:26L ~bo:true
    ~sr:[ "Hello"; "World" ]
    ~bi:(String.to_bytes "DEADBEEF")
    ()

let () =
  print_endline "==== Pollux Encoding Test Program ====";
  printf "Proto Struct: %s\n" (Everything.show test);
  let proto_enc = Everything.to_proto test in
  print_endline "================ end ================="
