module Proto.V2.Ledger 
open FStar.Int32 
open FStar.Bytes 

module I32 = FStar.Int32 
module B = FStar.Bytes 

type location = {loc:string}

type item = {
  name:string;
  public_description:string;
  private_description:string;
  value:I32.t;
  level:I32.t;
  origin_loc:location;
  current_loc:location;
}

type ledger = {
  version:I32.t;
  world_name:string;
  log:list item
}
