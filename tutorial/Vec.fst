module Vec

type vec (a:Type) : nat -> Type =
  | Nil : vec a 0
  | Cons : #n:nat -> hd:a -> tl:vec a n -> vec a (n + 1)

let rec append #a #n #m (v1:vec a n) (v2:vec a m)
  : vec a (n + m)
  = match v1 with
    | Nil -> v2
    | Cons hd tl -> Cons hd (append tl v2)

let rec reverse #a #n (v:vec a n)
  : vec a n
  = match v with
    | Nil -> Nil
    | Cons hd tl -> append (reverse tl) (Cons hd Nil)

let rec get #a #n (i:nat{i < n}) (v:vec a n)
  : a
  = let Cons hd tl = v in
        if i = 0 then hd
        else get (i - 1) tl

let int_vec = vec int

let test = int_vec 5

let test_vec : test = Cons 0 (Cons 1 (Cons 2 (Cons 3 (Cons 4 Nil))))

type dec : Type = 
| IMPLICIT
| REPEATED

type field (d:dec) (s:string) (id:nat) = 
| FIELD : int -> field d s id

let f1 : field IMPLICIT "test" 1 = FIELD 3
let f2 : field REPEATED "test" 3 = FIELD 5

type f1t = field IMPLICIT "test" 1 

let discrimiate #d1 #s1 #id1 #d2 #s2 #id2 (f1:field d1 s1 id1) (f2:field d2 s2 id2) = 
  if not (id1 = id2) then false else true

let t = discrimiate f1 f2
