
type IP<'c,'a> =
    abstract member Eps : list<'a> -> list<'a>
    abstract member D : 'c -> IP<'c,'a>

let setCmp (xs:list<_>) (ys:list<_>) =
    let axs = System.Collections.Generic.HashSet<_>(xs)
    let bxs = System.Collections.Generic.HashSet<_>(ys)
    axs.Count = bxs.Count && xs |> List.forall (fun a -> bxs.Contains a) && ys |> List.forall (fun a -> bxs.Contains a) 

let eps (p : IP<_,_>) =
    let current = []
    let rec run set =
        let r = p.Eps set
        if not <| setCmp set r then run r else r
    run current

type Empty<'c,'a>() =
    interface IP<'c,'a> with
        member x.D c = x :> _
        member x.Eps y = []

type Eps<'c,'a>(v : 'a) =
    interface IP<'c,'a> with
        member x.D _ = Empty() :> _
        member x.Eps y = [v]

type Char<'c when 'c : equality>(c : 'c) =
    interface IP<'c,'c> with
        member x.D c' =
            if c' = c then Eps c :> _
            else Empty() :> _
        member x.Eps y = []

type Nullability<'c,'a>(p : Lazy<IP<'c,'a>>) = 
    interface IP<'c,'a> with
        member x.D _ = Empty() :> _
        member x.Eps y = eps p.Value

type Alt<'c,'a>(l : IP<'c,'a>, r : IP<'c,'a>) =
    interface IP<'c,'a> with
        member x.D c = Alt(l.D c, r.D c) :> _
        member x.Eps y = eps r  @ eps l

let alt a b = Alt(a,b) :> IP<_,_>
let nullability p = Nullability p :> IP<_,_>

type Cat<'c,'a,'b,'d>(l : Lazy<IP<'c,'a>>,r : Lazy<IP<'c,'b>>, f : 'a -> 'b -> 'd) =
    let cat l r = Cat(l,r,f) :> IP<'c,'d> 
    interface IP<'c,'d> with
        member x.D c = 
            alt (cat (lazy l.Value.D c) r) (cat (lazy nullability l) (lazy r.Value.D c)) 
        member x.Eps s =
            [ for a in eps l.Value do
                for b in eps r.Value do
                    yield f a b ] 

type Red<'c,'a,'b>(y : Lazy<IP<'c,'a>>, f : 'a -> 'b) =
    interface IP<'c,'b> with
        member x.Eps s = 
            [ for x in y.Value.Eps [] do yield f x ]
        member x.D c = Red(lazy (y.Value.D c),f) :> IP<'c,'b>


let red p f = Red(lazy(p),f) :> IP<_,_>
let cat a b = Cat(lazy(a),lazy(b),(fun a b -> a,b)) :> IP<_,_>
let cat' a b = Cat(lazy(a),lazy(b),(fun a b -> [a;b]))  :> IP<_,_>

let fail<'c,'a> = Empty<_,_>() :> IP<'c,'a> 
let win v = Eps v :> IP<_,_>
let (<|>) a b = alt a b
let (<.>) a b = cat a b
let (<*>) a b = Cat(a,b,(fun a b -> a,b)) :> IP<_,_>
let (<..>) a b = cat' a b
let (!) a = Char a :> IP<_,_>
let (||>) p f = red p f

let parse xs (p : IP<_,_>) =
    let cache = System.Collections.Generic.Dictionary()
    let rec run xs p =
        match xs with 
         | []    -> eps p
         | x::xs -> 
            match cache.TryGetValue x with
             | (true,v) -> run xs v
             | _ ->
                let d = p.D x
                cache.Add(x,d)
                run xs d
    run xs p

let (!!) (x : string) = x.ToCharArray() |> Array.toList

let testConc = parse !!"ab" ( !'a' <.> !'b' ) = [('a', 'b')]
let testAlt1 = parse !!""   ( !'a' <|> !'b' ) = []
let testAlt2 = parse !!"a"  ( !'a' <|> !'b' ) = ['a']
let testAlt3 = parse !!"b"  ( !'a' <|> !'b' ) = ['b']

let testE = parse !!"a" ( win 1 <.> !'a')

let pSeq (xs : list<IP<'c,'a>>) =
    List.fold (fun s p -> red (cat' s (red p List.singleton)) List.concat) (win []) xs

let pString x = pSeq (!!x |> List.map (!)) ||> (fun s -> System.String(s |> List.toArray))
let pIgnore p = p ||> (fun _ -> ())

let testUrdar = parse !!"abc" (pString "abc")

//let mutable exp = ref Unchecked.defaultof<IP<char,unit>>
//exp := ( ( (lazy exp.Value) <*> lazy (pString "1" |> pIgnore) ) |> pIgnore) <|> (pString "a" |> pIgnore)

[<EntryPoint>]
let main argv = 
    0 
