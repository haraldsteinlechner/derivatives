
open System.Collections.Concurrent
open System.Collections.Generic
open FSharpx.Collections
open FSharpx.Collections.LazyList

let flip f a b = f b a

module Cantor =

    open FSharpx.Collections
    open FSharpx.Collections.LazyList

    let rec stripe = 
        function | Nil -> LazyList.empty
                 | Cons(Nil,xss) -> stripe xss
                 | Cons(Cons(x,xs),xss) -> consDelayed (LazyList.ofSeq [x]) (fun _ -> zipCons xs (stripe xss))

    and zipCons a b = 
        match a,b with
            | (Nil,ys) -> ys
            | (xs,Nil) -> LazyList.map (fun s -> cons s empty) xs
            | (Cons(x,xs),Cons(y,ys)) -> consDelayed (cons x y) (fun _ -> zipCons xs ys)


    let diagonal (xs : LazyList<_>) = xs |> stripe |> LazyList.concat

    let gen () = 
        let xs = LazyList.ofSeq <| Seq.initInfinite id
        let ys = LazyList.ofSeq <| Seq.initInfinite id
        xs |> LazyList.map (fun x ->
                 ys |> LazyList.map (fun y -> x+1,y+1)
        ) |> diagonal

    let map2Fair (xs : LazyList<'a>) (ys : LazyList<'b>) (f : 'a -> 'b -> 'c)  = 
        xs |> LazyList.map (fun x ->
                 ys |> LazyList.map (fun y -> f x y)
        ) |> diagonal

    let test () = gen () |> LazyList.take 10 |> LazyList.toList


type IP<'c,'a> =
    abstract member Eps : LazyList<'a> -> LazyList<'a>
    abstract member D : 'c -> IP<'c,'a>

let setCmp (xs:seq<_>) (ys:seq<_>) =
    let axs = HashSet<_>(xs)
    let bxs = HashSet<_>(ys)
    axs.Count = bxs.Count && xs |> Seq.forall (fun a -> bxs.Contains a) && ys |> Seq.forall (fun a -> bxs.Contains a) 

let eps (p : Lazy<IP<'c,'a>>) =
    LazyList.delayed (fun () -> 
        let current = LazyList.empty<'a>
        let rec run set =
            let r = p.Value.Eps set
            if System.Object.ReferenceEquals( r ,set ) then r else  r
        let r = run current
        r 
    )


let d<'c,'a> : Lazy<IP<'c,'a>> -> 'c -> IP<'c,'a> =
    let cache = ConcurrentDictionary<IP<'c,'a>*'c,IP<'c,'a>>()
    fun (p : Lazy<IP<'c,'a>>) (c : 'c)  -> cache.GetOrAdd((p.Value,c),System.Func<_,_>(fun (l,c) -> p.Value.D c))
    
type Empty<'c,'a>() =
    interface IP<'c,'a> with
        member x.D c = x :> _
        member x.Eps set = set

type Eps<'c,'a>(v : 'a) =
    let eps = LazyList.ofList [v]
    interface IP<'c,'a> with
        member x.D _ = Empty() :> _
        member x.Eps y = eps

type Char<'c when 'c : equality>(c : 'c) =
    interface IP<'c,'c> with
        member x.D c' =
            if c' = c then Eps c :> _
            else Empty() :> _
        member x.Eps set = set

type Nullability<'c,'a>(p : Lazy<IP<'c,'a>>) = 
    interface IP<'c,'a> with
        member x.D _ = Empty() :> _
        member x.Eps y = eps p

type Alt<'c,'a>(l : Lazy<IP<'c,'a>>, r : Lazy<IP<'c,'a>>) =
    let eps = LazyList.concat (LazyList.ofList [ yield eps r; yield eps l ] )
    interface IP<'c,'a> with
        member x.D c = Alt(lazy d l c, lazy d r c) :> IP<'c,'a>
        member x.Eps y = eps

let alt a b = Alt(a,b) :> IP<_,_>
let nullability p = Nullability p :> IP<_,_>

type Cat<'c,'a,'b,'d>(l : Lazy<IP<'c,'a>>,r : Lazy<IP<'c,'b>>, f : 'a -> 'b -> 'd) =
    let cat l r = Cat(l,r,f) :> IP<'c,'d> 
    let eps = Cantor.map2Fair (eps l) (eps r) f
    interface IP<'c,'d> with
        member x.D c = 
            alt (lazy (cat (lazy d l c) r) ) (lazy (cat (lazy nullability l) (lazy d r c)))         
        member x.Eps s = eps

type Red<'c,'a,'b>(y : Lazy<IP<'c,'a>>, f : 'a -> 'b) =
    let eps = eps y |> LazyList.map  f
    interface IP<'c,'b> with
        member x.Eps s = 
            eps
        member x.D c = 
            Red(lazy (d y c),f) :> IP<'c,'b>


let red p f = Red(lazy(p),f) :> IP<_,_>
let cat a b = Cat(lazy(a),lazy(b),(fun a b -> a,b)) :> IP<_,_>
let cat' a b = Cat(lazy(a),lazy(b),(fun a b -> [a;b]))  :> IP<_,_>

let fail<'c,'a> = Empty<_,_>() :> IP<'c,'a> 
let win v = Eps v :> IP<_,_>
let (<|>) a b = alt (lazy a) (lazy b)
let (<.>) a b = cat a b
let (<*>) a b = Cat(a,b,(fun a b -> a,b)) :> IP<_,_>
let (<..>) a b = cat' a b
let (!) a = Char(a) :> IP<_,_>
let (||>) p f = red p f

let parse xs (p : IP<'c,'a>) =
    let rec run xs p =
        match xs with 
         | []    -> eps (lazy p)
         | x::xs -> 
            let d = p.D x
            run xs d
    run xs p

let (!!) (x : string) = x.ToCharArray() |> Array.toList

let pSeq (xs : list<IP<'c,'a>>) =
    List.fold (fun s p -> red (cat' s (red p (Seq.toList << Seq.singleton))) List.concat) (win []) xs

let pString x = pSeq (!!x |> List.map (!)) ||> (fun s -> System.String(s |> List.toArray))
let pIgnore p = p ||> (fun _ -> ())

let testConc = parse !!"ab" ( !'a' <.> !'b' ) |> Seq.toList = [('a', 'b')]
let testAlt1 = parse !!""   ( !'a' <|> !'b' ) |> Seq.toList = []
let testAlt2 = parse !!"a"  ( !'a' <|> !'b' ) |> Seq.toList = ['a']
let testAlt3 = parse !!"b"  ( !'a' <|> !'b' ) |> Seq.toList = ['b']
let testE = parse !!"a" ( win 1 <.> !'a')
let testUrdar = parse !!"abc" (pString "abc")

let mutable exp = ref Unchecked.defaultof<IP<char,char>>
exp := alt (lazy (red (exp.Value <.> win 1) fst)) (lazy (!'a'))

[<EntryPoint>]
let main argv = 
    parse !!"ab" ( !'a' <.> !'b' ) |> Seq.toList |> printfn "%A"
//    printfn "%A" (LazyList.take 1 a |> LazyList.toArray)
    let a = parse !!"a" exp.Value
    printfn "%A" (LazyList.take 1 a |> LazyList.toArray)
    0 
