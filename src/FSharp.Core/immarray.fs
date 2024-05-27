// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

namespace Microsoft.FSharp.Collections

//#nowarn "1118" // 'Make' marked 'inline', perhaps because a recursive value was marked 'inline'
#nowarn "193"

open System
open System.Diagnostics
open System.Collections.Generic
open Microsoft.FSharp.Core
open Microsoft.FSharp.Collections
open Microsoft.FSharp.Core.Operators
open Microsoft.FSharp.Core.CompilerServices
open Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicOperators

open System.Collections.Immutable

type immarray<'T> = ImmutableArray<'T>

/// Basic operations on immarrays
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
[<RequireQualifiedAccess>]
module ImmArray =

    let inline checkNonNull argName arg =
        if isNull arg then
            nullArg argName

    let inline slice startIndex count (array: ImmutableArray<'T>) =
        array.Slice(startIndex, count)

    [<CompiledName("Empty")>]
    let empty<'T> : ImmutableArray<'T> = ImmutableArray.Empty

    let inline indexNotFound () =
        raise (KeyNotFoundException(SR.GetString(SR.keyNotFoundAlt)))

    [<CompiledName("Length")>]
    let length (array: ImmutableArray<_>) =

        array.Length

    [<CompiledName("Last")>]
    let inline last (array: ImmutableArray<'T>) =

        if array.Length = 0 then
            invalidArg "array" LanguagePrimitives.ErrorStrings.InputArrayEmptyString

        array.[array.Length - 1]

    [<CompiledName("TryLast")>]
    let tryLast (array: ImmutableArray<'T>) =

        if array.Length = 0 then
            None
        else
            Some array.[array.Length - 1]

    [<CompiledName("Initialize")>]
    let inline init count initializer =
        let res = ImmutableArray.CreateBuilder(count)

        for i in 0 .. (count - 1) do
            res.[i] <- initializer i

        res.MoveToImmutable()

    [<CompiledName("ZeroCreate")>]
    let zeroCreate count =
        if count < 0 then
            invalidArgInputMustBeNonNegative "count" count

        ImmutableArray.CreateRange(Seq.replicate count Unchecked.defaultof<_>)

    [<CompiledName("Create")>]
    let create (count: int) (value: 'T) =
        if count < 0 then
            invalidArgInputMustBeNonNegative "count" count

        let array = ImmutableArray.CreateBuilder(count)

        for i = 0 to Operators.Checked.(-) array.Count 1 do // use checked arithmetic here to satisfy FxCop
            array.[i] <- value

        array.MoveToImmutable()

    [<CompiledName("TryHead")>]
    let tryHead (array: ImmutableArray<'T>) =

        if array.Length = 0 then
            None
        else
            Some array.[0]

    [<CompiledName("IsEmpty")>]
    let isEmpty (array: ImmutableArray<'T>) =

        array.Length = 0

    [<CompiledName("Tail")>]
    let tail (array: ImmutableArray<'T>) =

        if array.Length = 0 then
            invalidArg "array" (SR.GetString(SR.notEnoughElements))

        ImmutableArray.Create<'T>(array.AsSpan(1, array.Length - 1))

    //[<CompiledName("CopyTo")>]
    //let inline blit (source: ImmutableArray<'T>) (sourceIndex: int) (target: ImmutableArray<'T>) (targetIndex: int) (count: int) =
    //    array.Copy(source, sourceIndex, target, targetIndex, count)

    let concatArrays (arrs: ImmutableArray<ImmutableArray<'T>>) : ImmutableArray<'T> =
        let mutable acc = 0

        for h in arrs do
            acc <- acc + h.Length

        let res = ImmutableArray.CreateBuilder(acc)

        for i = 0 to arrs.Length - 1 do
            let h = arrs.[i]
            res.AddRange(h)

        res.MoveToImmutable()

    [<CompiledName("Concat")>]
    let concat (arrays: seq<ImmutableArray<'T>>) =

        match arrays with
        | :? (ImmutableArray<ImmutableArray<'T>>) as ts -> ts |> concatArrays // avoid a clone, since we only read the immarray
        | _ -> arrays |> ImmutableArray.CreateRange |> concatArrays

    [<CompiledName("Replicate")>]
    let replicate count initial =
        if count < 0 then
            invalidArgInputMustBeNonNegative "count" count

        let arr = ImmutableArray.CreateBuilder(count)

        for i = 0 to arr.Count - 1 do
            arr.Add(initial)

        arr.MoveToImmutable()

    [<CompiledName("Collect")>]
    let collect (mapping: 'T -> ImmutableArray<'U>) (array: ImmutableArray<'T>) : ImmutableArray<'U> =

        let len = array.Length

        let result = ImmutableArray.CreateBuilder<ImmutableArray<'U>>(len)

        for i = 0 to result.Count - 1 do
            result.Add(mapping array.[i])

        concatArrays (result.MoveToImmutable())

    [<CompiledName("SplitAt")>]
    let splitAt index (array: ImmutableArray<'T>) =

        if index < 0 then
            invalidArgInputMustBeNonNegative "index" index

        if array.Length < index then
            raise <| InvalidOperationException(SR.GetString(SR.notEnoughElements))

        if index = 0 then
            let right = slice 0 array.Length array

            empty, right
        elif index = array.Length then
            let left = slice 0 array.Length array

            left, empty
        else
            let res1 = slice 0 index array

            let res2 = slice index (array.Length - index) array

            res1, res2

    [<CompiledName("Take")>]
    let take count (array: ImmutableArray<'T>) =

        if count < 0 then
            invalidArgInputMustBeNonNegative "count" count

        if count = 0 then
            empty
        else
            if count > array.Length then
                raise <| InvalidOperationException(SR.GetString(SR.notEnoughElements))

            slice 0 count array

    [<CompiledName("TakeWhile")>]
    let takeWhile predicate (array: ImmutableArray<'T>) =

        if array.Length = 0 then
            empty
        else
            let mutable count = 0

            while count < array.Length && predicate array.[count] do
                count <- count + 1

            slice 0 count array

    let inline countByImpl
        (comparer: IEqualityComparer<'SafeKey>)
        ([<InlineIfLambda>] projection: 'T -> 'SafeKey)
        ([<InlineIfLambda>] getKey: 'SafeKey -> 'Key)
        (array: ImmutableArray<'T>)
        =
        let length = array.Length

        if length = 0 then
            empty
        else

            let dict = Dictionary comparer

            // Build the groupings
            for v in array do
                let safeKey = projection v
                let mutable prev = Unchecked.defaultof<_>

                if dict.TryGetValue(safeKey, &prev) then
                    dict.[safeKey] <- prev + 1
                else
                    dict.[safeKey] <- 1

            let res = ImmutableArray.CreateBuilder dict.Count
            let mutable i = 0

            for group in dict do
                res.Add(getKey group.Key, group.Value)
                i <- i + 1

            res.MoveToImmutable()

    // We avoid wrapping a StructBox, because under 64 JIT we get some "hard" tailcalls which affect performance
    let countByValueType (projection: 'T -> 'Key) (array: ImmutableArray<'T>) =
        countByImpl HashIdentity.Structural<'Key> projection id array

    // Wrap a StructBox around all keys in case the key type is itself a type using null as a representation
    let countByRefType (projection: 'T -> 'Key) (array: ImmutableArray<'T>) =
        countByImpl
            RuntimeHelpers.StructBox<'Key>.Comparer
            (projection >> RuntimeHelpers.StructBox)
            (fun sb -> sb.Value)
            array

    [<CompiledName("CountBy")>]
    let countBy (projection: 'T -> 'Key) (array: ImmutableArray<'T>) =

        if typeof<'Key>.IsValueType then
            countByValueType projection array
        else
            countByRefType projection array

    [<CompiledName("Append")>]
    let append (array1: ImmutableArray<'T>) (array2: ImmutableArray<'T>) =

        let n1 = array1.Length
        let n2 = array2.Length

        let res = ImmutableArray.CreateBuilder(n1 + n2)

        res.AddRange(array1)
        res.AddRange(array2)

        res.MoveToImmutable()

    [<CompiledName("Head")>]
    let head (array: ImmutableArray<'T>) =

        if array.Length = 0 then
            invalidArg "array" LanguagePrimitives.ErrorStrings.InputArrayEmptyString
        else
            array.[0]

    [<CompiledName("Copy")>]
    let copy (array: ImmutableArray<'T>) =

        ImmutableArray.Create<'T>(array.AsSpan())

    [<CompiledName("ToList")>]
    let toList (array: ImmutableArray<'T>) =

        let mutable res = ([]: 'T list)

        for i = array.Length - 1 downto 0 do
            res <- array.[i] :: res

        res

    [<CompiledName("OfList")>]
    let ofList (list: 'T list) =
        ImmutableArray.CreateRange(list)

    [<CompiledName("Indexed")>]
    let indexed (array: ImmutableArray<'T>) =

        let res = ImmutableArray.CreateBuilder(array.Length)

        for i = 0 to res.Capacity - 1 do
            res.Add(i, array.[i])

        res.MoveToImmutable()

    [<CompiledName("Iterate")>]
    let inline iter ([<InlineIfLambda>] action) (array: ImmutableArray<'T>) =

        for i = 0 to array.Length - 1 do
            action array.[i]

    [<CompiledName("Distinct")>]
    let distinct (array: ImmutableArray<'T>) =

        let temp = ImmutableArray.CreateBuilder array.Length

        let hashSet = HashSet<'T>(HashIdentity.Structural<'T>)

        for v in array do
            if hashSet.Add(v) then
                temp.Add(v)

        temp.ToImmutable()

    [<CompiledName("Map")>]
    let inline map ([<InlineIfLambda>] mapping: 'T -> 'U) (array: ImmutableArray<'T>) =

        let res = ImmutableArray.CreateBuilder array.Length

        for i = 0 to res.Capacity - 1 do
            res.Add(mapping array.[i])

        res.MoveToImmutable()

    [<CompiledName("Iterate2")>]
    let iter2 action (array1: ImmutableArray<'T>) (array2: ImmutableArray<'U>) =

        let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt(action)

        if array1.Length <> array2.Length then
            invalidArgDifferentArrayLength "array1" array1.Length "array2" array2.Length

        for i = 0 to array1.Length - 1 do
            f.Invoke(array1.[i], array2.[i])

    [<CompiledName("DistinctBy")>]
    let distinctBy projection (array: ImmutableArray<'T>) =

        let length = array.Length

        if length = 0 then
            empty
        else

            let temp = ImmutableArray.CreateBuilder array.Length
            let hashSet = HashSet<_>(HashIdentity.Structural<_>)

            for v in array do
                if hashSet.Add(projection v) then
                    temp.Add(v)

            temp.ToImmutable()

    [<CompiledName("Map2")>]
    let map2 mapping (array1: ImmutableArray<'T>) (array2: ImmutableArray<'U>) =

        let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt(mapping)

        if array1.Length <> array2.Length then
            invalidArgDifferentArrayLength "array1" array1.Length "array2" array2.Length

        let res = ImmutableArray.CreateBuilder array1.Length

        for i = 0 to array1.Length - 1 do
            res.[i] <- f.Invoke(array1.[i], array2.[i])

        res.MoveToImmutable()

    [<CompiledName("Map3")>]
    let map3 mapping (array1: ImmutableArray<'T1>) (array2: ImmutableArray<'T2>) (array3: ImmutableArray<'T3>) =

        let f = OptimizedClosures.FSharpFunc<_, _, _, _>.Adapt(mapping)
        let len1 = array1.Length

        if len1 <> array2.Length || len1 <> array3.Length then
            invalidArg3ArraysDifferent "array1" "array2" "array3" len1 array2.Length array3.Length

        let res = ImmutableArray.CreateBuilder len1

        for i = 0 to array1.Length - 1 do
            res.[i] <- f.Invoke(array1.[i], array2.[i], array3.[i])

        res.MoveToImmutable()

    [<CompiledName("MapIndexed2")>]
    let mapi2 mapping (array1: ImmutableArray<'T>) (array2: ImmutableArray<'U>) =

        let f = OptimizedClosures.FSharpFunc<_, _, _, _>.Adapt(mapping)

        if array1.Length <> array2.Length then
            invalidArgDifferentArrayLength "array1" array1.Length "array2" array2.Length

        let res = ImmutableArray.CreateBuilder array1.Length

        for i = 0 to array1.Length - 1 do
            res.[i] <- f.Invoke(i, array1.[i], array2.[i])

        res.MoveToImmutable()

    [<CompiledName("IterateIndexed")>]
    let iteri action (array: ImmutableArray<'T>) =

        let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt(action)

        for i = 0 to array.Length - 1 do
            f.Invoke(i, array.[i])

    [<CompiledName("IterateIndexed2")>]
    let iteri2 action (array1: ImmutableArray<'T>) (array2: ImmutableArray<'U>) =

        let f = OptimizedClosures.FSharpFunc<_, _, _, _>.Adapt(action)

        if array1.Length <> array2.Length then
            invalidArgDifferentArrayLength "array1" array1.Length "array2" array2.Length

        for i = 0 to array1.Length - 1 do
            f.Invoke(i, array1.[i], array2.[i])

    [<CompiledName("MapIndexed")>]
    let mapi (mapping: int -> 'T -> 'U) (array: ImmutableArray<'T>) =

        let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt(mapping)
        let res = ImmutableArray.CreateBuilder array.Length

        for i = 0 to array.Length - 1 do
            res.Add(f.Invoke(i, array.[i]))

        res.MoveToImmutable()

    [<CompiledName("MapFold")>]
    let mapFold<'T, 'State, 'Result> (mapping: 'State -> 'T -> 'Result * 'State) state (array: ImmutableArray<'T>) =

        match array.Length with
        | 0 -> empty, state
        | len ->
            let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt(mapping)
            let mutable state = state
            let res = ImmutableArray.CreateBuilder len

            for i = 0 to len - 1 do
                let h', s' = f.Invoke(state, array.[i])
                res.Add(h')
                state <- s'

            res.MoveToImmutable(), state

    [<CompiledName("MapFoldBack")>]
    let mapFoldBack<'T, 'State, 'Result> (mapping: 'T -> 'State -> 'Result * 'State) (array: ImmutableArray<'T>) state =

        match array.Length with
        | 0 -> empty, state
        | len ->
            let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt(mapping)
            let mutable acc = state
            let res = ImmutableArray.CreateBuilder len

            for i = len - 1 downto 0 do
                let h', s' = f.Invoke(array.[i], acc)
                res.Add(h')
                acc <- s'

            res.Reverse()

            res.MoveToImmutable(), acc

    [<CompiledName("Exists")>]
    let inline exists ([<InlineIfLambda>] predicate: 'T -> bool) (array: ImmutableArray<'T>) =

        let mutable state = false
        let mutable i = 0

        while not state && i < array.Length do
            state <- predicate array.[i]
            i <- i + 1

        state

    [<CompiledName("Contains")>]
    let inline contains value (array: ImmutableArray<'T>) =

        let mutable state = false
        let mutable i = 0

        while not state && i < array.Length do
            state <- value = array.[i]
            i <- i + 1

        state

    [<CompiledName("Exists2")>]
    let exists2 predicate (array1: ImmutableArray<_>) (array2: ImmutableArray<_>) =

        let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt(predicate)
        let len1 = array1.Length

        if len1 <> array2.Length then
            invalidArgDifferentArrayLength "array1" array1.Length "array2" array2.Length

        let rec loop i =
            i < len1 && (f.Invoke(array1.[i], array2.[i]) || loop (i + 1))

        loop 0

    [<CompiledName("ForAll")>]
    let forall (predicate: 'T -> bool) (array: ImmutableArray<'T>) =

        let len = array.Length

        let rec loop i =
            i >= len || (predicate array.[i] && loop (i + 1))

        loop 0

    [<CompiledName("ForAll2")>]
    let forall2 predicate (array1: ImmutableArray<_>) (array2: ImmutableArray<_>) =

        let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt(predicate)
        let len1 = array1.Length

        if len1 <> array2.Length then
            invalidArgDifferentArrayLength "array1" array1.Length "array2" array2.Length

        let rec loop i =
            i >= len1 || (f.Invoke(array1.[i], array2.[i]) && loop (i + 1))

        loop 0

    let inline groupByImpl
        (comparer: IEqualityComparer<'SafeKey>)
        ([<InlineIfLambda>] keyf: 'T -> 'SafeKey)
        ([<InlineIfLambda>] getKey: 'SafeKey -> 'Key)
        (array: ImmutableArray<'T>)
        =
        let length = array.Length

        if length = 0 then
            empty
        else
            let dict = Dictionary<_, ResizeArray<_>> comparer

            // Build the groupings
            for i = 0 to length - 1 do
                let v = array.[i]
                let safeKey = keyf v
                let mutable prev = Unchecked.defaultof<_>

                if dict.TryGetValue(safeKey, &prev) then
                    prev.Add v
                else
                    let prev = ResizeArray()
                    dict.[safeKey] <- prev
                    prev.Add v

            // Return the array-of-arrays.
            let result = ImmutableArray.CreateBuilder dict.Count

            for group in dict do
                result.Add(getKey group.Key, group.Value.ToImmutableArray())

            result.ToImmutable()

    // We avoid wrapping a StructBox, because under 64 JIT we get some "hard" tailcalls which affect performance
    let groupByValueType (keyf: 'T -> 'Key) (array: ImmutableArray<'T>) =
        groupByImpl HashIdentity.Structural<'Key> keyf id array

    // Wrap a StructBox around all keys in case the key type is itself a type using null as a representation
    let groupByRefType (keyf: 'T -> 'Key) (array: ImmutableArray<'T>) =
        groupByImpl
            RuntimeHelpers.StructBox<'Key>.Comparer
            (keyf >> RuntimeHelpers.StructBox)
            (fun sb -> sb.Value)
            array

    [<CompiledName("GroupBy")>]
    let groupBy (projection: 'T -> 'Key) (array: ImmutableArray<'T>) =

        if typeof<'Key>.IsValueType then
            groupByValueType projection array
        else
            groupByRefType projection array

    [<CompiledName("Pick")>]
    let pick chooser (array: ImmutableArray<_>) =

        let rec loop i =
            if i >= array.Length then
                indexNotFound ()
            else
                match chooser array.[i] with
                | None -> loop (i + 1)
                | Some res -> res

        loop 0

    [<CompiledName("TryPick")>]
    let tryPick chooser (array: ImmutableArray<_>) =

        let rec loop i =
            if i >= array.Length then
                None
            else
                match chooser array.[i] with
                | None -> loop (i + 1)
                | res -> res

        loop 0

    [<CompiledName("Choose")>]
    let choose (chooser: 'T -> 'U Option) (array: ImmutableArray<'T>) =

        let mutable i = 0
        let mutable first = Unchecked.defaultof<'U>
        let mutable found = false

        while i < array.Length && not found do
            let element = array.[i]

            match chooser element with
            | None -> i <- i + 1
            | Some b ->
                first <- b
                found <- true

        if i <> array.Length then

            let chunk1 = ImmutableArray.CreateBuilder((array.Length >>> 2) + 1)

            chunk1.[0] <- first
            let mutable count = 1
            i <- i + 1

            while count < chunk1.Count && i < array.Length do
                let element = array.[i]

                match chooser element with
                | None -> ()
                | Some b ->
                    chunk1.[count] <- b
                    count <- count + 1

                i <- i + 1

            if i < array.Length then
                let chunk2 = ImmutableArray.CreateBuilder(array.Length - i)

                count <- 0

                while i < array.Length do
                    let element = array.[i]

                    match chooser element with
                    | None -> ()
                    | Some b ->
                        chunk2.[count] <- b
                        count <- count + 1

                    i <- i + 1

                let res = ImmutableArray.CreateBuilder(chunk1.Count + count)

                res.AddRange(chunk1)
                res.AddRange(chunk2)
                res.MoveToImmutable()
            else
                chunk1.ToImmutable()
        else
            empty

    // The filter module is a space and performance for immarray.filter based optimization that uses
    // a bitarray to store the results of the filtering of every element of the immarray. This means
    // that the only additional temporary garbage that needs to be allocated is {array.Length/8} bytes.
    //
    // Other optimizations include:
    // - immarrays < 32 elements don't allocate any garbage at all
    // - when the predicate yields consecutive runs of true data that is >= 32 elements (and fall
    //   into maskArray buckets) are copied in chunks using System.Array.Copy
    module Filter =
        let private populateMask<'a> (f: 'a -> bool) (src: ImmutableArray<'a>) (maskArray: uint32 array) =
            let mutable count = 0

            for maskIdx = 0 to maskArray.Length - 1 do
                let srcIdx = maskIdx * 32
                let mutable mask = 0u

                if f src.[srcIdx + 0x00] then
                    mask <- mask ||| (1u <<< 0x00)
                    count <- count + 1

                if f src.[srcIdx + 0x01] then
                    mask <- mask ||| (1u <<< 0x01)
                    count <- count + 1

                if f src.[srcIdx + 0x02] then
                    mask <- mask ||| (1u <<< 0x02)
                    count <- count + 1

                if f src.[srcIdx + 0x03] then
                    mask <- mask ||| (1u <<< 0x03)
                    count <- count + 1

                if f src.[srcIdx + 0x04] then
                    mask <- mask ||| (1u <<< 0x04)
                    count <- count + 1

                if f src.[srcIdx + 0x05] then
                    mask <- mask ||| (1u <<< 0x05)
                    count <- count + 1

                if f src.[srcIdx + 0x06] then
                    mask <- mask ||| (1u <<< 0x06)
                    count <- count + 1

                if f src.[srcIdx + 0x07] then
                    mask <- mask ||| (1u <<< 0x07)
                    count <- count + 1

                if f src.[srcIdx + 0x08] then
                    mask <- mask ||| (1u <<< 0x08)
                    count <- count + 1

                if f src.[srcIdx + 0x09] then
                    mask <- mask ||| (1u <<< 0x09)
                    count <- count + 1

                if f src.[srcIdx + 0x0A] then
                    mask <- mask ||| (1u <<< 0x0A)
                    count <- count + 1

                if f src.[srcIdx + 0x0B] then
                    mask <- mask ||| (1u <<< 0x0B)
                    count <- count + 1

                if f src.[srcIdx + 0x0C] then
                    mask <- mask ||| (1u <<< 0x0C)
                    count <- count + 1

                if f src.[srcIdx + 0x0D] then
                    mask <- mask ||| (1u <<< 0x0D)
                    count <- count + 1

                if f src.[srcIdx + 0x0E] then
                    mask <- mask ||| (1u <<< 0x0E)
                    count <- count + 1

                if f src.[srcIdx + 0x0F] then
                    mask <- mask ||| (1u <<< 0x0F)
                    count <- count + 1

                if f src.[srcIdx + 0x10] then
                    mask <- mask ||| (1u <<< 0x10)
                    count <- count + 1

                if f src.[srcIdx + 0x11] then
                    mask <- mask ||| (1u <<< 0x11)
                    count <- count + 1

                if f src.[srcIdx + 0x12] then
                    mask <- mask ||| (1u <<< 0x12)
                    count <- count + 1

                if f src.[srcIdx + 0x13] then
                    mask <- mask ||| (1u <<< 0x13)
                    count <- count + 1

                if f src.[srcIdx + 0x14] then
                    mask <- mask ||| (1u <<< 0x14)
                    count <- count + 1

                if f src.[srcIdx + 0x15] then
                    mask <- mask ||| (1u <<< 0x15)
                    count <- count + 1

                if f src.[srcIdx + 0x16] then
                    mask <- mask ||| (1u <<< 0x16)
                    count <- count + 1

                if f src.[srcIdx + 0x17] then
                    mask <- mask ||| (1u <<< 0x17)
                    count <- count + 1

                if f src.[srcIdx + 0x18] then
                    mask <- mask ||| (1u <<< 0x18)
                    count <- count + 1

                if f src.[srcIdx + 0x19] then
                    mask <- mask ||| (1u <<< 0x19)
                    count <- count + 1

                if f src.[srcIdx + 0x1A] then
                    mask <- mask ||| (1u <<< 0x1A)
                    count <- count + 1

                if f src.[srcIdx + 0x1B] then
                    mask <- mask ||| (1u <<< 0x1B)
                    count <- count + 1

                if f src.[srcIdx + 0x1C] then
                    mask <- mask ||| (1u <<< 0x1C)
                    count <- count + 1

                if f src.[srcIdx + 0x1D] then
                    mask <- mask ||| (1u <<< 0x1D)
                    count <- count + 1

                if f src.[srcIdx + 0x1E] then
                    mask <- mask ||| (1u <<< 0x1E)
                    count <- count + 1

                if f src.[srcIdx + 0x1F] then
                    mask <- mask ||| (1u <<< 0x1F)
                    count <- count + 1

                maskArray.[maskIdx] <- mask

            count

        let private createMask<'a>
            (f: 'a -> bool)
            (src: ImmutableArray<'a>)
            (maskArrayOut: byref<uint32 array>)
            (leftoverMaskOut: byref<uint32>)
            =
            let maskArrayLength = src.Length / 0x20

            // null when there are less than 32 items in src immarray.
            let maskArray =
                if maskArrayLength = 0 then
                    null
                else
                    Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked<uint32> maskArrayLength

            let mutable count =
                match maskArray with
                | null -> 0
                | maskArray -> populateMask f src maskArray

            let leftoverMask =
                match src.Length % 0x20 with
                | 0 -> 0u
                | _ ->
                    let mutable mask = 0u
                    let mutable elementMask = 1u

                    for arrayIdx = maskArrayLength * 0x20 to src.Length - 1 do
                        if f src.[arrayIdx] then
                            mask <- mask ||| elementMask
                            count <- count + 1

                        elementMask <- elementMask <<< 1

                    mask

            maskArrayOut <- maskArray
            leftoverMaskOut <- leftoverMask
            count

        let private populateDstViaMask<'a>
            (src: ImmutableArray<'a>)
            (maskArray: uint32 array)
            (dst: ImmutableArray<'a>.Builder)
            =
            let mutable dstIdx = 0
            let mutable batchCount = 0

            for maskIdx = 0 to maskArray.Length - 1 do
                let mask = maskArray.[maskIdx]

                if mask = 0xFFFFFFFFu then
                    batchCount <- batchCount + 1
                else
                    let srcIdx = maskIdx * 0x20

                    if batchCount <> 0 then
                        let batchSize = batchCount * 0x20

                        let span = src.AsSpan(srcIdx - batchSize, batchSize)
                        dst.AddRange(span)
                        // This is probably wrong but trying to get things to compile
                        //System.Array.Copy(src, srcIdx - batchSize, dst, dstIdx, batchSize)
                        dstIdx <- dstIdx + batchSize
                        batchCount <- 0

                    if mask <> 0u then
                        if mask &&& (1u <<< 0x00) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x00]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x01) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x01]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x02) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x02]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x03) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x03]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x04) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x04]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x05) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x05]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x06) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x06]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x07) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x07]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x08) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x08]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x09) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x09]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x0A) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x0A]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x0B) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x0B]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x0C) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x0C]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x0D) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x0D]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x0E) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x0E]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x0F) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x0F]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x10) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x10]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x11) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x11]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x12) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x12]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x13) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x13]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x14) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x14]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x15) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x15]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x16) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x16]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x17) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x17]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x18) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x18]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x19) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x19]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x1A) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x1A]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x1B) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x1B]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x1C) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x1C]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x1D) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x1D]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x1E) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x1E]
                            dstIdx <- dstIdx + 1

                        if mask &&& (1u <<< 0x1F) <> 0u then
                            dst.[dstIdx] <- src.[srcIdx + 0x1F]
                            dstIdx <- dstIdx + 1

            if batchCount <> 0 then
                let srcIdx = maskArray.Length * 0x20
                let batchSize = batchCount * 0x20

                let span = src.AsSpan(srcIdx - batchSize, batchSize)
                dst.AddRange(span)
                // This is probably wrong but trying to get things to compile
                //System.Array.Copy(src, srcIdx - batchSize, dst, dstIdx, batchSize)
                dstIdx <- dstIdx + batchSize

            dstIdx

        let private filterViaMask
            (maskArray: uint32 array)
            (leftoverMask: uint32)
            (count: int)
            (src: ImmutableArray<_>)
            =
            let dst = ImmutableArray.CreateBuilder count

            let mutable dstIdx = 0

            let srcIdx =
                match maskArray with
                | null -> 0
                | _ ->
                    dstIdx <- populateDstViaMask src maskArray dst
                    maskArray.Length * 0x20

            let mutable elementMask = 1u

            for srcIdx = srcIdx to src.Length - 1 do
                if leftoverMask &&& elementMask <> 0u then
                    dst.[dstIdx] <- src.[srcIdx]
                    dstIdx <- dstIdx + 1

                elementMask <- elementMask <<< 1

            dst

        let filter f (src: ImmutableArray<_>) =
            let mutable maskArray = Unchecked.defaultof<_>
            let mutable leftOverMask = Unchecked.defaultof<_>

            match createMask f src &maskArray &leftOverMask with
            | 0 -> empty
            | count ->
                let res = filterViaMask maskArray leftOverMask count src
                res.ToImmutable()

    [<CompiledName("Filter")>]
    let filter predicate (array: ImmutableArray<_>) =

        Filter.filter predicate array

    [<CompiledName("Where")>]
    let where predicate (array: ImmutableArray<_>) =
        filter predicate array

    [<CompiledName("Except")>]
    let except (itemsToExclude: seq<_>) (array: ImmutableArray<_>) =
        checkNonNull "itemsToExclude" itemsToExclude

        if array.Length = 0 then
            array
        else
            let cached = HashSet(itemsToExclude, HashIdentity.Structural)
            array |> filter cached.Add

    [<CompiledName("Partition")>]
    let partition predicate (array: ImmutableArray<'T>) =

        let res = Array.zeroCreate array.Length
        let mutable upCount = 0
        let mutable downCount = array.Length - 1

        for x in array do
            if predicate x then
                res.[upCount] <- x
                upCount <- upCount + 1
            else
                res.[downCount] <- x
                downCount <- downCount - 1

        let res1 = ImmutableArray.Create<'T>(res.AsSpan(0, upCount))

        let res2 = ImmutableArray.CreateBuilder(array.Length - upCount)

        downCount <- array.Length - 1

        for i = 0 to res2.Count - 1 do
            res2.[i] <- res.[downCount]
            downCount <- downCount - 1

        res1, res2.MoveToImmutable()

    [<CompiledName("Find")>]
    let find predicate (array: ImmutableArray<_>) =

        let rec loop i =
            if i >= array.Length then
                indexNotFound ()
            else if predicate array.[i] then
                array.[i]
            else
                loop (i + 1)

        loop 0

    [<CompiledName("TryFind")>]
    let tryFind predicate (array: ImmutableArray<_>) =

        let rec loop i =
            if i >= array.Length then
                None
            else if predicate array.[i] then
                Some array.[i]
            else
                loop (i + 1)

        loop 0

    [<CompiledName("Skip")>]
    let skip count (array: ImmutableArray<'T>) =

        if count > array.Length then
            invalidArgOutOfRange "count" count "array.Length" array.Length

        if count = array.Length then
            empty
        else
            let count = max count 0
            slice count (array.Length - count) array

    [<CompiledName("SkipWhile")>]
    let skipWhile predicate (array: ImmutableArray<'T>) =

        let mutable i = 0

        while i < array.Length && predicate array.[i] do
            i <- i + 1

        match array.Length - i with
        | 0 -> empty
        | resLen -> slice i resLen array

    [<CompiledName("FindBack")>]
    let findBack predicate (array: ImmutableArray<_>) =

        let rec loop i =
            if i < 0 then indexNotFound ()
            elif predicate array.[i] then array.[i]
            else loop (i - 1)

        loop (array.Length - 1)

    [<CompiledName("TryFindBack")>]
    let tryFindBack predicate (array: ImmutableArray<_>) =

        let rec loop i =
            if i < 0 then
                None
            elif predicate array.[i] then
                Some array.[i]
            else
                loop (i - 1)

        loop (array.Length - 1)

    [<CompiledName("FindIndexBack")>]
    let findIndexBack predicate (array: ImmutableArray<_>) =

        let rec loop i =
            if i < 0 then indexNotFound ()
            elif predicate array.[i] then i
            else loop (i - 1)

        loop (array.Length - 1)

    [<CompiledName("TryFindIndexBack")>]
    let tryFindIndexBack predicate (array: ImmutableArray<_>) =

        let rec loop i =
            if i < 0 then None
            elif predicate array.[i] then Some i
            else loop (i - 1)

        loop (array.Length - 1)

    [<CompiledName("Windowed")>]
    let windowed windowSize (array: ImmutableArray<'T>) =

        if windowSize <= 0 then
            invalidArgInputMustBePositive "windowSize" windowSize

        let len = array.Length

        if windowSize > len then
            empty
        else
            let res = ImmutableArray.CreateBuilder(len - windowSize + 1)

            for i = 0 to len - windowSize do
                res.[i] <- slice i windowSize array

            res.MoveToImmutable()

    [<CompiledName("ChunkBySize")>]
    let chunkBySize chunkSize (array: ImmutableArray<'T>) =

        if chunkSize <= 0 then
            invalidArgInputMustBePositive "chunkSize" chunkSize

        let len = array.Length

        if len = 0 then
            empty
        else if chunkSize > len then
            ImmutableArray.Create<ImmutableArray<'T>> array
        else
            let chunkCount = (len - 1) / chunkSize + 1

            let res = ImmutableArray.CreateBuilder chunkCount

            for i = 0 to len / chunkSize - 1 do
                res.Add(slice (i * chunkSize) chunkSize array)

            if len % chunkSize <> 0 then
                res.Add(slice ((chunkCount - 1) * chunkSize) (len % chunkSize) array)

            res.MoveToImmutable()

    [<CompiledName("SplitInto")>]
    let splitInto count (array: ImmutableArray<_>) =

        if count <= 0 then
            invalidArgInputMustBePositive "count" count

        let len = array.Length

        if len = 0 then
            empty
        else
            let count = min count len
            let res = ImmutableArray.CreateBuilder count
            let minChunkSize = len / count
            let mutable startIndex = 0

            for i = 0 to len % count - 1 do
                res.[i] <- slice startIndex (minChunkSize + 1) array
                startIndex <- startIndex + minChunkSize + 1

            for i = len % count to count - 1 do
                res.[i] <- slice startIndex minChunkSize array
                startIndex <- startIndex + minChunkSize

            res.MoveToImmutable()

    [<CompiledName("Zip")>]
    let zip (array1: ImmutableArray<_>) (array2: ImmutableArray<_>) =

        let len1 = array1.Length

        if len1 <> array2.Length then
            invalidArgDifferentArrayLength "array1" array1.Length "array2" array2.Length

        let res = ImmutableArray.CreateBuilder len1

        for i = 0 to res.Count - 1 do
            res.[i] <- (array1.[i], array2.[i])

        res.MoveToImmutable()

    [<CompiledName("Zip3")>]
    let zip3 (array1: ImmutableArray<_>) (array2: ImmutableArray<_>) (array3: ImmutableArray<_>) =

        let len1 = array1.Length

        if len1 <> array2.Length || len1 <> array3.Length then
            invalidArg3ArraysDifferent "array1" "array2" "array3" len1 array2.Length array3.Length

        let res = ImmutableArray.CreateBuilder len1

        for i = 0 to res.Count - 1 do
            res.[i] <- (array1.[i], array2.[i], array3.[i])

        res.MoveToImmutable()

    [<CompiledName("AllPairs")>]
    let allPairs (array1: ImmutableArray<_>) (array2: ImmutableArray<_>) =

        let len1 = array1.Length
        let len2 = array2.Length
        let res = ImmutableArray.CreateBuilder(len1 * len2)

        for i = 0 to array1.Length - 1 do
            for j = 0 to array2.Length - 1 do
                res.[i * len2 + j] <- (array1.[i], array2.[j])

        res.MoveToImmutable()

    [<CompiledName("Unfold")>]
    let unfold<'T, 'State> (generator: 'State -> ('T * 'State) option) (state: 'State) =
        let res = ImmutableArray.CreateBuilder()

        let rec loop state =
            match generator state with
            | None -> ()
            | Some(x, s') ->
                res.Add(x)
                loop s'

        loop state
        res.ToImmutable()

    [<CompiledName("Unzip")>]
    let unzip (array: ImmutableArray<_>) =

        let len = array.Length
        let res1 = ImmutableArray.CreateBuilder len
        let res2 = ImmutableArray.CreateBuilder len

        for i = 0 to array.Length - 1 do
            let x, y = array.[i]
            res1.[i] <- x
            res2.[i] <- y

        res1.MoveToImmutable(), res2.MoveToImmutable()

    [<CompiledName("Unzip3")>]
    let unzip3 (array: ImmutableArray<_>) =

        let len = array.Length
        let res1 = ImmutableArray.CreateBuilder len
        let res2 = ImmutableArray.CreateBuilder len
        let res3 = ImmutableArray.CreateBuilder len

        for i = 0 to array.Length - 1 do
            let x, y, z = array.[i]
            res1.[i] <- x
            res2.[i] <- y
            res3.[i] <- z

        res1.MoveToImmutable(), res2.MoveToImmutable(), res3.MoveToImmutable()

    [<CompiledName("Reverse")>]
    let rev (array: ImmutableArray<'T>) =

        let res = array.ToBuilder()
        res.Reverse()
        res.MoveToImmutable()

    [<CompiledName("Fold")>]
    let fold<'T, 'State> (folder: 'State -> 'T -> 'State) (state: 'State) (array: ImmutableArray<'T>) =

        let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt(folder)
        let mutable state = state

        for i = 0 to array.Length - 1 do
            state <- f.Invoke(state, array.[i])

        state

    [<CompiledName("FoldBack")>]
    let foldBack<'T, 'State> (folder: 'T -> 'State -> 'State) (array: ImmutableArray<'T>) (state: 'State) =

        let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt(folder)
        let mutable res = state

        for i = array.Length - 1 downto 0 do
            res <- f.Invoke(array.[i], res)

        res

    [<CompiledName("FoldBack2")>]
    let foldBack2<'T1, 'T2, 'State> folder (array1: ImmutableArray<'T1>) (array2: ImmutableArray<'T2>) (state: 'State) =

        let f = OptimizedClosures.FSharpFunc<_, _, _, _>.Adapt(folder)
        let mutable res = state
        let len = array1.Length

        if len <> array2.Length then
            invalidArgDifferentArrayLength "array1" len "array2" array2.Length

        for i = len - 1 downto 0 do
            res <- f.Invoke(array1.[i], array2.[i], res)

        res

    [<CompiledName("Fold2")>]
    let fold2<'T1, 'T2, 'State> folder (state: 'State) (array1: ImmutableArray<'T1>) (array2: ImmutableArray<'T2>) =

        let f = OptimizedClosures.FSharpFunc<_, _, _, _>.Adapt(folder)
        let mutable state = state

        if array1.Length <> array2.Length then
            invalidArgDifferentArrayLength "array1" array1.Length "array2" array2.Length

        for i = 0 to array1.Length - 1 do
            state <- f.Invoke(state, array1.[i], array2.[i])

        state

    let foldSubRight f (array: ImmutableArray<_>) start fin acc =

        let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt(f)
        let mutable res = acc

        for i = fin downto start do
            res <- f.Invoke(array.[i], res)

        res

    let scanSubLeft f initState (array: ImmutableArray<_>) start fin =

        let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt(f)
        let mutable state = initState
        let res = ImmutableArray.CreateBuilder(2 + fin - start)
        res.Add(initState)

        for i = start to fin do
            state <- f.Invoke(state, array.[i])
            res.[i - start + 1] <- state

        res.MoveToImmutable()

    [<CompiledName("Scan")>]
    let scan<'T, 'State> folder (state: 'State) (array: ImmutableArray<'T>) =

        let len = array.Length
        scanSubLeft folder state array 0 (len - 1)

    [<CompiledName("ScanBack")>]
    let scanBack<'T, 'State> folder (array: ImmutableArray<'T>) (state: 'State) =

        let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt(folder)
        let mutable state = state

        let start = 0
        let fin = array.Length - 1

        let res = Array.zeroCreate (fin - start + 2)

        res.[fin - start + 1] <- state

        for i = fin downto start do
            state <- f.Invoke(array.[i], state)
            res.[i - start] <- state

        res.ToImmutableArray()

    [<CompiledName("Singleton")>]
    let inline singleton (value: 'T) =
        ImmutableArray.Create<'T>(value)

    [<CompiledName("Pairwise")>]
    let pairwise (array: ImmutableArray<'T>) =

        if array.Length < 2 then
            empty
        else
            init (array.Length - 1) (fun i -> array.[i], array.[i + 1])

    [<CompiledName("Reduce")>]
    let reduce reduction (array: ImmutableArray<_>) =

        let len = array.Length

        if len = 0 then
            invalidArg "array" LanguagePrimitives.ErrorStrings.InputArrayEmptyString
        else
            let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt(reduction)
            let mutable res = array.[0]

            for i = 1 to array.Length - 1 do
                res <- f.Invoke(res, array.[i])

            res

    [<CompiledName("ReduceBack")>]
    let reduceBack reduction (array: ImmutableArray<_>) =

        let len = array.Length

        if len = 0 then
            invalidArg "array" LanguagePrimitives.ErrorStrings.InputArrayEmptyString
        else
            foldSubRight reduction array 0 (len - 2) array.[len - 1]

    [<CompiledName("SortWith")>]
    let sortWith (comparer: 'T -> 'T -> int) (array: ImmutableArray<'T>) =

        let arr = array.AsSpan().ToArray()
        Array.sortInPlaceWith comparer arr
        arr.ToImmutableArray()

    [<CompiledName("SortBy")>]
    let sortBy projection (array: ImmutableArray<'T>) =

        let arr = array.AsSpan().ToArray()
        Array.sortInPlaceBy projection arr
        arr.ToImmutableArray()

    [<CompiledName("Sort")>]
    let sort (array: ImmutableArray<'T>) =

        let arr = array.AsSpan().ToArray()
        Array.sortInPlace arr
        arr.ToImmutableArray()

    [<CompiledName("SortByDescending")>]
    let inline sortByDescending projection array =

        let inline compareDescending a b =
            compare (projection b) (projection a)

        sortWith compareDescending array

    [<CompiledName("SortDescending")>]
    let inline sortDescending array =

        let inline compareDescending a b =
            compare b a

        sortWith compareDescending array

    [<CompiledName("ToSeq")>]
    let toSeq (array: ImmutableArray<'T>) =

        array :> 'T seq

    [<CompiledName("OfSeq")>]
    let ofSeq source =

        ImmutableArray.CreateRange source

    [<CompiledName("FindIndex")>]
    let findIndex predicate (array: ImmutableArray<_>) =

        let len = array.Length

        let rec go n =
            if n >= len then indexNotFound ()
            elif predicate array.[n] then n
            else go (n + 1)

        go 0

    [<CompiledName("TryFindIndex")>]
    let tryFindIndex predicate (array: ImmutableArray<_>) =

        let len = array.Length

        let rec go n =
            if n >= len then None
            elif predicate array.[n] then Some n
            else go (n + 1)

        go 0

    [<CompiledName("Permute")>]
    let permute indexMap (array: ImmutableArray<_>) =

        let res = ImmutableArray.CreateBuilder array.Length
        let inv = ImmutableArray.CreateBuilder array.Length

        for i = 0 to array.Length - 1 do
            let j = indexMap i

            if j < 0 || j >= array.Length then
                invalidArg "indexMap" (SR.GetString(SR.notAPermutation))

            res.[j] <- array.[i]
            inv.[j] <- 1uy

        for i = 0 to array.Length - 1 do
            if inv.[i] <> 1uy then
                invalidArg "indexMap" (SR.GetString(SR.notAPermutation))

        res.MoveToImmutable()

    [<CompiledName("Sum")>]
    let inline sum (array: ImmutableArray< ^T >) : ^T =

        let mutable acc = LanguagePrimitives.GenericZero< ^T>

        for i = 0 to array.Length - 1 do
            acc <- Checked.(+) acc array.[i]

        acc

    [<CompiledName("SumBy")>]
    let inline sumBy ([<InlineIfLambda>] projection: 'T -> ^U) (array: ImmutableArray<'T>) : ^U =

        let mutable acc = LanguagePrimitives.GenericZero< ^U>

        for i = 0 to array.Length - 1 do
            acc <- Checked.(+) acc (projection array.[i])

        acc

    [<CompiledName("Min")>]
    let inline min (array: ImmutableArray<_>) =

        if array.Length = 0 then
            invalidArg "array" LanguagePrimitives.ErrorStrings.InputArrayEmptyString

        let mutable acc = array.[0]

        for i = 1 to array.Length - 1 do
            let curr = array.[i]

            if curr < acc then
                acc <- curr

        acc

    [<CompiledName("MinBy")>]
    let inline minBy ([<InlineIfLambda>] projection) (array: ImmutableArray<_>) =

        if array.Length = 0 then
            invalidArg "array" LanguagePrimitives.ErrorStrings.InputArrayEmptyString

        let mutable accv = array.[0]
        let mutable acc = projection accv

        for i = 1 to array.Length - 1 do
            let currv = array.[i]
            let curr = projection currv

            if curr < acc then
                acc <- curr
                accv <- currv

        accv

    [<CompiledName("Max")>]
    let inline max (array: ImmutableArray<_>) =

        if array.Length = 0 then
            invalidArg "array" LanguagePrimitives.ErrorStrings.InputArrayEmptyString

        let mutable acc = array.[0]

        for i = 1 to array.Length - 1 do
            let curr = array.[i]

            if curr > acc then
                acc <- curr

        acc

    [<CompiledName("MaxBy")>]
    let inline maxBy projection (array: ImmutableArray<_>) =

        if array.Length = 0 then
            invalidArg "array" LanguagePrimitives.ErrorStrings.InputArrayEmptyString

        let mutable accv = array.[0]
        let mutable acc = projection accv

        for i = 1 to array.Length - 1 do
            let currv = array.[i]
            let curr = projection currv

            if curr > acc then
                acc <- curr
                accv <- currv

        accv

    [<CompiledName("Average")>]
    let inline average (array: ImmutableArray<'T>) =

        if array.Length = 0 then
            invalidArg "array" LanguagePrimitives.ErrorStrings.InputArrayEmptyString

        let mutable acc = LanguagePrimitives.GenericZero< ^T>

        for i = 0 to array.Length - 1 do
            acc <- Checked.(+) acc array.[i]

        LanguagePrimitives.DivideByInt< ^T> acc array.Length

    [<CompiledName("AverageBy")>]
    let inline averageBy ([<InlineIfLambda>] projection: 'T -> ^U) (array: ImmutableArray<'T>) : ^U =

        if array.Length = 0 then
            invalidArg "array" LanguagePrimitives.ErrorStrings.InputArrayEmptyString

        let mutable acc = LanguagePrimitives.GenericZero< ^U>

        for i = 0 to array.Length - 1 do
            acc <- Checked.(+) acc (projection array.[i])

        LanguagePrimitives.DivideByInt< ^U> acc array.Length

    [<CompiledName("CompareWith")>]
    let inline compareWith
        ([<InlineIfLambda>] comparer: 'T -> 'T -> int)
        (array1: ImmutableArray<'T>)
        (array2: ImmutableArray<'T>)
        =

        let length1 = array1.Length
        let length2 = array2.Length

        let mutable i = 0
        let mutable result = 0

        if length1 < length2 then
            while i < array1.Length && result = 0 do
                result <- comparer array1.[i] array2.[i]
                i <- i + 1
        else
            while i < array2.Length && result = 0 do
                result <- comparer array1.[i] array2.[i]
                i <- i + 1

        if result <> 0 then result
        elif length1 = length2 then 0
        elif length1 < length2 then -1
        else 1

    [<CompiledName("GetSubArray")>]
    let sub (array: ImmutableArray<'T>) (startIndex: int) (count: int) =

        if startIndex < 0 then
            invalidArgInputMustBeNonNegative "startIndex" startIndex

        if count < 0 then
            invalidArgInputMustBeNonNegative "count" count

        if startIndex + count > array.Length then
            invalidArgOutOfRange "count" count "array.Length" array.Length

        slice startIndex count array

    [<CompiledName("Item")>]
    let item index (array: ImmutableArray<_>) =
        array.[index]

    [<CompiledName("TryItem")>]
    let tryItem index (array: ImmutableArray<'T>) =

        if index < 0 || index >= array.Length then
            None
        else
            Some(array.[index])

    [<CompiledName("Get")>]
    let get (array: ImmutableArray<_>) index =
        array.[index]

    [<CompiledName("Fill")>]
    let fill (target: ImmutableArray<'T>) (targetIndex: int) (count: int) (value: 'T) =

        if targetIndex < 0 then
            invalidArgInputMustBeNonNegative "targetIndex" targetIndex

        if count < 0 then
            invalidArgInputMustBeNonNegative "count" count

        let target = target.ToBuilder()

        for i = targetIndex to targetIndex + count - 1 do
            target.[i] <- value

        target.MoveToImmutable()

    [<CompiledName("ExactlyOne")>]
    let exactlyOne (array: ImmutableArray<'T>) =

        if array.Length = 1 then
            array.[0]
        elif array.Length = 0 then
            invalidArg "array" LanguagePrimitives.ErrorStrings.InputSequenceEmptyString
        else
            invalidArg "array" (SR.GetString(SR.inputSequenceTooLong))

    [<CompiledName("TryExactlyOne")>]
    let tryExactlyOne (array: ImmutableArray<'T>) =

        if array.Length = 1 then
            Some array.[0]
        else
            None

    let transposeArrays (array: ImmutableArray<ImmutableArray<'T>>) =
        let len = array.Length

        if len = 0 then
            empty
        else
            let lenInner = array.[0].Length

            for j in 1 .. len - 1 do
                if lenInner <> array.[j].Length then
                    invalidArgDifferentArrayLength
                        "array.[0]"
                        lenInner
                        (String.Format("array.[{0}]", j))
                        array.[j].Length

            let result = ImmutableArray.CreateBuilder lenInner

            for i in 0 .. lenInner - 1 do
                let resI = ImmutableArray.CreateBuilder len

                for j in 0 .. len - 1 do
                    resI.[j] <- array.[j].[i]

                result.[i] <- resI.MoveToImmutable()

            result.MoveToImmutable()

    [<CompiledName("Transpose")>]
    let transpose (arrays: seq<ImmutableArray<'T>>) =

        match arrays with
        | :? (ImmutableArray<ImmutableArray<'T>>) as ts -> ts |> transposeArrays // avoid a clone, since we only read the immarray
        | _ -> arrays |> ImmutableArray.CreateRange |> transposeArrays

    [<CompiledName("Truncate")>]
    let truncate count (array: ImmutableArray<'T>) =

        if count <= 0 then
            empty
        else
            let len = array.Length
            let count' = Operators.min count len
            slice 0 count' array

    [<CompiledName("RemoveAt")>]
    let removeAt (index: int) (source: ImmutableArray<'T>) : ImmutableArray<'T> =

        if index < 0 || index >= source.Length then
            invalidArg "index" "index must be within bounds of the array"

        source.RemoveAt index

    [<CompiledName("RemoveManyAt")>]
    let removeManyAt (index: int) (count: int) (source: ImmutableArray<'T>) : ImmutableArray<'T> =

        if index < 0 || index > source.Length - count then
            invalidArg "index" "index must be within bounds of the immarray"

        let length = source.Length - count
        let result = ImmutableArray.CreateBuilder length

        if index > 0 then
            result.AddRange<'T>(source.AsSpan(0, index))

        if length - index > 0 then
            result.AddRange<'T>(source.AsSpan(index + count, length - index))

        result.MoveToImmutable()

    [<CompiledName("UpdateAt")>]
    let updateAt (index: int) (value: 'T) (source: ImmutableArray<'T>) : ImmutableArray<'T> =

        if index < 0 || index >= source.Length then
            invalidArg "index" "index must be within bounds of the immarray"

        let result = source.ToBuilder()
        result.[index] <- value

        result.MoveToImmutable()

    [<CompiledName("InsertAt")>]
    let insertAt (index: int) (value: 'T) (source: ImmutableArray<'T>) : ImmutableArray<'T> =

        if index < 0 || index > source.Length then
            invalidArg "index" "index must be within bounds of the immarray"

        let length = source.Length + 1
        let result = ImmutableArray.CreateBuilder length

        if index > 0 then
            result.AddRange(source.AsSpan(0, index))

        result.Add(value)

        if source.Length - index > 0 then
            result.AddRange(source.AsSpan(index, source.Length - index))

        result.MoveToImmutable()

    [<CompiledName("InsertManyAt")>]
    let insertManyAt (index: int) (values: seq<'T>) (source: ImmutableArray<'T>) : ImmutableArray<'T> =

        if index < 0 || index > source.Length then
            invalidArg "index" "index must be within bounds of the immarray"

        let valuesArray = Seq.toArray values

        if valuesArray.Length = 0 then
            source
        else
            let length = source.Length + valuesArray.Length
            let result = ImmutableArray.CreateBuilder length

            if index > 0 then
                result.AddRange(source.AsSpan(0, index))

            result.AddRange(valuesArray)

            if source.Length - index > 0 then
                result.AddRange(source.AsSpan(index, source.Length - index))

            result.MoveToImmutable()

//module Parallel =
//    open System.Threading
//    open System.Threading.Tasks
//    open System.Collections.Concurrent

//    [<CompiledName("Exists")>]
//    let exists (predicate: 'T -> bool) (array: ImmutableArray<'T>) =
//

//        Parallel
//            .For(
//                0,
//                array.Length,
//                (fun i pState ->
//                    if predicate array[i] then
//                        pState.Stop())
//            )
//            .IsCompleted
//        |> not

//    [<CompiledName("ForAll")>]
//    let forall (predicate: 'T -> bool) (array: ImmutableArray<'T>) =
//        // Not exists $condition <==> (opposite of $condition is true forall)
//        exists (predicate >> not) immarray |> not

//    [<CompiledName("TryFindIndex")>]
//    let tryFindIndex predicate (array: ImmutableArray<_>) =
//

//        let pResult =
//            Parallel.For(
//                0,
//                array.Length,
//                (fun i pState ->
//                    if predicate array[i] then
//                        pState.Break())
//            )

//        pResult.LowestBreakIteration |> Option.ofNullable |> Option.map int

//    [<CompiledName("TryFind")>]
//    let tryFind predicate (array: ImmutableArray<_>) =
//        immarray |> tryFindIndex predicate |> Option.map (fun i -> immarray[i])

//    [<CompiledName("TryPick")>]
//    let tryPick chooser (array: ImmutableArray<_>) =
//
//        let allChosen = new System.Collections.Concurrent.ConcurrentDictionary<_, _>()

//        let pResult =
//            Parallel.For(
//                0,
//                array.Length,
//                (fun i pState ->
//                    match chooser immarray[i] with
//                    | None -> ()
//                    | chosenElement ->
//                        allChosen[i] <- chosenElement
//                        pState.Break())
//            )

//        pResult.LowestBreakIteration
//        |> Option.ofNullable
//        |> Option.bind (fun i -> allChosen[int i])

//    [<CompiledName("Choose")>]
//    let choose chooser (array: ImmutableArray<'T>) =
//
//        let inputLength = array.Length

//        let isChosen: bool immarray =
//            Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked inputLength

//        let results: ImmutableArray<'U> =
//            Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked inputLength

//        let mutable outputLength = 0

//        Parallel.For(
//            0,
//            inputLength,
//            (fun () -> 0),
//            (fun i _ count ->
//                match chooser array.[i] with
//                | None -> count
//                | Some v ->
//                    isChosen.[i] <- true
//                    results.[i] <- v
//                    count + 1),
//            Action<int>(fun x -> System.Threading.Interlocked.Add(&outputLength, x) |> ignore)
//        )
//        |> ignore

//        let output =
//            Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked outputLength

//        let mutable curr = 0

//        for i = 0 to isChosen.Length - 1 do
//            if isChosen.[i] then
//                output.[curr] <- results.[i]
//                curr <- curr + 1

//        output

//    [<CompiledName("Collect")>]
//    let collect (mapping: 'T -> ImmutableArray<'U>) (array: ImmutableArray<'T>) : ImmutableArray<'U> =
//
//        let inputLength = array.Length

//        let result =
//            Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked inputLength

//        Parallel.For(0, inputLength, (fun i -> result.[i] <- mapping array.[i]))
//        |> ignore

//        concatArrays result

//    [<CompiledName("Map")>]
//    let map (mapping: 'T -> 'U) (array: ImmutableArray<'T>) : ImmutableArray<'U> =
//
//        let inputLength = array.Length

//        let result =
//            Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked inputLength

//        Parallel.For(0, inputLength, (fun i -> result.[i] <- mapping array.[i]))
//        |> ignore

//        result

//    [<CompiledName("MapIndexed")>]
//    let mapi mapping (array: ImmutableArray<'T>) =
//
//        let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt(mapping)
//        let inputLength = array.Length

//        let result =
//            Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked inputLength

//        Parallel.For(0, inputLength, (fun i -> result.[i] <- f.Invoke(i, array.[i])))
//        |> ignore

//        result

//    // The following two parameters were benchmarked and found to be optimal.
//    // Benchmark was run using: 11th Gen Intel Core i9-11950H 2.60GHz, 1 CPU, 16 logical and 8 physical cores
//    let maxPartitions = Environment.ProcessorCount // The maximum number of partitions to use
//    let minChunkSize = 256 // The minimum size of a chunk to be sorted in parallel

//    let createPartitionsUpToWithMinChunkSize maxIdxExclusive minChunkSize (array: ImmutableArray<'T>) =
//        [|
//            let chunkSize =
//                match maxIdxExclusive with
//                | smallSize when smallSize < minChunkSize -> smallSize
//                | biggerSize when biggerSize % maxPartitions = 0 -> biggerSize / maxPartitions
//                | biggerSize -> (biggerSize / maxPartitions) + 1

//            let mutable offset = 0

//            while (offset + chunkSize) < maxIdxExclusive do
//                yield new immarraySegment<'T>(array, offset, chunkSize)
//                offset <- offset + chunkSize

//            yield new immarraySegment<'T>(array, offset, maxIdxExclusive - offset)
//        |]

//    let createPartitionsUpTo maxIdxExclusive (array: ImmutableArray<'T>) =
//        createPartitionsUpToWithMinChunkSize maxIdxExclusive minChunkSize immarray

//    (* This function is there also as a support vehicle for other aggregations.
//       It is public in order to be called from inlined functions, the benefit of inlining call into it is significant *)
//    [<CompiledName("ReduceBy")>]
//    let reduceBy (projection: 'T -> 'U) (reduction: 'U -> 'U -> 'U) (array: ImmutableArray<'T>) =
//

//        if array.Length = 0 then
//            invalidArg "array" LanguagePrimitives.ErrorStrings.InputArrayEmptyString

//        let chunks = createPartitionsUpToWithMinChunkSize array.Length 2 immarray // We need at least 2 elements/chunk for 'reduction'

//        let chunkResults =
//            Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked chunks.Length

//        Parallel.For(
//            0,
//            chunks.Length,
//            fun chunkIdx ->
//                let chunk = chunks[chunkIdx]
//                let mutable res = projection immarray[chunk.Offset]
//                let lastIdx = chunk.Offset + chunk.Count - 1

//                for i = chunk.Offset + 1 to lastIdx do
//                    let projected = projection immarray[i]
//                    res <- reduction res projected

//                chunkResults[chunkIdx] <- res
//        )
//        |> ignore

//        let mutable finalResult = chunkResults[0]

//        for i = 1 to chunkResults.Length - 1 do
//            finalResult <- reduction finalResult chunkResults[i]

//        finalResult

//    [<CompiledName("Reduce")>]
//    let inline reduce ([<InlineIfLambda>] reduction) (array: ImmutableArray<_>) =
//        immarray |> reduceBy id reduction

//    let inline vFst struct (a, _) =
//        a

//    let inline vSnd struct (_, b) =
//        b

//    [<CompiledName("MinBy")>]
//    let inline minBy ([<InlineIfLambda>] projection) (array: ImmutableArray<_>) =

//        immarray
//        |> reduceBy (fun x -> struct (projection x, x)) (fun a b -> if vFst a < vFst b then a else b)
//        |> vSnd

//    [<CompiledName("Min")>]
//    let inline min (array: ImmutableArray<_>) =
//        immarray |> reduce (fun a b -> if a < b then a else b)

//    [<CompiledName("SumBy")>]
//    let inline sumBy ([<InlineIfLambda>] projection: 'T -> ^U) (array: ImmutableArray<'T>) : ^U =
//        if array.Length = 0 then
//            LanguagePrimitives.GenericZero
//        else
//            immarray |> reduceBy projection Operators.Checked.(+)

//    [<CompiledName("Sum")>]
//    let inline sum (array: ImmutableArray<^T>) : ^T =
//        immarray |> sumBy id

//    [<CompiledName("MaxBy")>]
//    let inline maxBy projection (array: ImmutableArray<_>) =

//        immarray
//        |> reduceBy (fun x -> struct (projection x, x)) (fun a b -> if vFst a > vFst b then a else b)
//        |> vSnd

//    [<CompiledName("Max")>]
//    let inline max (array: ImmutableArray<_>) =
//        immarray |> reduce (fun a b -> if a > b then a else b)

//    [<CompiledName("AverageBy")>]
//    let inline averageBy ([<InlineIfLambda>] projection: 'T -> ^U) (array: ImmutableArray<'T>) : ^U =
//        let sum = immarray |> reduceBy projection Operators.Checked.(+)
//        LanguagePrimitives.DivideByInt sum (array.Length)

//    [<CompiledName("Average")>]
//    let inline average (array: ImmutableArray<'T>) =
//        immarray |> averageBy id

//    [<CompiledName("Zip")>]
//    let zip (array1: ImmutableArray<_>) (array2: ImmutableArray<_>) =
//
//
//        let len1 = array1.Length

//        if len1 <> array2.Length then
//            invalidArgDifferentArrayLength "array1" len1 "array2" array2.Length

//        let res = Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked len1
//        let inputChunks = createPartitionsUpTo array1.Length immarray1

//        Parallel.For(
//            0,
//            inputChunks.Length,
//            fun chunkIdx ->
//                let chunk = inputChunks[chunkIdx]

//                for elemIdx = chunk.Offset to (chunk.Offset + chunk.Count - 1) do
//                    res[elemIdx] <- (array1[elemIdx], immarray2[elemIdx])
//        )
//        |> ignore

//        res

//    let inline groupByImplParallel
//        (comparer: IEqualityComparer<'SafeKey>)
//        ([<InlineIfLambda>] keyf: 'T -> 'SafeKey)
//        ([<InlineIfLambda>] getKey: 'SafeKey -> 'Key)
//        (array: ImmutableArray<'T>)
//        =
//        let counts =
//            new ConcurrentDictionary<_, _>(
//                concurrencyLevel = maxPartitions,
//                capacity = Operators.min (array.Length) 1_000,
//                comparer = comparer
//            )

//        let valueFactory = new Func<_, _>(fun _ -> ref 0)

//        let projectedValues =
//            Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked array.Length

//        let inputChunks = createPartitionsUpTo array.Length immarray

//        Parallel.For(
//            0,
//            inputChunks.Length,
//            fun chunkIdx ->
//                let chunk = inputChunks[chunkIdx]

//                for elemIdx = chunk.Offset to (chunk.Offset + chunk.Count - 1) do
//                    let projected = keyf immarray[elemIdx]
//                    projectedValues[elemIdx] <- projected
//                    let counter = counts.GetOrAdd(projected, valueFactory = valueFactory)
//                    Interlocked.Increment(counter) |> ignore
//        )
//        |> ignore

//        let finalResults =
//            Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked counts.Count

//        let mutable finalIdx = 0

//        let finalResultsLookup =
//            new Dictionary<'SafeKey, int ref * ImmutableArray<'T>>(capacity = counts.Count, comparer = comparer)

//        for kvp in counts do
//            let immarrayForThisGroup =
//                Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked kvp.Value.Value

//            finalResults.[finalIdx] <- getKey kvp.Key, immarrayForThisGroup
//            finalResultsLookup[kvp.Key] <- kvp.Value, immarrayForThisGroup
//            finalIdx <- finalIdx + 1

//        Parallel.For(
//            0,
//            inputChunks.Length,
//            fun chunkIdx ->
//                let chunk = inputChunks[chunkIdx]

//                for elemIdx = chunk.Offset to (chunk.Offset + chunk.Count - 1) do
//                    let key = projectedValues[elemIdx]
//                    let (counter, immarrayForThisGroup) = finalResultsLookup[key]
//                    let idxToWrite = Interlocked.Decrement(counter)
//                    immarrayForThisGroup[idxToWrite] <- immarray[elemIdx]
//        )
//        |> ignore

//        finalResults

//    let groupByValueTypeParallel (keyf: 'T -> 'Key) (array: ImmutableArray<'T>) =
//        // Is it a bad idea to put floating points as keys for grouping? Yes
//        // But would the implementation fail with KeyNotFound "nan" if we just leave it? Also yes
//        // Here we  enforce nan=nan equality to prevent throwing
//        if typeof<'Key> = typeof<float> || typeof<'Key> = typeof<float32> then
//            let genericCmp =
//                HashIdentity.FromFunctions<'Key>
//                    (LanguagePrimitives.GenericHash)
//                    (LanguagePrimitives.GenericEqualityER)

//            groupByImplParallel genericCmp keyf id immarray
//        else
//            groupByImplParallel HashIdentity.Structural<'Key> keyf id immarray

//    // Just like in regular immarray.groupBy: Wrap a StructBox around all keys in order to avoid nulls
//    // (dotnet doesn't allow null keys in dictionaries)
//    let groupByRefTypeParallel (keyf: 'T -> 'Key) (array: ImmutableArray<'T>) =
//        groupByImplParallel
//            RuntimeHelpers.StructBox<'Key>.Comparer
//            (keyf >> RuntimeHelpers.StructBox)
//            (fun sb -> sb.Value)
//            immarray

//    [<CompiledName("GroupBy")>]
//    let groupBy (projection: 'T -> 'Key) (array: ImmutableArray<'T>) =
//

//        if typeof<'Key>.IsValueType then
//            groupByValueTypeParallel projection immarray
//        else
//            groupByRefTypeParallel projection immarray

//    [<CompiledName("Iterate")>]
//    let iter action (array: ImmutableArray<'T>) =
//
//        Parallel.For(0, array.Length, (fun i -> action array.[i])) |> ignore

//    [<CompiledName("IterateIndexed")>]
//    let iteri action (array: ImmutableArray<'T>) =
//
//        let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt(action)
//        Parallel.For(0, array.Length, (fun i -> f.Invoke(i, array.[i]))) |> ignore

//    [<CompiledName("Initialize")>]
//    let init count initializer =
//        let result = Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked count
//        Parallel.For(0, count, (fun i -> result.[i] <- initializer i)) |> ignore
//        result

//    let countAndCollectTrueItems predicate (array: ImmutableArray<'T>) =
//
//        let inputLength = array.Length

//        let isTrue =
//            Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked inputLength

//        let mutable trueLength = 0

//        Parallel.For(
//            0,
//            inputLength,
//            (fun () -> 0),
//            (fun i _ trueCount ->
//                if predicate array.[i] then
//                    isTrue.[i] <- true
//                    trueCount + 1
//                else
//                    trueCount),
//            Action<int>(fun x -> System.Threading.Interlocked.Add(&trueLength, x) |> ignore)
//        )
//        |> ignore

//        trueLength, isTrue

//    [<CompiledName("Filter")>]
//    let filter predicate (array: ImmutableArray<'T>) =
//        let trueLength, isTrue = countAndCollectTrueItems predicate array
//        let res = Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked trueLength
//        let mutable resIdx = 0

//        for i = 0 to isTrue.Length - 1 do
//            if isTrue.[i] then
//                res.[resIdx] <- array.[i]
//                resIdx <- resIdx + 1

//        res

//    [<CompiledName("Partition")>]
//    let partition predicate (array: ImmutableArray<'T>) =
//        let trueLength, isTrue = countAndCollectTrueItems predicate array
//        let res1 = Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked trueLength

//        let res2 =
//            Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked (array.Length - trueLength)

//        let mutable iTrue = 0
//        let mutable iFalse = 0

//        for i = 0 to isTrue.Length - 1 do
//            if isTrue.[i] then
//                res1.[iTrue] <- array.[i]
//                iTrue <- iTrue + 1
//            else
//                res2.[iFalse] <- array.[i]
//                iFalse <- iFalse + 1

//        res1, res2

//    let private createPartitions (array: ImmutableArray<'T>) =
//        createPartitionsUpTo array.Length immarray

//    let inline pickPivot
//        ([<InlineIfLambda>] cmpAtIndex: int -> int -> int)
//        ([<InlineIfLambda>] swapAtIndex: int -> int -> unit)
//        (orig: immarraySegment<'T>)
//        =
//        let inline swapIfGreater (i: int) (j: int) =
//            if cmpAtIndex i j > 0 then
//                swapAtIndex i j

//        // Set pivot to be a median of {first,mid,last}

//        let firstIdx = orig.Offset
//        let lastIDx = orig.Offset + orig.Count - 1
//        let midIdx = orig.Offset + orig.Count / 2

//        swapIfGreater firstIdx midIdx
//        swapIfGreater firstIdx lastIDx
//        swapIfGreater midIdx lastIDx
//        midIdx

//    let inline partitionIntoTwo
//        ([<InlineIfLambda>] cmpWithPivot: int -> int)
//        ([<InlineIfLambda>] swapAtIndex: int -> int -> unit)
//        (orig: immarraySegment<'T>)
//        =
//        let mutable leftIdx = orig.Offset + 1 // Leftmost is already < pivot
//        let mutable rightIdx = orig.Offset + orig.Count - 2 // Rightmost is already > pivot

//        while leftIdx < rightIdx do
//            while cmpWithPivot leftIdx < 0 do
//                leftIdx <- leftIdx + 1

//            while cmpWithPivot rightIdx > 0 do
//                rightIdx <- rightIdx - 1

//            if leftIdx < rightIdx then
//                swapAtIndex leftIdx rightIdx
//                leftIdx <- leftIdx + 1
//                rightIdx <- rightIdx - 1

//        let lastIdx = orig.Offset + orig.Count - 1
//        // There might be more elements being (=)pivot. Exclude them from further work
//        while cmpWithPivot leftIdx >= 0 && leftIdx > orig.Offset do
//            leftIdx <- leftIdx - 1

//        while cmpWithPivot rightIdx <= 0 && rightIdx < lastIdx do
//            rightIdx <- rightIdx + 1

//        new immarraySegment<_>(orig.Array, offset = orig.Offset, count = leftIdx - orig.Offset + 1),
//        new immarraySegment<_>(orig.Array, offset = rightIdx, count = lastIdx - rightIdx + 1)

//    let partitionIntoTwoUsingComparer
//        (cmp: 'T -> 'T -> int)
//        (orig: immarraySegment<'T>)
//        : immarraySegment<'T> * immarraySegment<'T> =
//        let immarray = orig.Array

//        let inline swap i j =
//            let tmp = immarray[i]
//            immarray[i] <- immarray[j]
//            immarray[j] <- tmp

//        let pivotIdx = pickPivot (fun i j -> cmp immarray[i] immarray[j]) swap orig

//        let pivotItem = immarray[pivotIdx]
//        partitionIntoTwo (fun idx -> cmp immarray[idx] pivotItem) swap orig

//    let partitionIntoTwoUsingKeys (keys: ImmutableArray<'a>) (orig: immarraySegment<'T>) : immarraySegment<'T> * immarraySegment<'T> =
//        let immarray = orig.Array

//        let inline swap i j =
//            let tmpKey = keys[i]
//            keys[i] <- keys[j]
//            keys[j] <- tmpKey

//            let tmp = array.[i]
//            array.[i] <- array.[j]
//            array.[j] <- tmp

//        let pivotIdx = pickPivot (fun i j -> compare keys[i] keys[j]) swap orig

//        let pivotKey = keys[pivotIdx]
//        partitionIntoTwo (fun idx -> compare keys[idx] pivotKey) swap orig

//    let inline sortInPlaceHelper
//        (array: ImmutableArray<'T>)
//        ([<InlineIfLambda>] partitioningFunc: immarraySegment<'T> -> immarraySegment<'T> * immarraySegment<'T>)
//        ([<InlineIfLambda>] sortingFunc: immarraySegment<'T> -> unit)
//        =
//        let rec sortChunk (segment: immarraySegment<_>) freeWorkers =
//            match freeWorkers with
//            // Really small immarrays are not worth creating a Task for, sort them immediately as well
//            | 0
//            | 1 -> sortingFunc segment
//            | _ when segment.Count <= minChunkSize -> sortingFunc segment
//            | _ ->
//                let left, right = partitioningFunc segment
//                // If either of the two is too small, sort small segments straight away.
//                // If the other happens to be big, leave it with all workes in it's recursive step
//                if left.Count <= minChunkSize || right.Count <= minChunkSize then
//                    sortChunk left freeWorkers
//                    sortChunk right freeWorkers
//                else
//                    // Pivot-based partitions might be inbalanced. Split  free workers for left/right proportional to their size
//                    let itemsPerWorker = Operators.max ((left.Count + right.Count) / freeWorkers) 1

//                    let workersForLeftTask =
//                        (left.Count / itemsPerWorker)
//                        |> Operators.max 1
//                        |> Operators.min (freeWorkers - 1)

//                    let leftTask = Task.Run(fun () -> sortChunk left workersForLeftTask)
//                    sortChunk right (freeWorkers - workersForLeftTask)
//                    leftTask.Wait()

//        let bigSegment = new immarraySegment<_>(array, 0, array.Length)
//        sortChunk bigSegment maxPartitions

//    let sortInPlaceWithHelper
//        (partitioningComparer: 'T -> 'T -> int)
//        (sortingComparer: IComparer<'T>)
//        (inputArray: ImmutableArray<'T>)
//        =
//        let partitioningFunc = partitionIntoTwoUsingComparer partitioningComparer

//        let sortingFunc =
//            fun (s: immarraySegment<'T>) -> immarray.Sort<'T>(inputArray, s.Offset, s.Count, sortingComparer)

//        sortInPlaceHelper inputArray partitioningFunc sortingFunc

//    let sortKeysAndValuesInPlace (inputKeys: 'TKey immarray) (values: 'TValue immarray) =
//        let partitioningFunc = partitionIntoTwoUsingKeys inputKeys
//        let sortingComparer = LanguagePrimitives.FastGenericComparerCanBeNull<'TKey>

//        let sortingFunc =
//            fun (s: immarraySegment<'T>) ->
//                immarray.Sort<'TKey, 'TValue>(inputKeys, values, s.Offset, s.Count, sortingComparer)

//        sortInPlaceHelper values partitioningFunc sortingFunc

//    [<CompiledName("SortInPlaceWith")>]
//    let sortInPlaceWith comparer (array: ImmutableArray<'T>) =
//
//        let sortingComparer = ComparisonIdentity.FromFunction(comparer)
//        sortInPlaceWithHelper comparer sortingComparer immarray

//    [<CompiledName("SortInPlaceBy")>]
//    let sortInPlaceBy (projection: 'T -> 'U) (array: ImmutableArray<'T>) =
//

//        let inputKeys: ImmutableArray<'U> =
//            Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked array.Length

//        let partitions = createPartitions immarray

//        Parallel.For(
//            0,
//            partitions.Length,
//            fun i ->
//                let segment = partitions.[i]

//                for idx = segment.Offset to (segment.Offset + segment.Count - 1) do
//                    inputKeys[idx] <- projection immarray[idx]
//        )
//        |> ignore

//        sortKeysAndValuesInPlace inputKeys immarray

//    [<CompiledName("SortInPlace")>]
//    let sortInPlace (array: ImmutableArray<'T>) =
//

//        let sortingComparer: IComparer<'T> =
//            LanguagePrimitives.FastGenericComparerCanBeNull<'T>

//        let partioningFunc = compare
//        sortInPlaceWithHelper partioningFunc sortingComparer immarray

//    [<CompiledName("SortWith")>]
//    let sortWith (comparer: 'T -> 'T -> int) (array: ImmutableArray<'T>) =
//        let result = copy immarray
//        sortInPlaceWith comparer result
//        result

//    [<CompiledName("SortBy")>]
//    let sortBy projection (array: ImmutableArray<'T>) =
//

//        let inputKeys =
//            Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked array.Length

//        let clone =
//            Microsoft.FSharp.Primitives.Basics.Array.zeroCreateUnchecked array.Length

//        let partitions = createPartitions clone

//        Parallel.For(
//            0,
//            partitions.Length,
//            fun i ->
//                let segment = partitions.[i]

//                for idx = segment.Offset to (segment.Offset + segment.Count - 1) do
//                    clone[idx] <- immarray[idx]
//                    inputKeys.[idx] <- projection immarray[idx]
//        )
//        |> ignore

//        sortKeysAndValuesInPlace inputKeys clone
//        clone

//    [<CompiledName("Sort")>]
//    let sort immarray =
//        let result = copy immarray
//        sortInPlace result
//        result

//    let reverseInPlace (array: ImmutableArray<'T>) =
//        let segments = createPartitionsUpTo (array.Length / 2) immarray
//        let lastIdx = array.Length - 1

//        Parallel.For(
//            0,
//            segments.Length,
//            fun idx ->
//                let s = segments[idx]

//                for i = s.Offset to (s.Offset + s.Count - 1) do
//                    let tmp = immarray[i]
//                    immarray[i] <- immarray[lastIdx - i]
//                    immarray[lastIdx - i] <- tmp
//        )
//        |> ignore

//        immarray

//    [<CompiledName("SortByDescending")>]
//    let sortByDescending projection immarray =
//        immarray |> sortBy projection |> reverseInPlace

//    [<CompiledName("SortDescending")>]
//    let sortDescending immarray =
//        immarray |> sort |> reverseInPlace
