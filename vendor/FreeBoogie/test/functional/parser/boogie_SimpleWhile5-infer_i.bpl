// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: -nologo /prover:blank /print:boogie_tmp.@TIME@.bpl /proverLog:boogie_tmp.@TIME@.simplify SimpleWhile5.dll /infer:i

type real;

type elements;

type struct;

type exposeVersionType;

var $Heap: [ref,<x>name]x where IsHeap($Heap);

function IsHeap(h: [ref,<x>name]x) returns (bool);

const $allocated: <bool>name;

const $elements: <elements>name;

const $inv: <name>name;

const $localinv: <name>name;

const $exposeVersion: <exposeVersionType>name;

axiom DeclType($exposeVersion) == System.Object;

const $sharingMode: name;

const $SharingMode_Unshared: name;

const $SharingMode_LockProtected: name;

const $ownerRef: <ref>name;

const $ownerFrame: <name>name;

const $PeerGroupPlaceholder: name;

function ClassRepr(class: name) returns (ref);

axiom (forall c0: name, c1: name :: { ClassRepr(c0), ClassRepr(c1) } c0 != c1 ==> ClassRepr(c0) != ClassRepr(c1));

axiom (forall T: name :: !($typeof(ClassRepr(T)) <: System.Object));

axiom (forall T: name :: ClassRepr(T) != null);

axiom (forall T: name, h: [ref,<x>name]x :: { h[ClassRepr(T), $ownerFrame] } IsHeap(h) ==> h[ClassRepr(T), $ownerFrame] == $PeerGroupPlaceholder);

function IsDirectlyModifiableField(f: name) returns (bool);

axiom !IsDirectlyModifiableField($allocated);

axiom IsDirectlyModifiableField($elements);

axiom !IsDirectlyModifiableField($inv);

axiom !IsDirectlyModifiableField($localinv);

axiom !IsDirectlyModifiableField($ownerRef);

axiom !IsDirectlyModifiableField($ownerFrame);

axiom !IsDirectlyModifiableField($exposeVersion);

function IsStaticField(f: name) returns (bool);

axiom !IsStaticField($allocated);

axiom !IsStaticField($elements);

axiom !IsStaticField($inv);

axiom !IsStaticField($localinv);

axiom !IsStaticField($exposeVersion);

function ValueArrayGet(elements, int) returns (any);

function ValueArraySet(elements, int, any) returns (elements);

function RefArrayGet(elements, int) returns (ref);

function RefArraySet(elements, int, ref) returns (elements);

axiom (forall A: elements, i: int, x: any :: ValueArrayGet(ValueArraySet(A, i, x), i) == x);

axiom (forall A: elements, i: int, j: int, x: any :: i != j ==> ValueArrayGet(ValueArraySet(A, i, x), j) == ValueArrayGet(A, j));

axiom (forall A: elements, i: int, x: ref :: RefArrayGet(RefArraySet(A, i, x), i) == x);

axiom (forall A: elements, i: int, j: int, x: ref :: i != j ==> RefArrayGet(RefArraySet(A, i, x), j) == RefArrayGet(A, j));

function ArrayIndex(arr: ref, dim: int, indexAtDim: int, remainingIndexContribution: int) returns (int);

axiom (forall a: ref, d: int, x: int, y: int, x': int, y': int :: { ArrayIndex(a, d, x, y), ArrayIndex(a, d, x', y') } ArrayIndex(a, d, x, y) == ArrayIndex(a, d, x', y') ==> x == x' && y == y');

axiom (forall a: ref, T: name, i: int, r: int, heap: [ref,<x>name]x :: { $typeof(a) <: RefArray(T, r), RefArrayGet(heap[a, $elements], i) } IsHeap(heap) && $typeof(a) <: RefArray(T, r) ==> $Is(RefArrayGet(heap[a, $elements], i), T));

axiom (forall a: ref, T: name, i: int, r: int, heap: [ref,<x>name]x :: { $typeof(a) <: NonNullRefArray(T, r), RefArrayGet(heap[a, $elements], i) } IsHeap(heap) && $typeof(a) <: NonNullRefArray(T, r) ==> $IsNotNull(RefArrayGet(heap[a, $elements], i), T));

function $Rank(ref) returns (int);

axiom (forall a: ref :: 1 <= $Rank(a));

axiom (forall a: ref, T: name, r: int :: { $typeof(a) <: RefArray(T, r) } a != null && $typeof(a) <: RefArray(T, r) ==> $Rank(a) == r);

axiom (forall a: ref, T: name, r: int :: { $typeof(a) <: NonNullRefArray(T, r) } a != null && $typeof(a) <: NonNullRefArray(T, r) ==> $Rank(a) == r);

axiom (forall a: ref, T: name, r: int :: { $typeof(a) <: ValueArray(T, r) } a != null && $typeof(a) <: ValueArray(T, r) ==> $Rank(a) == r);

function $Length(ref) returns (int);

axiom (forall a: ref :: { $Length(a) } 0 <= $Length(a));

function $DimLength(ref, int) returns (int);

axiom (forall a: ref, i: int :: 0 <= $DimLength(a, i));

axiom (forall a: ref :: { $DimLength(a, 0) } $Rank(a) == 1 ==> $DimLength(a, 0) == $Length(a));

function $LBound(ref, int) returns (int);

function $UBound(ref, int) returns (int);

axiom (forall a: ref, i: int :: { $LBound(a, i) } $LBound(a, i) == 0);

axiom (forall a: ref, i: int :: { $UBound(a, i) } $UBound(a, i) == $DimLength(a, i) - 1);

const $ArrayCategoryValue: name;

const $ArrayCategoryRef: name;

const $ArrayCategoryNonNullRef: name;

function $ArrayCategory(arrayType: name) returns (arrayCategory: name);

axiom (forall T: name, ET: name, r: int :: { T <: ValueArray(ET, r) } T <: ValueArray(ET, r) ==> $ArrayCategory(T) == $ArrayCategoryValue);

axiom (forall T: name, ET: name, r: int :: { T <: RefArray(ET, r) } T <: RefArray(ET, r) ==> $ArrayCategory(T) == $ArrayCategoryRef);

axiom (forall T: name, ET: name, r: int :: { T <: NonNullRefArray(ET, r) } T <: NonNullRefArray(ET, r) ==> $ArrayCategory(T) == $ArrayCategoryNonNullRef);

const System.Array: name;

axiom System.Array <: System.Object;

function $ElementType(name) returns (name);

function ValueArray(elementType: name, rank: int) returns (name);

axiom (forall T: name, r: int :: { ValueArray(T, r) } ValueArray(T, r) <: System.Array);

function RefArray(elementType: name, rank: int) returns (name);

axiom (forall T: name, r: int :: { RefArray(T, r) } RefArray(T, r) <: System.Array);

function NonNullRefArray(elementType: name, rank: int) returns (name);

axiom (forall T: name, r: int :: { NonNullRefArray(T, r) } NonNullRefArray(T, r) <: System.Array);

axiom (forall T: name, U: name, r: int :: U <: T ==> RefArray(U, r) <: RefArray(T, r));

axiom (forall T: name, U: name, r: int :: U <: T ==> NonNullRefArray(U, r) <: NonNullRefArray(T, r));

axiom (forall A: name, r: int :: $ElementType(ValueArray(A, r)) == A);

axiom (forall A: name, r: int :: $ElementType(RefArray(A, r)) == A);

axiom (forall A: name, r: int :: $ElementType(NonNullRefArray(A, r)) == A);

axiom (forall A: name, r: int, T: name :: { T <: RefArray(A, r) } T <: RefArray(A, r) ==> T == RefArray($ElementType(T), r) && $ElementType(T) <: A);

axiom (forall A: name, r: int, T: name :: { T <: NonNullRefArray(A, r) } T <: NonNullRefArray(A, r) ==> T == NonNullRefArray($ElementType(T), r) && $ElementType(T) <: A);

axiom (forall A: name, r: int, T: name :: { T <: ValueArray(A, r) } T <: ValueArray(A, r) ==> T == ValueArray(A, r));

axiom (forall A: name, r: int, T: name :: RefArray(A, r) <: T ==> System.Array <: T || (T == RefArray($ElementType(T), r) && A <: $ElementType(T)));

axiom (forall A: name, r: int, T: name :: NonNullRefArray(A, r) <: T ==> System.Array <: T || (T == NonNullRefArray($ElementType(T), r) && A <: $ElementType(T)));

axiom (forall A: name, r: int, T: name :: ValueArray(A, r) <: T ==> System.Array <: T || T == ValueArray(A, r));

function $ArrayPtr(elementType: name) returns (name);

function $StructGet(struct, name) returns (any);

function $StructSet(struct, name, any) returns (struct);

axiom (forall s: struct, f: name, x: any :: $StructGet($StructSet(s, f, x), f) == x);

axiom (forall s: struct, f: name, f': name, x: any :: f != f' ==> $StructGet($StructSet(s, f, x), f') == $StructGet(s, f'));

function ZeroInit(s: struct, typ: name) returns (bool);

function $typeof(ref) returns (name);

function $BaseClass(sub: name) returns (base: name);

function AsDirectSubClass(sub: name, base: name) returns (sub': name);

function OneClassDown(sub: name, base: name) returns (directSub: name);

axiom (forall A: name, B: name, C: name :: { C <: AsDirectSubClass(B, A) } C <: AsDirectSubClass(B, A) ==> OneClassDown(C, A) == B);

function $IsValueType(name) returns (bool);

axiom (forall T: name :: $IsValueType(T) ==> (forall U: name :: T <: U ==> T == U) && (forall U: name :: U <: T ==> T == U));

const System.Object: name;

function $IsTokenForType(struct, name) returns (bool);

function TypeObject(name) returns (ref);

const System.Type: name;

axiom System.Type <: System.Object;

axiom (forall T: name :: { TypeObject(T) } $IsNotNull(TypeObject(T), System.Type));

function TypeName(ref) returns (name);

axiom (forall T: name :: { TypeObject(T) } TypeName(TypeObject(T)) == T);

function $Is(ref, name) returns (bool);

axiom (forall o: ref, T: name :: { $Is(o, T) } $Is(o, T) <==> o == null || $typeof(o) <: T);

function $IsNotNull(ref, name) returns (bool);

axiom (forall o: ref, T: name :: { $IsNotNull(o, T) } $IsNotNull(o, T) <==> o != null && $Is(o, T));

function $As(ref, name) returns (ref);

axiom (forall o: ref, T: name :: $Is(o, T) ==> $As(o, T) == o);

axiom (forall o: ref, T: name :: !$Is(o, T) ==> $As(o, T) == null);

axiom (forall h: [ref,<x>name]x, o: ref :: { $typeof(o) <: System.Array, h[o, $inv] } IsHeap(h) && o != null && $typeof(o) <: System.Array ==> h[o, $inv] == $typeof(o) && h[o, $localinv] == $typeof(o));

function IsAllocated(h: [ref,<x>name]x, o: any) returns (bool);

axiom (forall h: [ref,<x>name]x, o: ref, f: name :: { IsAllocated(h, h[o, f]) } IsHeap(h) && h[o, $allocated] ==> IsAllocated(h, h[o, f]));

axiom (forall h: [ref,<x>name]x, o: ref, f: <ref>name :: { h[h[o, f], $allocated] } IsHeap(h) && h[o, $allocated] ==> h[h[o, f], $allocated]);

axiom (forall h: [ref,<x>name]x, s: struct, f: name :: { IsAllocated(h, $StructGet(s, f)) } IsAllocated(h, s) ==> IsAllocated(h, $StructGet(s, f)));

axiom (forall h: [ref,<x>name]x, e: elements, i: int :: { IsAllocated(h, RefArrayGet(e, i)) } IsAllocated(h, e) ==> IsAllocated(h, RefArrayGet(e, i)));

axiom (forall h: [ref,<x>name]x, e: elements, i: int :: { IsAllocated(h, ValueArrayGet(e, i)) } IsAllocated(h, e) ==> IsAllocated(h, ValueArrayGet(e, i)));

axiom (forall h: [ref,<x>name]x, o: ref :: { h[o, $allocated] } IsAllocated(h, o) ==> h[o, $allocated]);

axiom (forall h: [ref,<x>name]x, c: name :: { h[ClassRepr(c), $allocated] } IsHeap(h) ==> h[ClassRepr(c), $allocated]);

const $BeingConstructed: ref;

const $NonNullFieldsAreInitialized: <bool>name;

function DeclType(field: name) returns (class: name);

function AsNonNullRefField(field: <ref>name, T: name) returns (f: <ref>name);

function AsRefField(field: <ref>name, T: name) returns (f: <ref>name);

function AsRangeField(field: <int>name, T: name) returns (f: <int>name);

axiom (forall f: <ref>name, T: name :: { AsNonNullRefField(f, T) } AsNonNullRefField(f, T) == f ==> AsRefField(f, T) == f);

axiom (forall h: [ref,<x>name]x, o: ref, f: <ref>name, T: name :: { h[o, AsRefField(f, T)] } IsHeap(h) ==> $Is(h[o, AsRefField(f, T)], T));

axiom (forall h: [ref,<x>name]x, o: ref, f: <ref>name, T: name :: { h[o, AsNonNullRefField(f, T)] } IsHeap(h) && o != null && (o != $BeingConstructed || h[$BeingConstructed, $NonNullFieldsAreInitialized] == true) ==> h[o, AsNonNullRefField(f, T)] != null);

axiom (forall h: [ref,<x>name]x, o: ref, f: <int>name, T: name :: { h[o, AsRangeField(f, T)] } IsHeap(h) ==> InRange(h[o, AsRangeField(f, T)], T));

function $IsMemberlessType(name) returns (bool);

axiom (forall o: ref :: { $IsMemberlessType($typeof(o)) } !$IsMemberlessType($typeof(o)));

function $IsImmutable(T: name) returns (bool);

axiom !$IsImmutable(System.Object);

function $AsImmutable(T: name) returns (theType: name);

function $AsMutable(T: name) returns (theType: name);

axiom (forall T: name, U: name :: { U <: $AsImmutable(T) } U <: $AsImmutable(T) ==> $IsImmutable(U) && $AsImmutable(U) == U);

axiom (forall T: name, U: name :: { U <: $AsMutable(T) } U <: $AsMutable(T) ==> !$IsImmutable(U) && $AsMutable(U) == U);

function AsOwner(string: ref, owner: ref) returns (theString: ref);

axiom (forall o: ref, T: name :: { $typeof(o) <: $AsImmutable(T) } o != null && o != $BeingConstructed && $typeof(o) <: $AsImmutable(T) ==> (forall h: [ref,<x>name]x :: { IsHeap(h) } IsHeap(h) ==> h[o, $inv] == $typeof(o) && h[o, $localinv] == $typeof(o) && h[o, $ownerFrame] == $PeerGroupPlaceholder && AsOwner(o, h[o, $ownerRef]) == o && (forall t: ref :: { AsOwner(o, h[t, $ownerRef]) } AsOwner(o, h[t, $ownerRef]) == o ==> t == o || h[t, $ownerFrame] != $PeerGroupPlaceholder)));

const System.String: name;

function $StringLength(ref) returns (int);

axiom (forall s: ref :: { $StringLength(s) } 0 <= $StringLength(s));

function AsRepField(f: <ref>name, declaringType: name) returns (theField: <ref>name);

axiom (forall h: [ref,<x>name]x, o: ref, f: <ref>name, T: name :: { h[o, AsRepField(f, T)] } IsHeap(h) && h[o, AsRepField(f, T)] != null ==> h[h[o, AsRepField(f, T)], $ownerRef] == o && h[h[o, AsRepField(f, T)], $ownerFrame] == T);

function AsPeerField(f: <ref>name) returns (theField: <ref>name);

axiom (forall h: [ref,<x>name]x, o: ref, f: <ref>name :: { h[o, AsPeerField(f)] } IsHeap(h) && h[o, AsPeerField(f)] != null ==> h[h[o, AsPeerField(f)], $ownerRef] == h[o, $ownerRef] && h[h[o, AsPeerField(f)], $ownerFrame] == h[o, $ownerFrame]);

axiom (forall h: [ref,<x>name]x, o: ref :: { h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame] } IsHeap(h) && h[o, $ownerFrame] != $PeerGroupPlaceholder && h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame] && h[h[o, $ownerRef], $localinv] != $BaseClass(h[o, $ownerFrame]) ==> h[o, $inv] == $typeof(o) && h[o, $localinv] == $typeof(o));

procedure $SetOwner(o: ref, ow: ref, fr: name);
  modifies $Heap;
  ensures (forall p: ref, F: name :: { $Heap[p, F] } (F != $ownerRef && F != $ownerFrame) || old($Heap[p, $ownerRef] != $Heap[o, $ownerRef]) || old($Heap[p, $ownerFrame] != $Heap[o, $ownerFrame]) ==> old($Heap[p, F]) == $Heap[p, F]);
  ensures (forall p: ref :: { $Heap[p, $ownerRef] } { $Heap[p, $ownerFrame] } old($Heap[p, $ownerRef] == $Heap[o, $ownerRef]) && old($Heap[p, $ownerFrame] == $Heap[o, $ownerFrame]) ==> $Heap[p, $ownerRef] == ow && $Heap[p, $ownerFrame] == fr);



procedure $UpdateOwnersForRep(o: ref, T: name, e: ref);
  modifies $Heap;
  ensures (forall p: ref, F: name :: { $Heap[p, F] } (F != $ownerRef && F != $ownerFrame) || old($Heap[p, $ownerRef] != $Heap[e, $ownerRef]) || old($Heap[p, $ownerFrame] != $Heap[e, $ownerFrame]) ==> old($Heap[p, F]) == $Heap[p, F]);
  ensures e == null ==> $Heap == old($Heap);
  ensures e != null ==> (forall p: ref :: { $Heap[p, $ownerRef] } { $Heap[p, $ownerFrame] } old($Heap[p, $ownerRef] == $Heap[e, $ownerRef]) && old($Heap[p, $ownerFrame] == $Heap[e, $ownerFrame]) ==> $Heap[p, $ownerRef] == o && $Heap[p, $ownerFrame] == T);



procedure $UpdateOwnersForPeer(c: ref, d: ref);
  modifies $Heap;
  ensures (forall p: ref, F: name :: { $Heap[p, F] } (F != $ownerRef && F != $ownerFrame) || old(($Heap[p, $ownerRef] != $Heap[c, $ownerRef] || $Heap[p, $ownerFrame] != $Heap[c, $ownerFrame]) && ($Heap[p, $ownerRef] != $Heap[d, $ownerRef] || $Heap[p, $ownerFrame] != $Heap[d, $ownerFrame])) ==> old($Heap[p, F]) == $Heap[p, F]);
  ensures d == null ==> $Heap == old($Heap);
  ensures d != null ==> (forall p: ref :: { $Heap[p, $ownerRef] } { $Heap[p, $ownerFrame] } (old($Heap[p, $ownerRef] == $Heap[c, $ownerRef]) && old($Heap[p, $ownerFrame] == $Heap[c, $ownerFrame])) || (old($Heap[p, $ownerRef] == $Heap[d, $ownerRef]) && old($Heap[p, $ownerFrame] == $Heap[d, $ownerFrame])) ==> (old($Heap)[d, $ownerFrame] == $PeerGroupPlaceholder && $Heap[p, $ownerRef] == old($Heap)[c, $ownerRef] && $Heap[p, $ownerFrame] == old($Heap)[c, $ownerFrame]) || (old($Heap)[d, $ownerFrame] != $PeerGroupPlaceholder && $Heap[p, $ownerRef] == old($Heap)[d, $ownerRef] && $Heap[p, $ownerFrame] == old($Heap)[d, $ownerFrame]));



const $FirstConsistentOwner: <ref>name;

function $AsPureObject(ref) returns (ref);

function ##FieldDependsOnFCO(o: ref, f: name, ev: exposeVersionType) returns (value: any);

axiom (forall o: ref, f: name, h: [ref,<x>name]x :: { h[$AsPureObject(o), f] } IsHeap(h) && o != null && h[o, $allocated] == true && h[o, $ownerFrame] != $PeerGroupPlaceholder && h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame] && h[h[o, $ownerRef], $localinv] != $BaseClass(h[o, $ownerFrame]) ==> h[o, f] == ##FieldDependsOnFCO(o, f, h[h[o, $FirstConsistentOwner], $exposeVersion]));

axiom (forall o: ref, h: [ref,<x>name]x :: { h[o, $FirstConsistentOwner] } IsHeap(h) && o != null && h[o, $allocated] == true && h[o, $ownerFrame] != $PeerGroupPlaceholder && h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame] && h[h[o, $ownerRef], $localinv] != $BaseClass(h[o, $ownerFrame]) ==> h[o, $FirstConsistentOwner] != null && h[h[o, $FirstConsistentOwner], $allocated] == true && (h[h[o, $FirstConsistentOwner], $ownerFrame] == $PeerGroupPlaceholder || !(h[h[h[o, $FirstConsistentOwner], $ownerRef], $inv] <: h[h[o, $FirstConsistentOwner], $ownerFrame]) || h[h[h[o, $FirstConsistentOwner], $ownerRef], $localinv] == $BaseClass(h[h[o, $FirstConsistentOwner], $ownerFrame])));

function Box(any, ref) returns (ref);

function Unbox(ref) returns (any);

axiom (forall x: any, p: ref :: { Unbox(Box(x, p)) } Unbox(Box(x, p)) == x);

function UnboxedType(ref) returns (name);

axiom (forall p: ref :: { $IsValueType(UnboxedType(p)) } $IsValueType(UnboxedType(p)) ==> (forall heap: [ref,<x>name]x, x: any :: { heap[Box(x, p), $inv] } IsHeap(heap) ==> heap[Box(x, p), $inv] == $typeof(Box(x, p)) && heap[Box(x, p), $localinv] == $typeof(Box(x, p))));

axiom (forall x: any, p: ref :: { UnboxedType(Box(x, p)) <: System.Object } UnboxedType(Box(x, p)) <: System.Object && Box(x, p) == p ==> x == p);

function BoxTester(p: ref, typ: name) returns (ref);

axiom (forall p: ref, typ: name :: { BoxTester(p, typ) } UnboxedType(p) == typ <==> BoxTester(p, typ) != null);

const System.SByte: name;

axiom $IsValueType(System.SByte);

const System.Byte: name;

axiom $IsValueType(System.Byte);

const System.Int16: name;

axiom $IsValueType(System.Int16);

const System.UInt16: name;

axiom $IsValueType(System.UInt16);

const System.Int32: name;

axiom $IsValueType(System.Int32);

const System.UInt32: name;

axiom $IsValueType(System.UInt32);

const System.Int64: name;

axiom $IsValueType(System.Int64);

const System.UInt64: name;

axiom $IsValueType(System.UInt64);

const System.Char: name;

axiom $IsValueType(System.Char);

const int#m2147483648: int;

const int#2147483647: int;

const int#4294967295: int;

const int#m9223372036854775808: int;

const int#9223372036854775807: int;

const int#18446744073709551615: int;

axiom int#m9223372036854775808 < int#m2147483648;

axiom int#m2147483648 < 0 - 100000;

axiom 100000 < int#2147483647;

axiom int#2147483647 < int#4294967295;

axiom int#4294967295 < int#9223372036854775807;

axiom int#9223372036854775807 < int#18446744073709551615;

function InRange(i: int, T: name) returns (bool);

axiom (forall i: int :: InRange(i, System.SByte) <==> 0 - 128 <= i && i < 128);

axiom (forall i: int :: InRange(i, System.Byte) <==> 0 <= i && i < 256);

axiom (forall i: int :: InRange(i, System.Int16) <==> 0 - 32768 <= i && i < 32768);

axiom (forall i: int :: InRange(i, System.UInt16) <==> 0 <= i && i < 65536);

axiom (forall i: int :: InRange(i, System.Int32) <==> int#m2147483648 <= i && i <= int#2147483647);

axiom (forall i: int :: InRange(i, System.UInt32) <==> 0 <= i && i <= int#4294967295);

axiom (forall i: int :: InRange(i, System.Int64) <==> int#m9223372036854775808 <= i && i <= int#9223372036854775807);

axiom (forall i: int :: InRange(i, System.UInt64) <==> 0 <= i && i <= int#18446744073709551615);

axiom (forall i: int :: InRange(i, System.Char) <==> 0 <= i && i < 65536);

function $IntToInt(val: int, fromType: name, toType: name) returns (int);

function $IntToReal(int, fromType: name, toType: name) returns (real);

function $RealToInt(real, fromType: name, toType: name) returns (int);

function $RealToReal(val: real, fromType: name, toType: name) returns (real);

function $SizeIs(name, int) returns (bool);

function $IfThenElse(bool, any, any) returns (any);

axiom (forall b: bool, x: any, y: any :: { $IfThenElse(b, x, y) } b ==> $IfThenElse(b, x, y) == x);

axiom (forall b: bool, x: any, y: any :: { $IfThenElse(b, x, y) } !b ==> $IfThenElse(b, x, y) == y);

function #neg(int) returns (int);

function #and(int, int) returns (int);

function #or(int, int) returns (int);

function #xor(int, int) returns (int);

function #shl(int, int) returns (int);

function #shr(int, int) returns (int);

function #rneg(real) returns (real);

function #radd(real, real) returns (real);

function #rsub(real, real) returns (real);

function #rmul(real, real) returns (real);

function #rdiv(real, real) returns (real);

function #rmod(real, real) returns (real);

function #rLess(real, real) returns (bool);

function #rAtmost(real, real) returns (bool);

function #rEq(real, real) returns (bool);

function #rNeq(real, real) returns (bool);

function #rAtleast(real, real) returns (bool);

function #rGreater(real, real) returns (bool);

axiom (forall x: int, y: int :: { x % y } { x / y } x % y == x - x / y * y);

axiom (forall x: int, y: int :: { x % y } 0 <= x && 0 < y ==> 0 <= x % y && x % y < y);

axiom (forall x: int, y: int :: { x % y } 0 <= x && y < 0 ==> 0 <= x % y && x % y < 0 - y);

axiom (forall x: int, y: int :: { x % y } x <= 0 && 0 < y ==> 0 - y < x % y && x % y <= 0);

axiom (forall x: int, y: int :: { x % y } x <= 0 && y < 0 ==> y < x % y && x % y <= 0);

axiom (forall x: int, y: int :: { (x + y) % y } 0 <= x && 0 <= y ==> (x + y) % y == x % y);

axiom (forall x: int, y: int :: { (y + x) % y } 0 <= x && 0 <= y ==> (y + x) % y == x % y);

axiom (forall x: int, y: int :: { (x - y) % y } 0 <= x - y && 0 <= y ==> (x - y) % y == x % y);

axiom (forall a: int, b: int, d: int :: { a % d, b % d } 2 <= d && a % d == b % d && a < b ==> a + d <= b);

axiom (forall x: int, y: int :: { #and(x, y) } 0 <= x || 0 <= y ==> 0 <= #and(x, y));

axiom (forall x: int, y: int :: { #or(x, y) } 0 <= x && 0 <= y ==> 0 <= #or(x, y) && #or(x, y) <= x + y);

axiom (forall i: int :: { #shl(i, 0) } #shl(i, 0) == i);

axiom (forall i: int, j: int :: 0 <= j ==> #shl(i, j + 1) == #shl(i, j) * 2);

axiom (forall i: int :: { #shr(i, 0) } #shr(i, 0) == i);

axiom (forall i: int, j: int :: 0 <= j ==> #shr(i, j + 1) == #shr(i, j) / 2);

function #System.String.IsInterned$System.String$notnull(ref) returns (ref);

function #System.String.Equals$System.String(ref, ref) returns (bool);

function #System.String.Equals$System.String$System.String(ref, ref) returns (bool);

axiom (forall a: ref, b: ref :: { #System.String.Equals$System.String(a, b) } #System.String.Equals$System.String(a, b) == #System.String.Equals$System.String$System.String(a, b));

axiom (forall a: ref, b: ref :: { #System.String.Equals$System.String$System.String(a, b) } #System.String.Equals$System.String$System.String(a, b) == #System.String.Equals$System.String$System.String(b, a));

axiom (forall a: ref, b: ref :: { #System.String.Equals$System.String$System.String(a, b) } a != null && b != null && #System.String.Equals$System.String$System.String(a, b) ==> #System.String.IsInterned$System.String$notnull(a) == #System.String.IsInterned$System.String$notnull(b));

const $UnknownRef: ref;

const System.Collections.Generic.IEnumerable`1...System.Char: name;

const System.ICloneable: name;

const System.IComparable: name;

const System.IConvertible: name;

const System.Collections.IEnumerable: name;

const System.IEquatable`1...System.String: name;

const SimpleWhile5: name;

const System.IComparable`1...System.String: name;

axiom SimpleWhile5 <: SimpleWhile5;

axiom $BaseClass(SimpleWhile5) == System.Object;

axiom SimpleWhile5 <: $BaseClass(SimpleWhile5) && AsDirectSubClass(SimpleWhile5, $BaseClass(SimpleWhile5)) == SimpleWhile5;

axiom !$IsImmutable(SimpleWhile5) && $AsMutable(SimpleWhile5) == SimpleWhile5;

axiom (forall $U: name :: { $U <: SimpleWhile5 } $U <: SimpleWhile5 ==> $U == SimpleWhile5);

procedure SimpleWhile5.Fact$System.Int32(this: ref, i$in: int where InRange(i$in, System.Int32)) returns ($result: int where InRange($result, System.Int32));
  free requires true;
  // user-declared preconditions
  requires i$in >= 0;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  // user-declared postconditions
  ensures $result >= 0;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation SimpleWhile5.Fact$System.Int32(this: ref, i$in: int) returns ($result: int)
{
  var i: int where InRange(i, System.Int32), returnValue: int where InRange(returnValue, System.Int32), stack0i: int, stack0b: bool, stack0o: ref, local2: int where InRange(local2, System.Int32), return.value: int where InRange(return.value, System.Int32), SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32), $Heap$block1649$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, SimpleWhile5);
    assume $Heap[this, $allocated] == true;
    i := i$in;
    goto block1530;

  block1530:
    goto block1632;

  block1632:
    // ----- nop
    // ----- load constant 1  ----- SimpleWhile5.ssc(10,3)
    returnValue := 1;
    goto block1649$LoopPreheader;

  block1649:
    // ----- default loop invariant: allocation and ownership are stable  ----- SimpleWhile5.ssc(12,3)
    assume (forall $o: ref :: $Heap$block1649$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block1649$LoopPreheader[$ot, $allocated] == true && $Heap$block1649$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block1649$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block1649$LoopPreheader[$ot, $ownerFrame]) && $Heap$block1649$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- SimpleWhile5.ssc(12,3)
    assume (forall $o: ref :: ($Heap$block1649$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block1649$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block1649$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block1649$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- SimpleWhile5.ssc(12,3)
    assert (forall $o: ref :: $o != null && $Heap$block1649$LoopPreheader[$o, $allocated] == true ==> $Heap$block1649$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block1649$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- load constant 1  ----- SimpleWhile5.ssc(12,3)
    stack0i := 1;
    // ----- binary operator  ----- SimpleWhile5.ssc(12,3)
    // ----- branch  ----- SimpleWhile5.ssc(12,3)
    goto true1649to1683, false1649to1666;

  true1649to1683:
    assume i < stack0i;
    goto block1683;

  false1649to1666:
    assume i >= stack0i;
    goto block1666;

  block1683:
    // ----- serialized AssertStatement  ----- SimpleWhile5.ssc(18,3)
    assert returnValue >= 1;
    goto block1768;

  block1666:
    // ----- binary operator  ----- SimpleWhile5.ssc(14,4)
    stack0i := returnValue * i;
    // ----- copy  ----- SimpleWhile5.ssc(14,4)
    returnValue := stack0i;
    // ----- copy  ----- SimpleWhile5.ssc(15,4)
    local2 := i;
    // ----- load constant 1  ----- SimpleWhile5.ssc(15,4)
    stack0i := 1;
    // ----- binary operator  ----- SimpleWhile5.ssc(15,4)
    stack0i := local2 - stack0i;
    // ----- copy  ----- SimpleWhile5.ssc(15,4)
    i := stack0i;
    // ----- copy
    stack0i := local2;
    // ----- branch  ----- SimpleWhile5.ssc(16,4)
    goto block1649;

  block1768:
    // ----- nop
    // ----- copy  ----- SimpleWhile5.ssc(22,3)
    return.value := returnValue;
    // ----- branch
    goto block1870;

  block1870:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;

  block1649$LoopPreheader:
    $Heap$block1649$LoopPreheader := $Heap;
    goto block1649;

}



axiom System.String <: System.String;

axiom $BaseClass(System.String) == System.Object;

axiom System.String <: $BaseClass(System.String) && AsDirectSubClass(System.String, $BaseClass(System.String)) == System.String;

axiom $IsImmutable(System.String) && $AsImmutable(System.String) == System.String;

axiom System.IComparable <: System.Object;

axiom $IsMemberlessType(System.IComparable);

axiom System.String <: System.IComparable;

axiom System.ICloneable <: System.Object;

axiom $IsMemberlessType(System.ICloneable);

axiom System.String <: System.ICloneable;

axiom System.IConvertible <: System.Object;

axiom $IsMemberlessType(System.IConvertible);

axiom System.String <: System.IConvertible;

axiom System.IComparable`1...System.String <: System.Object;

axiom $IsMemberlessType(System.IComparable`1...System.String);

axiom System.String <: System.IComparable`1...System.String;

axiom System.Collections.Generic.IEnumerable`1...System.Char <: System.Object;

axiom System.Collections.IEnumerable <: System.Object;

axiom $IsMemberlessType(System.Collections.IEnumerable);

axiom System.Collections.Generic.IEnumerable`1...System.Char <: System.Collections.IEnumerable;

axiom $IsMemberlessType(System.Collections.Generic.IEnumerable`1...System.Char);

axiom System.String <: System.Collections.Generic.IEnumerable`1...System.Char;

axiom System.String <: System.Collections.IEnumerable;

axiom System.IEquatable`1...System.String <: System.Object;

axiom $IsMemberlessType(System.IEquatable`1...System.String);

axiom System.String <: System.IEquatable`1...System.String;

axiom (forall $U: name :: { $U <: System.String } $U <: System.String ==> $U == System.String);

procedure SimpleWhile5.NonNegative$System.Int32$System.Int32$System.Int32(this: ref, X$in: int where InRange(X$in, System.Int32), Y$in: int where InRange(Y$in, System.Int32), K$in: int where InRange(K$in, System.Int32)) returns ($result: int where InRange($result, System.Int32));
  free requires true;
  free requires true;
  free requires true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  // user-declared postconditions
  ensures 0 <= $result;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation SimpleWhile5.NonNegative$System.Int32$System.Int32$System.Int32(this: ref, X$in: int, Y$in: int, K$in: int) returns ($result: int)
{
  var X: int where InRange(X, System.Int32), Y: int where InRange(Y, System.Int32), K: int where InRange(K, System.Int32), x: int where InRange(x, System.Int32), stack0b: bool, local1: int where InRange(local1, System.Int32), stack0i: int, y: int where InRange(y, System.Int32), local3: int where InRange(local3, System.Int32), n: int where InRange(n, System.Int32), return.value: int where InRange(return.value, System.Int32), local5: int where InRange(local5, System.Int32), SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32), $Heap$block2856$LoopPreheader: [ref,<x>name]x, $Heap$block2805$LoopPreheader: [ref,<x>name]x, $Heap$block2754$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, SimpleWhile5);
    assume $Heap[this, $allocated] == true;
    X := X$in;
    Y := Y$in;
    K := K$in;
    goto block2720;

  block2720:
    goto block2737;

  block2737:
    // ----- load constant 0  ----- SimpleWhile5.ssc(29,3)
    x := 0;
    goto block2754$LoopPreheader;

  block2754:
    // ----- default loop invariant: allocation and ownership are stable  ----- SimpleWhile5.ssc(30,3)
    assume (forall $o: ref :: $Heap$block2754$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block2754$LoopPreheader[$ot, $allocated] == true && $Heap$block2754$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block2754$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block2754$LoopPreheader[$ot, $ownerFrame]) && $Heap$block2754$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- SimpleWhile5.ssc(30,3)
    assume (forall $o: ref :: ($Heap$block2754$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block2754$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block2754$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block2754$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- SimpleWhile5.ssc(30,3)
    assert (forall $o: ref :: $o != null && $Heap$block2754$LoopPreheader[$o, $allocated] == true ==> $Heap$block2754$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block2754$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- binary operator  ----- SimpleWhile5.ssc(30,3)
    // ----- branch  ----- SimpleWhile5.ssc(30,3)
    goto true2754to2788, false2754to2771;

  true2754to2788:
    assume x >= X;
    goto block2788;

  false2754to2771:
    assume x < X;
    goto block2771;

  block2788:
    // ----- load constant 0  ----- SimpleWhile5.ssc(32,3)
    y := 0;
    goto block2805$LoopPreheader;

  block2771:
    // ----- copy  ----- SimpleWhile5.ssc(30,19)
    local1 := x;
    // ----- load constant 1  ----- SimpleWhile5.ssc(30,19)
    stack0i := 1;
    // ----- binary operator  ----- SimpleWhile5.ssc(30,19)
    stack0i := local1 + stack0i;
    // ----- copy  ----- SimpleWhile5.ssc(30,19)
    x := stack0i;
    // ----- copy
    stack0i := local1;
    // ----- branch  ----- SimpleWhile5.ssc(30,25)
    goto block2754;

  block2805:
    // ----- default loop invariant: allocation and ownership are stable  ----- SimpleWhile5.ssc(33,3)
    assume (forall $o: ref :: $Heap$block2805$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block2805$LoopPreheader[$ot, $allocated] == true && $Heap$block2805$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block2805$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block2805$LoopPreheader[$ot, $ownerFrame]) && $Heap$block2805$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- SimpleWhile5.ssc(33,3)
    assume (forall $o: ref :: ($Heap$block2805$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block2805$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block2805$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block2805$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- SimpleWhile5.ssc(33,3)
    assert (forall $o: ref :: $o != null && $Heap$block2805$LoopPreheader[$o, $allocated] == true ==> $Heap$block2805$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block2805$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- binary operator  ----- SimpleWhile5.ssc(33,3)
    // ----- branch  ----- SimpleWhile5.ssc(33,3)
    goto true2805to2839, false2805to2822;

  true2805to2839:
    assume y >= Y;
    goto block2839;

  false2805to2822:
    assume y < Y;
    goto block2822;

  block2839:
    // ----- load constant 12  ----- SimpleWhile5.ssc(35,3)
    n := 12;
    goto block2856$LoopPreheader;

  block2822:
    // ----- copy  ----- SimpleWhile5.ssc(33,19)
    local3 := y;
    // ----- load constant 1  ----- SimpleWhile5.ssc(33,19)
    stack0i := 1;
    // ----- binary operator  ----- SimpleWhile5.ssc(33,19)
    stack0i := local3 + stack0i;
    // ----- copy  ----- SimpleWhile5.ssc(33,19)
    y := stack0i;
    // ----- copy
    stack0i := local3;
    // ----- branch  ----- SimpleWhile5.ssc(33,25)
    goto block2805;

  block2856:
    // ----- default loop invariant: allocation and ownership are stable  ----- SimpleWhile5.ssc(36,10)
    assume (forall $o: ref :: $Heap$block2856$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block2856$LoopPreheader[$ot, $allocated] == true && $Heap$block2856$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block2856$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block2856$LoopPreheader[$ot, $ownerFrame]) && $Heap$block2856$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- SimpleWhile5.ssc(36,10)
    assume (forall $o: ref :: ($Heap$block2856$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block2856$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block2856$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block2856$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- SimpleWhile5.ssc(36,10)
    assert (forall $o: ref :: $o != null && $Heap$block2856$LoopPreheader[$o, $allocated] == true ==> $Heap$block2856$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block2856$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- load constant 100  ----- SimpleWhile5.ssc(36,10)
    stack0i := 100;
    // ----- binary operator  ----- SimpleWhile5.ssc(36,10)
    // ----- branch  ----- SimpleWhile5.ssc(36,10)
    goto true2856to2890, false2856to2873;

  true2856to2890:
    assume K >= stack0i;
    goto block2890;

  false2856to2873:
    assume K < stack0i;
    goto block2873;

  block2890:
    // ----- copy  ----- SimpleWhile5.ssc(39,3)
    return.value := n;
    // ----- branch
    goto block2992;

  block2873:
    // ----- binary operator  ----- SimpleWhile5.ssc(37,4)
    stack0i := x * y;
    // ----- copy  ----- SimpleWhile5.ssc(37,4)
    n := stack0i;
    // ----- copy  ----- SimpleWhile5.ssc(36,19)
    local5 := K;
    // ----- load constant 1  ----- SimpleWhile5.ssc(36,19)
    stack0i := 1;
    // ----- binary operator  ----- SimpleWhile5.ssc(36,19)
    stack0i := local5 + stack0i;
    // ----- copy  ----- SimpleWhile5.ssc(36,19)
    K := stack0i;
    // ----- copy
    stack0i := local5;
    // ----- branch
    goto block2856;

  block2992:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy  ----- SimpleWhile5.ssc(40,2)
    stack0i := return.value;
    // ----- return  ----- SimpleWhile5.ssc(40,2)
    $result := stack0i;
    return;

  block2856$LoopPreheader:
    $Heap$block2856$LoopPreheader := $Heap;
    goto block2856;

  block2805$LoopPreheader:
    $Heap$block2805$LoopPreheader := $Heap;
    goto block2805;

  block2754$LoopPreheader:
    $Heap$block2754$LoopPreheader := $Heap;
    goto block2754;

}



procedure SimpleWhile5.Positive$System.Int32$System.Int32$System.Int32(this: ref, X$in: int where InRange(X$in, System.Int32), Y$in: int where InRange(Y$in, System.Int32), K$in: int where InRange(K$in, System.Int32)) returns ($result: int where InRange($result, System.Int32));
  free requires true;
  free requires true;
  free requires true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  // user-declared postconditions
  ensures 1 <= $result;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation SimpleWhile5.Positive$System.Int32$System.Int32$System.Int32(this: ref, X$in: int, Y$in: int, K$in: int) returns ($result: int)
{
  var X: int where InRange(X, System.Int32), Y: int where InRange(Y, System.Int32), K: int where InRange(K, System.Int32), x: int where InRange(x, System.Int32), stack0b: bool, y: int where InRange(y, System.Int32), local1: int where InRange(local1, System.Int32), stack0i: int, n: int where InRange(n, System.Int32), local3: int where InRange(local3, System.Int32), return.value: int where InRange(return.value, System.Int32), local5: int where InRange(local5, System.Int32), SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32), $Heap$block4114$LoopPreheader: [ref,<x>name]x, $Heap$block4063$LoopPreheader: [ref,<x>name]x, $Heap$block4012$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, SimpleWhile5);
    assume $Heap[this, $allocated] == true;
    X := X$in;
    Y := Y$in;
    K := K$in;
    goto block3978;

  block3978:
    goto block3995;

  block3995:
    // ----- load constant 1  ----- SimpleWhile5.ssc(46,3)
    x := 1;
    goto block4012$LoopPreheader;

  block4012:
    // ----- default loop invariant: allocation and ownership are stable  ----- SimpleWhile5.ssc(47,3)
    assume (forall $o: ref :: $Heap$block4012$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block4012$LoopPreheader[$ot, $allocated] == true && $Heap$block4012$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block4012$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block4012$LoopPreheader[$ot, $ownerFrame]) && $Heap$block4012$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- SimpleWhile5.ssc(47,3)
    assume (forall $o: ref :: ($Heap$block4012$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block4012$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block4012$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block4012$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- SimpleWhile5.ssc(47,3)
    assert (forall $o: ref :: $o != null && $Heap$block4012$LoopPreheader[$o, $allocated] == true ==> $Heap$block4012$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block4012$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- binary operator  ----- SimpleWhile5.ssc(47,3)
    // ----- branch  ----- SimpleWhile5.ssc(47,3)
    goto true4012to4046, false4012to4029;

  true4012to4046:
    assume x >= X;
    goto block4046;

  false4012to4029:
    assume x < X;
    goto block4029;

  block4046:
    // ----- load constant 1  ----- SimpleWhile5.ssc(49,3)
    y := 1;
    goto block4063$LoopPreheader;

  block4029:
    // ----- copy  ----- SimpleWhile5.ssc(47,19)
    local1 := x;
    // ----- load constant 1  ----- SimpleWhile5.ssc(47,19)
    stack0i := 1;
    // ----- binary operator  ----- SimpleWhile5.ssc(47,19)
    stack0i := local1 + stack0i;
    // ----- copy  ----- SimpleWhile5.ssc(47,19)
    x := stack0i;
    // ----- copy
    stack0i := local1;
    // ----- branch  ----- SimpleWhile5.ssc(47,25)
    goto block4012;

  block4063:
    // ----- default loop invariant: allocation and ownership are stable  ----- SimpleWhile5.ssc(50,3)
    assume (forall $o: ref :: $Heap$block4063$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block4063$LoopPreheader[$ot, $allocated] == true && $Heap$block4063$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block4063$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block4063$LoopPreheader[$ot, $ownerFrame]) && $Heap$block4063$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- SimpleWhile5.ssc(50,3)
    assume (forall $o: ref :: ($Heap$block4063$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block4063$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block4063$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block4063$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- SimpleWhile5.ssc(50,3)
    assert (forall $o: ref :: $o != null && $Heap$block4063$LoopPreheader[$o, $allocated] == true ==> $Heap$block4063$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block4063$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- binary operator  ----- SimpleWhile5.ssc(50,3)
    // ----- branch  ----- SimpleWhile5.ssc(50,3)
    goto true4063to4097, false4063to4080;

  true4063to4097:
    assume y >= Y;
    goto block4097;

  false4063to4080:
    assume y < Y;
    goto block4080;

  block4097:
    // ----- load constant 12  ----- SimpleWhile5.ssc(52,3)
    n := 12;
    goto block4114$LoopPreheader;

  block4080:
    // ----- copy  ----- SimpleWhile5.ssc(50,19)
    local3 := y;
    // ----- load constant 1  ----- SimpleWhile5.ssc(50,19)
    stack0i := 1;
    // ----- binary operator  ----- SimpleWhile5.ssc(50,19)
    stack0i := local3 + stack0i;
    // ----- copy  ----- SimpleWhile5.ssc(50,19)
    y := stack0i;
    // ----- copy
    stack0i := local3;
    // ----- branch  ----- SimpleWhile5.ssc(50,25)
    goto block4063;

  block4114:
    // ----- default loop invariant: allocation and ownership are stable  ----- SimpleWhile5.ssc(53,10)
    assume (forall $o: ref :: $Heap$block4114$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block4114$LoopPreheader[$ot, $allocated] == true && $Heap$block4114$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block4114$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block4114$LoopPreheader[$ot, $ownerFrame]) && $Heap$block4114$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- SimpleWhile5.ssc(53,10)
    assume (forall $o: ref :: ($Heap$block4114$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block4114$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block4114$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block4114$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- SimpleWhile5.ssc(53,10)
    assert (forall $o: ref :: $o != null && $Heap$block4114$LoopPreheader[$o, $allocated] == true ==> $Heap$block4114$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block4114$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- load constant 100  ----- SimpleWhile5.ssc(53,10)
    stack0i := 100;
    // ----- binary operator  ----- SimpleWhile5.ssc(53,10)
    // ----- branch  ----- SimpleWhile5.ssc(53,10)
    goto true4114to4148, false4114to4131;

  true4114to4148:
    assume K >= stack0i;
    goto block4148;

  false4114to4131:
    assume K < stack0i;
    goto block4131;

  block4148:
    // ----- copy  ----- SimpleWhile5.ssc(56,3)
    return.value := n;
    // ----- branch
    goto block4250;

  block4131:
    // ----- binary operator  ----- SimpleWhile5.ssc(54,4)
    stack0i := x * y;
    // ----- copy  ----- SimpleWhile5.ssc(54,4)
    n := stack0i;
    // ----- copy  ----- SimpleWhile5.ssc(53,19)
    local5 := K;
    // ----- load constant 1  ----- SimpleWhile5.ssc(53,19)
    stack0i := 1;
    // ----- binary operator  ----- SimpleWhile5.ssc(53,19)
    stack0i := local5 + stack0i;
    // ----- copy  ----- SimpleWhile5.ssc(53,19)
    K := stack0i;
    // ----- copy
    stack0i := local5;
    // ----- branch
    goto block4114;

  block4250:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy  ----- SimpleWhile5.ssc(57,2)
    stack0i := return.value;
    // ----- return  ----- SimpleWhile5.ssc(57,2)
    $result := stack0i;
    return;

  block4114$LoopPreheader:
    $Heap$block4114$LoopPreheader := $Heap;
    goto block4114;

  block4063$LoopPreheader:
    $Heap$block4063$LoopPreheader := $Heap;
    goto block4063;

  block4012$LoopPreheader:
    $Heap$block4012$LoopPreheader := $Heap;
    goto block4012;

}



procedure SimpleWhile5.NegativeWrong$System.Int32$System.Int32$System.Int32(this: ref, X$in: int where InRange(X$in, System.Int32), Y$in: int where InRange(Y$in, System.Int32), K$in: int where InRange(K$in, System.Int32)) returns ($result: int where InRange($result, System.Int32));
  free requires true;
  free requires true;
  free requires true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  // user-declared postconditions
  ensures $result < 0;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation SimpleWhile5.NegativeWrong$System.Int32$System.Int32$System.Int32(this: ref, X$in: int, Y$in: int, K$in: int) returns ($result: int)
{
  var X: int where InRange(X, System.Int32), Y: int where InRange(Y, System.Int32), K: int where InRange(K, System.Int32), x: int where InRange(x, System.Int32), stack0b: bool, local1: int where InRange(local1, System.Int32), stack0i: int, y: int where InRange(y, System.Int32), n: int where InRange(n, System.Int32), local3: int where InRange(local3, System.Int32), return.value: int where InRange(return.value, System.Int32), local5: int where InRange(local5, System.Int32), SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32), $Heap$block5372$LoopPreheader: [ref,<x>name]x, $Heap$block5321$LoopPreheader: [ref,<x>name]x, $Heap$block5270$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, SimpleWhile5);
    assume $Heap[this, $allocated] == true;
    X := X$in;
    Y := Y$in;
    K := K$in;
    goto block5236;

  block5236:
    goto block5253;

  block5253:
    // ----- load constant -1  ----- SimpleWhile5.ssc(63,3)
    x := -1;
    goto block5270$LoopPreheader;

  block5270:
    // ----- default loop invariant: allocation and ownership are stable  ----- SimpleWhile5.ssc(64,3)
    assume (forall $o: ref :: $Heap$block5270$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block5270$LoopPreheader[$ot, $allocated] == true && $Heap$block5270$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block5270$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block5270$LoopPreheader[$ot, $ownerFrame]) && $Heap$block5270$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- SimpleWhile5.ssc(64,3)
    assume (forall $o: ref :: ($Heap$block5270$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block5270$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block5270$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block5270$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- SimpleWhile5.ssc(64,3)
    assert (forall $o: ref :: $o != null && $Heap$block5270$LoopPreheader[$o, $allocated] == true ==> $Heap$block5270$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block5270$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- binary operator  ----- SimpleWhile5.ssc(64,3)
    // ----- branch  ----- SimpleWhile5.ssc(64,3)
    goto true5270to5304, false5270to5287;

  true5270to5304:
    assume X >= x;
    goto block5304;

  false5270to5287:
    assume X < x;
    goto block5287;

  block5304:
    // ----- load constant -1  ----- SimpleWhile5.ssc(66,3)
    y := -1;
    goto block5321$LoopPreheader;

  block5287:
    // ----- copy  ----- SimpleWhile5.ssc(64,19)
    local1 := x;
    // ----- load constant 1  ----- SimpleWhile5.ssc(64,19)
    stack0i := 1;
    // ----- binary operator  ----- SimpleWhile5.ssc(64,19)
    stack0i := local1 - stack0i;
    // ----- copy  ----- SimpleWhile5.ssc(64,19)
    x := stack0i;
    // ----- copy
    stack0i := local1;
    // ----- branch  ----- SimpleWhile5.ssc(64,25)
    goto block5270;

  block5321:
    // ----- default loop invariant: allocation and ownership are stable  ----- SimpleWhile5.ssc(67,3)
    assume (forall $o: ref :: $Heap$block5321$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block5321$LoopPreheader[$ot, $allocated] == true && $Heap$block5321$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block5321$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block5321$LoopPreheader[$ot, $ownerFrame]) && $Heap$block5321$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- SimpleWhile5.ssc(67,3)
    assume (forall $o: ref :: ($Heap$block5321$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block5321$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block5321$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block5321$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- SimpleWhile5.ssc(67,3)
    assert (forall $o: ref :: $o != null && $Heap$block5321$LoopPreheader[$o, $allocated] == true ==> $Heap$block5321$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block5321$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- binary operator  ----- SimpleWhile5.ssc(67,3)
    // ----- branch  ----- SimpleWhile5.ssc(67,3)
    goto true5321to5355, false5321to5338;

  true5321to5355:
    assume Y >= y;
    goto block5355;

  false5321to5338:
    assume Y < y;
    goto block5338;

  block5355:
    // ----- binary operator  ----- SimpleWhile5.ssc(69,3)
    stack0i := x * y;
    // ----- copy  ----- SimpleWhile5.ssc(69,3)
    n := stack0i;
    goto block5372$LoopPreheader;

  block5338:
    // ----- copy  ----- SimpleWhile5.ssc(67,19)
    local3 := y;
    // ----- load constant 1  ----- SimpleWhile5.ssc(67,19)
    stack0i := 1;
    // ----- binary operator  ----- SimpleWhile5.ssc(67,19)
    stack0i := local3 - stack0i;
    // ----- copy  ----- SimpleWhile5.ssc(67,19)
    y := stack0i;
    // ----- copy
    stack0i := local3;
    // ----- branch  ----- SimpleWhile5.ssc(67,25)
    goto block5321;

  block5372:
    // ----- default loop invariant: allocation and ownership are stable  ----- SimpleWhile5.ssc(70,10)
    assume (forall $o: ref :: $Heap$block5372$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block5372$LoopPreheader[$ot, $allocated] == true && $Heap$block5372$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block5372$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block5372$LoopPreheader[$ot, $ownerFrame]) && $Heap$block5372$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- SimpleWhile5.ssc(70,10)
    assume (forall $o: ref :: ($Heap$block5372$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block5372$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block5372$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block5372$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- SimpleWhile5.ssc(70,10)
    assert (forall $o: ref :: $o != null && $Heap$block5372$LoopPreheader[$o, $allocated] == true ==> $Heap$block5372$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block5372$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- load constant 100  ----- SimpleWhile5.ssc(70,10)
    stack0i := 100;
    // ----- binary operator  ----- SimpleWhile5.ssc(70,10)
    // ----- branch  ----- SimpleWhile5.ssc(70,10)
    goto true5372to5406, false5372to5389;

  true5372to5406:
    assume K >= stack0i;
    goto block5406;

  false5372to5389:
    assume K < stack0i;
    goto block5389;

  block5406:
    // ----- copy  ----- SimpleWhile5.ssc(73,3)
    return.value := n;
    // ----- branch
    goto block5508;

  block5389:
    // ----- binary operator  ----- SimpleWhile5.ssc(71,4)
    stack0i := x * y;
    // ----- copy  ----- SimpleWhile5.ssc(71,4)
    n := stack0i;
    // ----- copy  ----- SimpleWhile5.ssc(70,19)
    local5 := K;
    // ----- load constant 1  ----- SimpleWhile5.ssc(70,19)
    stack0i := 1;
    // ----- binary operator  ----- SimpleWhile5.ssc(70,19)
    stack0i := local5 + stack0i;
    // ----- copy  ----- SimpleWhile5.ssc(70,19)
    K := stack0i;
    // ----- copy
    stack0i := local5;
    // ----- branch
    goto block5372;

  block5508:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy  ----- SimpleWhile5.ssc(74,2)
    stack0i := return.value;
    // ----- return  ----- SimpleWhile5.ssc(74,2)
    $result := stack0i;
    return;

  block5372$LoopPreheader:
    $Heap$block5372$LoopPreheader := $Heap;
    goto block5372;

  block5321$LoopPreheader:
    $Heap$block5321$LoopPreheader := $Heap;
    goto block5321;

  block5270$LoopPreheader:
    $Heap$block5270$LoopPreheader := $Heap;
    goto block5270;

}



procedure SimpleWhile5.NegativeIntermediates$System.Int32$System.Int32$System.Int32(this: ref, X$in: int where InRange(X$in, System.Int32), Y$in: int where InRange(Y$in, System.Int32), K$in: int where InRange(K$in, System.Int32)) returns ($result: int where InRange($result, System.Int32));
  free requires true;
  free requires true;
  free requires true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  // user-declared postconditions
  ensures 1 <= $result;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation SimpleWhile5.NegativeIntermediates$System.Int32$System.Int32$System.Int32(this: ref, X$in: int, Y$in: int, K$in: int) returns ($result: int)
{
  var X: int where InRange(X, System.Int32), Y: int where InRange(Y, System.Int32), K: int where InRange(K, System.Int32), x: int where InRange(x, System.Int32), stack0b: bool, local1: int where InRange(local1, System.Int32), stack0i: int, y: int where InRange(y, System.Int32), local3: int where InRange(local3, System.Int32), n: int where InRange(n, System.Int32), return.value: int where InRange(return.value, System.Int32), local5: int where InRange(local5, System.Int32), SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32), $Heap$block6647$LoopPreheader: [ref,<x>name]x, $Heap$block6596$LoopPreheader: [ref,<x>name]x, $Heap$block6545$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, SimpleWhile5);
    assume $Heap[this, $allocated] == true;
    X := X$in;
    Y := Y$in;
    K := K$in;
    goto block6511;

  block6511:
    goto block6528;

  block6528:
    // ----- load constant -1  ----- SimpleWhile5.ssc(80,3)
    x := -1;
    goto block6545$LoopPreheader;

  block6545:
    // ----- default loop invariant: allocation and ownership are stable  ----- SimpleWhile5.ssc(81,3)
    assume (forall $o: ref :: $Heap$block6545$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block6545$LoopPreheader[$ot, $allocated] == true && $Heap$block6545$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block6545$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block6545$LoopPreheader[$ot, $ownerFrame]) && $Heap$block6545$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- SimpleWhile5.ssc(81,3)
    assume (forall $o: ref :: ($Heap$block6545$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block6545$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block6545$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block6545$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- SimpleWhile5.ssc(81,3)
    assert (forall $o: ref :: $o != null && $Heap$block6545$LoopPreheader[$o, $allocated] == true ==> $Heap$block6545$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block6545$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- binary operator  ----- SimpleWhile5.ssc(81,3)
    // ----- branch  ----- SimpleWhile5.ssc(81,3)
    goto true6545to6579, false6545to6562;

  true6545to6579:
    assume X >= x;
    goto block6579;

  false6545to6562:
    assume X < x;
    goto block6562;

  block6579:
    // ----- load constant -1  ----- SimpleWhile5.ssc(83,3)
    y := -1;
    goto block6596$LoopPreheader;

  block6562:
    // ----- copy  ----- SimpleWhile5.ssc(81,19)
    local1 := x;
    // ----- load constant 1  ----- SimpleWhile5.ssc(81,19)
    stack0i := 1;
    // ----- binary operator  ----- SimpleWhile5.ssc(81,19)
    stack0i := local1 - stack0i;
    // ----- copy  ----- SimpleWhile5.ssc(81,19)
    x := stack0i;
    // ----- copy
    stack0i := local1;
    // ----- branch  ----- SimpleWhile5.ssc(81,25)
    goto block6545;

  block6596:
    // ----- default loop invariant: allocation and ownership are stable  ----- SimpleWhile5.ssc(84,3)
    assume (forall $o: ref :: $Heap$block6596$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block6596$LoopPreheader[$ot, $allocated] == true && $Heap$block6596$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block6596$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block6596$LoopPreheader[$ot, $ownerFrame]) && $Heap$block6596$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- SimpleWhile5.ssc(84,3)
    assume (forall $o: ref :: ($Heap$block6596$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block6596$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block6596$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block6596$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- SimpleWhile5.ssc(84,3)
    assert (forall $o: ref :: $o != null && $Heap$block6596$LoopPreheader[$o, $allocated] == true ==> $Heap$block6596$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block6596$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- binary operator  ----- SimpleWhile5.ssc(84,3)
    // ----- branch  ----- SimpleWhile5.ssc(84,3)
    goto true6596to6630, false6596to6613;

  true6596to6630:
    assume Y >= y;
    goto block6630;

  false6596to6613:
    assume Y < y;
    goto block6613;

  block6630:
    // ----- binary operator  ----- SimpleWhile5.ssc(86,3)
    stack0i := x * y;
    // ----- copy  ----- SimpleWhile5.ssc(86,3)
    n := stack0i;
    goto block6647$LoopPreheader;

  block6613:
    // ----- copy  ----- SimpleWhile5.ssc(84,19)
    local3 := y;
    // ----- load constant 1  ----- SimpleWhile5.ssc(84,19)
    stack0i := 1;
    // ----- binary operator  ----- SimpleWhile5.ssc(84,19)
    stack0i := local3 - stack0i;
    // ----- copy  ----- SimpleWhile5.ssc(84,19)
    y := stack0i;
    // ----- copy
    stack0i := local3;
    // ----- branch  ----- SimpleWhile5.ssc(84,25)
    goto block6596;

  block6647:
    // ----- default loop invariant: allocation and ownership are stable  ----- SimpleWhile5.ssc(87,10)
    assume (forall $o: ref :: $Heap$block6647$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block6647$LoopPreheader[$ot, $allocated] == true && $Heap$block6647$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block6647$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block6647$LoopPreheader[$ot, $ownerFrame]) && $Heap$block6647$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- SimpleWhile5.ssc(87,10)
    assume (forall $o: ref :: ($Heap$block6647$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block6647$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block6647$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block6647$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- SimpleWhile5.ssc(87,10)
    assert (forall $o: ref :: $o != null && $Heap$block6647$LoopPreheader[$o, $allocated] == true ==> $Heap$block6647$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block6647$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- load constant 100  ----- SimpleWhile5.ssc(87,10)
    stack0i := 100;
    // ----- binary operator  ----- SimpleWhile5.ssc(87,10)
    // ----- branch  ----- SimpleWhile5.ssc(87,10)
    goto true6647to6681, false6647to6664;

  true6647to6681:
    assume K >= stack0i;
    goto block6681;

  false6647to6664:
    assume K < stack0i;
    goto block6664;

  block6681:
    // ----- copy  ----- SimpleWhile5.ssc(90,3)
    return.value := n;
    // ----- branch
    goto block6783;

  block6664:
    // ----- binary operator  ----- SimpleWhile5.ssc(88,4)
    stack0i := x * y;
    // ----- copy  ----- SimpleWhile5.ssc(88,4)
    n := stack0i;
    // ----- copy  ----- SimpleWhile5.ssc(87,19)
    local5 := K;
    // ----- load constant 1  ----- SimpleWhile5.ssc(87,19)
    stack0i := 1;
    // ----- binary operator  ----- SimpleWhile5.ssc(87,19)
    stack0i := local5 + stack0i;
    // ----- copy  ----- SimpleWhile5.ssc(87,19)
    K := stack0i;
    // ----- copy
    stack0i := local5;
    // ----- branch
    goto block6647;

  block6783:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy  ----- SimpleWhile5.ssc(91,2)
    stack0i := return.value;
    // ----- return  ----- SimpleWhile5.ssc(91,2)
    $result := stack0i;
    return;

  block6647$LoopPreheader:
    $Heap$block6647$LoopPreheader := $Heap;
    goto block6647;

  block6596$LoopPreheader:
    $Heap$block6596$LoopPreheader := $Heap;
    goto block6596;

  block6545$LoopPreheader:
    $Heap$block6545$LoopPreheader := $Heap;
    goto block6545;

}



procedure SimpleWhile5..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == SimpleWhile5 && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(SimpleWhile5 <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation SimpleWhile5..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, SimpleWhile5);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block7531;

  block7531:
    goto block7548;

  block7548:
    // ----- call  ----- SimpleWhile5.ssc(3,7)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == SimpleWhile5 ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := SimpleWhile5;
    assume IsHeap($Heap);
    return;

}



procedure System.Object..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(System.Object <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);


