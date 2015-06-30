// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: -nologo /prover:blank /print:boogie_tmp.@TIME@.bpl /proverLog:boogie_tmp.@TIME@.simplify WhereMotivation.dll

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

const Types.x: <int>name;

const Types.next: <ref>name;

const System.Runtime.InteropServices._MemberInfo: name;

const System.Collections.IEnumerable: name;

const System.Collections.Generic.IEnumerable`1...System.Char: name;

const System.Reflection.ICustomAttributeProvider: name;

const System.IComparable`1...System.String: name;

const System.ICloneable: name;

const System.IComparable: name;

const System.Reflection.IReflect: name;

const System.IEquatable`1...System.String: name;

const System.IConvertible: name;

const Types: name;

const System.Runtime.InteropServices._Type: name;

const System.Reflection.MemberInfo: name;

axiom !IsStaticField(Types.next);

axiom IsDirectlyModifiableField(Types.next);

axiom AsRepField(Types.next, Types) == Types.next;

axiom DeclType(Types.next) == Types;

axiom AsRefField(Types.next, Types) == Types.next;

axiom !IsStaticField(Types.x);

axiom IsDirectlyModifiableField(Types.x);

axiom DeclType(Types.x) == Types;

axiom AsRangeField(Types.x, System.Int32) == Types.x;

axiom Types <: Types;

axiom $BaseClass(Types) == System.Object;

axiom Types <: $BaseClass(Types) && AsDirectSubClass(Types, $BaseClass(Types)) == Types;

axiom !$IsImmutable(Types) && $AsMutable(Types) == Types;

axiom (forall $U: name :: { $U <: Types } $U <: Types ==> $U == Types);

procedure Types.M(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
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



implementation Types.M(this: ref)
{
  var stack0o: ref, o: ref where $Is(o, System.Object);

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    goto block1445;

  block1445:
    goto block1462;

  block1462:
    // ----- serialized AssumeStatement  ----- WhereMotivation.ssc(8,5)
    assume $Heap[this, Types.next] != null;
    goto block1547;

  block1547:
    // ----- nop
    // ----- load field  ----- WhereMotivation.ssc(9,5)
    assert this != null;
    o := $Heap[this, Types.next];
    // ----- serialized AssertStatement  ----- WhereMotivation.ssc(10,5)
    assert $IsNotNull(o, Types);
    goto block1632;

  block1632:
    // ----- nop
    // ----- return  ----- WhereMotivation.ssc(11,3)
    return;

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

procedure Types.MLoop0(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || $f != Types.x) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Types.MLoop0(this: ref)
{
  var stack0o: ref, stack0i: int, stack1i: int, stack0b: bool, o: ref where $Is(o, System.Object), local1: ref where $Is(local1, Types), stack1s: struct, stack1o: ref, temp0: exposeVersionType, local2: int where InRange(local2, System.Int32), temp1: exposeVersionType, $Heap$block2805$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    goto block2635;

  block2635:
    goto block2703;

  block2703:
    // ----- serialized AssumeStatement  ----- WhereMotivation.ssc(16,5)
    assume $Heap[this, Types.next] != null;
    goto block2788;

  block2788:
    // ----- nop
    goto block2805$LoopPreheader;

  block2805:
    // ----- default loop invariant: allocation and ownership are stable  ----- WhereMotivation.ssc(22,5)
    assume (forall $o: ref :: $Heap$block2805$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block2805$LoopPreheader[$ot, $allocated] == true && $Heap$block2805$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block2805$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block2805$LoopPreheader[$ot, $ownerFrame]) && $Heap$block2805$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- WhereMotivation.ssc(22,5)
    assume (forall $o: ref :: ($Heap$block2805$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block2805$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block2805$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block2805$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- WhereMotivation.ssc(22,5)
    assert (forall $o: ref :: $o != null && $Heap$block2805$LoopPreheader[$o, $allocated] == true ==> $Heap$block2805$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block2805$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- load field  ----- WhereMotivation.ssc(22,5)
    assert this != null;
    stack0i := $Heap[this, Types.x];
    // ----- load constant 10  ----- WhereMotivation.ssc(22,5)
    stack1i := 10;
    // ----- binary operator  ----- WhereMotivation.ssc(22,5)
    // ----- branch  ----- WhereMotivation.ssc(22,5)
    goto true2805to2873, false2805to2822;

  true2805to2873:
    assume stack0i >= stack1i;
    goto block2873;

  false2805to2822:
    assume stack0i < stack1i;
    goto block2822;

  block2873:
    // ----- load field  ----- WhereMotivation.ssc(28,5)
    assert this != null;
    o := $Heap[this, Types.next];
    // ----- serialized AssertStatement  ----- WhereMotivation.ssc(29,5)
    assert o == null || $IsNotNull(o, Types);
    goto block2975;

  block2822:
    // ----- copy  ----- WhereMotivation.ssc(23,24)
    local1 := this;
    // ----- copy  ----- WhereMotivation.ssc(23,24)
    stack0o := local1;
    // ----- load token  ----- WhereMotivation.ssc(23,24)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Types);
    // ----- statically resolved GetTypeFromHandle call  ----- WhereMotivation.ssc(23,24)
    stack1o := TypeObject(Types);
    // ----- classic unpack  ----- WhereMotivation.ssc(23,24)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == Types && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block2839;

  block2975:
    // ----- nop
    // ----- serialized AssertStatement  ----- WhereMotivation.ssc(30,5)
    assert $IsNotNull(o, Types);
    goto block3060;

  block2839:
    // ----- load field  ----- WhereMotivation.ssc(24,9)
    assert this != null;
    local2 := $Heap[this, Types.x];
    // ----- load constant 1  ----- WhereMotivation.ssc(24,9)
    stack0i := 1;
    // ----- binary operator  ----- WhereMotivation.ssc(24,9)
    stack0i := local2 + stack0i;
    // ----- store field  ----- WhereMotivation.ssc(24,9)
    assert this != null;
    havoc temp1;
    $Heap[this, $exposeVersion] := temp1;
    $Heap[this, Types.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local2;
    // ----- branch
    goto block3094;

  block3060:
    // ----- nop
    // ----- return  ----- WhereMotivation.ssc(31,3)
    return;

  block3094:
    // ----- copy  ----- WhereMotivation.ssc(25,7)
    stack0o := local1;
    // ----- load token  ----- WhereMotivation.ssc(25,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Types);
    // ----- statically resolved GetTypeFromHandle call  ----- WhereMotivation.ssc(25,7)
    stack1o := TypeObject(Types);
    // ----- classic pack  ----- WhereMotivation.ssc(25,7)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == Types ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := Types;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block2856;

  block2856:
    // ----- branch  ----- WhereMotivation.ssc(26,6)
    goto block2805;

  block2805$LoopPreheader:
    $Heap$block2805$LoopPreheader := $Heap;
    goto block2805;

}



axiom System.Type <: System.Type;

axiom System.Reflection.MemberInfo <: System.Reflection.MemberInfo;

axiom $BaseClass(System.Reflection.MemberInfo) == System.Object;

axiom System.Reflection.MemberInfo <: $BaseClass(System.Reflection.MemberInfo) && AsDirectSubClass(System.Reflection.MemberInfo, $BaseClass(System.Reflection.MemberInfo)) == System.Reflection.MemberInfo;

axiom $IsImmutable(System.Reflection.MemberInfo) && $AsImmutable(System.Reflection.MemberInfo) == System.Reflection.MemberInfo;

axiom System.Reflection.ICustomAttributeProvider <: System.Object;

axiom $IsMemberlessType(System.Reflection.ICustomAttributeProvider);

axiom System.Reflection.MemberInfo <: System.Reflection.ICustomAttributeProvider;

axiom System.Runtime.InteropServices._MemberInfo <: System.Object;

axiom $IsMemberlessType(System.Runtime.InteropServices._MemberInfo);

axiom System.Reflection.MemberInfo <: System.Runtime.InteropServices._MemberInfo;

axiom $IsMemberlessType(System.Reflection.MemberInfo);

axiom $BaseClass(System.Type) == System.Reflection.MemberInfo;

axiom System.Type <: $BaseClass(System.Type) && AsDirectSubClass(System.Type, $BaseClass(System.Type)) == System.Type;

axiom $IsImmutable(System.Type) && $AsImmutable(System.Type) == System.Type;

axiom System.Runtime.InteropServices._Type <: System.Object;

axiom $IsMemberlessType(System.Runtime.InteropServices._Type);

axiom System.Type <: System.Runtime.InteropServices._Type;

axiom System.Reflection.IReflect <: System.Object;

axiom $IsMemberlessType(System.Reflection.IReflect);

axiom System.Type <: System.Reflection.IReflect;

axiom $IsMemberlessType(System.Type);

procedure Types.MLoop1(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || $f != Types.x) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Types.MLoop1(this: ref)
{
  var stack0o: ref, local1: ref where $Is(local1, Types), stack1s: struct, stack1o: ref, temp0: exposeVersionType, stack0i: int, stack1i: int, stack0b: bool, local2: int where InRange(local2, System.Int32), temp1: exposeVersionType, o: ref where $Is(o, System.Object), $Heap$block4318$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    goto block4148;

  block4148:
    goto block4216;

  block4216:
    // ----- serialized AssumeStatement  ----- WhereMotivation.ssc(36,5)
    assume $Heap[this, Types.next] != null;
    goto block4301;

  block4301:
    // ----- nop
    // ----- copy  ----- WhereMotivation.ssc(41,22)
    local1 := this;
    // ----- copy  ----- WhereMotivation.ssc(41,22)
    stack0o := local1;
    // ----- load token  ----- WhereMotivation.ssc(41,22)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Types);
    // ----- statically resolved GetTypeFromHandle call  ----- WhereMotivation.ssc(41,22)
    stack1o := TypeObject(Types);
    // ----- classic unpack  ----- WhereMotivation.ssc(41,22)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == Types && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block4318$LoopPreheader;

  block4318:
    // ----- default loop invariant: allocation and ownership are stable  ----- WhereMotivation.ssc(42,7)
    assume (forall $o: ref :: $Heap$block4318$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block4318$LoopPreheader[$ot, $allocated] == true && $Heap$block4318$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block4318$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block4318$LoopPreheader[$ot, $ownerFrame]) && $Heap$block4318$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- WhereMotivation.ssc(42,7)
    assume (forall $o: ref :: ($Heap$block4318$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block4318$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block4318$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block4318$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- WhereMotivation.ssc(42,7)
    assert (forall $o: ref :: $o != null && $Heap$block4318$LoopPreheader[$o, $allocated] == true ==> $Heap$block4318$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block4318$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- load field  ----- WhereMotivation.ssc(42,7)
    assert this != null;
    stack0i := $Heap[this, Types.x];
    // ----- load constant 10  ----- WhereMotivation.ssc(42,7)
    stack1i := 10;
    // ----- binary operator  ----- WhereMotivation.ssc(42,7)
    // ----- branch  ----- WhereMotivation.ssc(42,7)
    goto true4318to4352, false4318to4335;

  true4318to4352:
    assume stack0i >= stack1i;
    goto block4352;

  false4318to4335:
    assume stack0i < stack1i;
    goto block4335;

  block4352:
    // ----- branch
    goto block4488;

  block4335:
    // ----- load field  ----- WhereMotivation.ssc(43,9)
    assert this != null;
    local2 := $Heap[this, Types.x];
    // ----- load constant 1  ----- WhereMotivation.ssc(43,9)
    stack0i := 1;
    // ----- binary operator  ----- WhereMotivation.ssc(43,9)
    stack0i := local2 + stack0i;
    // ----- store field  ----- WhereMotivation.ssc(43,9)
    assert this != null;
    havoc temp1;
    $Heap[this, $exposeVersion] := temp1;
    $Heap[this, Types.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local2;
    // ----- branch  ----- WhereMotivation.ssc(44,8)
    goto block4318;

  block4488:
    // ----- copy  ----- WhereMotivation.ssc(45,5)
    stack0o := local1;
    // ----- load token  ----- WhereMotivation.ssc(45,5)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Types);
    // ----- statically resolved GetTypeFromHandle call  ----- WhereMotivation.ssc(45,5)
    stack1o := TypeObject(Types);
    // ----- classic pack  ----- WhereMotivation.ssc(45,5)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == Types ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := Types;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block4369;

  block4369:
    // ----- load field  ----- WhereMotivation.ssc(49,5)
    assert this != null;
    o := $Heap[this, Types.next];
    // ----- serialized AssertStatement  ----- WhereMotivation.ssc(50,5)
    assert $IsNotNull(o, Types);
    goto block4454;

  block4454:
    // ----- nop
    // ----- return  ----- WhereMotivation.ssc(51,3)
    return;

  block4318$LoopPreheader:
    $Heap$block4318$LoopPreheader := $Heap;
    goto block4318;

}



procedure Types.MLoop2(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || $f != Types.x) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Types.MLoop2(this: ref)
{
  var stack0o: ref, local1: ref where $Is(local1, Types), stack1s: struct, stack1o: ref, temp0: exposeVersionType, stack0i: int, stack1i: int, stack0b: bool, local2: int where InRange(local2, System.Int32), temp1: exposeVersionType, o: ref where $Is(o, System.Object), $Heap$block5729$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    goto block5559;

  block5559:
    goto block5627;

  block5627:
    // ----- serialized AssumeStatement  ----- WhereMotivation.ssc(56,5)
    assume $Heap[this, Types.next] != null;
    goto block5712;

  block5712:
    // ----- nop
    // ----- copy  ----- WhereMotivation.ssc(58,22)
    local1 := this;
    // ----- copy  ----- WhereMotivation.ssc(58,22)
    stack0o := local1;
    // ----- load token  ----- WhereMotivation.ssc(58,22)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Types);
    // ----- statically resolved GetTypeFromHandle call  ----- WhereMotivation.ssc(58,22)
    stack1o := TypeObject(Types);
    // ----- classic unpack  ----- WhereMotivation.ssc(58,22)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == Types && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block5729$LoopPreheader;

  block5729:
    // ----- default loop invariant: allocation and ownership are stable  ----- WhereMotivation.ssc(60,7)
    assume (forall $o: ref :: $Heap$block5729$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block5729$LoopPreheader[$ot, $allocated] == true && $Heap$block5729$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block5729$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block5729$LoopPreheader[$ot, $ownerFrame]) && $Heap$block5729$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- WhereMotivation.ssc(60,7)
    assume (forall $o: ref :: ($Heap$block5729$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block5729$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block5729$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block5729$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- WhereMotivation.ssc(60,7)
    assert (forall $o: ref :: $o != null && $Heap$block5729$LoopPreheader[$o, $allocated] == true ==> $Heap$block5729$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block5729$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- load field  ----- WhereMotivation.ssc(60,7)
    assert this != null;
    stack0i := $Heap[this, Types.x];
    // ----- load constant 10  ----- WhereMotivation.ssc(60,7)
    stack1i := 10;
    // ----- binary operator  ----- WhereMotivation.ssc(60,7)
    // ----- branch  ----- WhereMotivation.ssc(60,7)
    goto true5729to5763, false5729to5746;

  true5729to5763:
    assume stack0i >= stack1i;
    goto block5763;

  false5729to5746:
    assume stack0i < stack1i;
    goto block5746;

  block5763:
    // ----- load field  ----- WhereMotivation.ssc(64,7)
    assert this != null;
    o := $Heap[this, Types.next];
    // ----- serialized AssertStatement  ----- WhereMotivation.ssc(65,7)
    assert o == null || $IsNotNull(o, Types);
    goto block5865;

  block5746:
    // ----- load field  ----- WhereMotivation.ssc(61,9)
    assert this != null;
    local2 := $Heap[this, Types.x];
    // ----- load constant 1  ----- WhereMotivation.ssc(61,9)
    stack0i := 1;
    // ----- binary operator  ----- WhereMotivation.ssc(61,9)
    stack0i := local2 + stack0i;
    // ----- store field  ----- WhereMotivation.ssc(61,9)
    assert this != null;
    havoc temp1;
    $Heap[this, $exposeVersion] := temp1;
    $Heap[this, Types.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local2;
    // ----- branch  ----- WhereMotivation.ssc(62,8)
    goto block5729;

  block5865:
    // ----- nop
    // ----- serialized AssertStatement  ----- WhereMotivation.ssc(66,7)
    assert $IsNotNull(o, Types);
    goto block5950;

  block5950:
    // ----- nop
    // ----- branch
    goto block6001;

  block6001:
    // ----- copy  ----- WhereMotivation.ssc(67,5)
    stack0o := local1;
    // ----- load token  ----- WhereMotivation.ssc(67,5)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Types);
    // ----- statically resolved GetTypeFromHandle call  ----- WhereMotivation.ssc(67,5)
    stack1o := TypeObject(Types);
    // ----- classic pack  ----- WhereMotivation.ssc(67,5)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == Types ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := Types;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block5967;

  block5967:
    // ----- return  ----- WhereMotivation.ssc(68,3)
    return;

  block5729$LoopPreheader:
    $Heap$block5729$LoopPreheader := $Heap;
    goto block5729;

}



procedure Types.MLoop3(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || $f != Types.x) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Types.MLoop3(this: ref)
{
  var stack50000o: ref, stack0o: ref, ty: ref where $Is(ty, Types), local1: ref where $Is(local1, Types), stack1s: struct, stack1o: ref, temp0: exposeVersionType, local2: ref where $Is(local2, Types), temp1: exposeVersionType, stack0i: int, stack1i: int, stack0b: bool, local3: int where InRange(local3, System.Int32), temp2: exposeVersionType, $Heap$block7055$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    goto block6953;

  block6953:
    goto block7021;

  block7021:
    // ----- new object  ----- WhereMotivation.ssc(75,5)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Types;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- WhereMotivation.ssc(75,5)
    assert stack50000o != null;
    call Types..ctor(stack50000o);
    // ----- copy  ----- WhereMotivation.ssc(75,5)
    stack0o := stack50000o;
    // ----- copy  ----- WhereMotivation.ssc(75,5)
    ty := stack0o;
    // ----- copy  ----- WhereMotivation.ssc(76,22)
    local1 := ty;
    // ----- copy  ----- WhereMotivation.ssc(76,22)
    stack0o := local1;
    // ----- load token  ----- WhereMotivation.ssc(76,22)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Types);
    // ----- statically resolved GetTypeFromHandle call  ----- WhereMotivation.ssc(76,22)
    stack1o := TypeObject(Types);
    // ----- classic unpack  ----- WhereMotivation.ssc(76,22)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == Types && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block7038;

  block7038:
    // ----- copy  ----- WhereMotivation.ssc(77,24)
    local2 := this;
    // ----- copy  ----- WhereMotivation.ssc(77,24)
    stack0o := local2;
    // ----- load token  ----- WhereMotivation.ssc(77,24)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Types);
    // ----- statically resolved GetTypeFromHandle call  ----- WhereMotivation.ssc(77,24)
    stack1o := TypeObject(Types);
    // ----- classic unpack  ----- WhereMotivation.ssc(77,24)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == Types && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp1;
    $Heap[stack0o, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    goto block7055$LoopPreheader;

  block7055:
    // ----- default loop invariant: allocation and ownership are stable  ----- WhereMotivation.ssc(78,9)
    assume (forall $o: ref :: $Heap$block7055$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block7055$LoopPreheader[$ot, $allocated] == true && $Heap$block7055$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block7055$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block7055$LoopPreheader[$ot, $ownerFrame]) && $Heap$block7055$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- WhereMotivation.ssc(78,9)
    assume (forall $o: ref :: ($Heap$block7055$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block7055$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block7055$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block7055$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- WhereMotivation.ssc(78,9)
    assert (forall $o: ref :: $o != null && $Heap$block7055$LoopPreheader[$o, $allocated] == true ==> $Heap$block7055$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block7055$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- load field  ----- WhereMotivation.ssc(78,9)
    assert this != null;
    stack0i := $Heap[this, Types.x];
    // ----- load constant 10  ----- WhereMotivation.ssc(78,9)
    stack1i := 10;
    // ----- binary operator  ----- WhereMotivation.ssc(78,9)
    // ----- branch  ----- WhereMotivation.ssc(78,9)
    goto true7055to7089, false7055to7072;

  true7055to7089:
    assume stack0i >= stack1i;
    goto block7089;

  false7055to7072:
    assume stack0i < stack1i;
    goto block7072;

  block7089:
    // ----- branch
    goto block7157;

  block7072:
    // ----- load field  ----- WhereMotivation.ssc(79,11)
    assert this != null;
    local3 := $Heap[this, Types.x];
    // ----- load constant 1  ----- WhereMotivation.ssc(79,11)
    stack0i := 1;
    // ----- binary operator  ----- WhereMotivation.ssc(79,11)
    stack0i := local3 + stack0i;
    // ----- store field  ----- WhereMotivation.ssc(79,11)
    assert this != null;
    havoc temp2;
    $Heap[this, $exposeVersion] := temp2;
    $Heap[this, Types.x] := stack0i;
    assume IsHeap($Heap);
    // ----- copy
    stack0i := local3;
    // ----- branch  ----- WhereMotivation.ssc(80,10)
    goto block7055;

  block7157:
    // ----- copy  ----- WhereMotivation.ssc(81,7)
    stack0o := local2;
    // ----- load token  ----- WhereMotivation.ssc(81,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Types);
    // ----- statically resolved GetTypeFromHandle call  ----- WhereMotivation.ssc(81,7)
    stack1o := TypeObject(Types);
    // ----- classic pack  ----- WhereMotivation.ssc(81,7)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == Types ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := Types;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block7106;

  block7106:
    // ----- branch
    goto block7174;

  block7174:
    // ----- copy  ----- WhereMotivation.ssc(82,5)
    stack0o := local1;
    // ----- load token  ----- WhereMotivation.ssc(82,5)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Types);
    // ----- statically resolved GetTypeFromHandle call  ----- WhereMotivation.ssc(82,5)
    stack1o := TypeObject(Types);
    // ----- classic pack  ----- WhereMotivation.ssc(82,5)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == Types ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := Types;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block7123;

  block7123:
    // ----- return  ----- WhereMotivation.ssc(83,3)
    return;

  block7055$LoopPreheader:
    $Heap$block7055$LoopPreheader := $Heap;
    goto block7055;

}



procedure Types..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Types && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Types <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure Types.SLoop0(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || $f != Types.next) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Types.SLoop0(this: ref)
{
  var local0: ref where $Is(local0, Types), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType, i: int where InRange(i, System.Int32), stack0i: int, stack0b: bool, local3: int where InRange(local3, System.Int32), $Heap$block8330$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    goto block8228;

  block8228:
    goto block8296;

  block8296:
    // ----- copy  ----- WhereMotivation.ssc(88,22)
    local0 := this;
    // ----- copy  ----- WhereMotivation.ssc(88,22)
    stack0o := local0;
    // ----- load token  ----- WhereMotivation.ssc(88,22)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Types);
    // ----- statically resolved GetTypeFromHandle call  ----- WhereMotivation.ssc(88,22)
    stack1o := TypeObject(Types);
    // ----- classic unpack  ----- WhereMotivation.ssc(88,22)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == Types && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block8313;

  block8313:
    // ----- load constant 0  ----- WhereMotivation.ssc(89,12)
    i := 0;
    goto block8330$LoopPreheader;

  block8330:
    // ----- default loop invariant: allocation and ownership are stable  ----- WhereMotivation.ssc(90,24)
    assume (forall $o: ref :: $Heap$block8330$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block8330$LoopPreheader[$ot, $allocated] == true && $Heap$block8330$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block8330$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block8330$LoopPreheader[$ot, $ownerFrame]) && $Heap$block8330$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- WhereMotivation.ssc(90,24)
    assume (forall $o: ref :: ($Heap$block8330$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block8330$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block8330$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block8330$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- WhereMotivation.ssc(90,24)
    assert (forall $o: ref :: $o != null && $Heap$block8330$LoopPreheader[$o, $allocated] == true ==> $Heap$block8330$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block8330$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- serialized LoopInvariant  ----- WhereMotivation.ssc(90,24)
    assert ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this) && (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == Types ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    goto block8415;

  block8415:
    // ----- nop
    // ----- load constant 10  ----- WhereMotivation.ssc(89,23)
    stack0i := 10;
    // ----- binary operator  ----- WhereMotivation.ssc(89,23)
    // ----- branch  ----- WhereMotivation.ssc(89,23)
    goto true8415to8449, false8415to8432;

  true8415to8449:
    assume i >= stack0i;
    goto block8449;

  false8415to8432:
    assume i < stack0i;
    goto block8432;

  block8449:
    stack0o := null;
    // ----- store field  ----- WhereMotivation.ssc(95,7)
    assert this != null;
    assert !($Heap[this, $inv] <: Types) || $Heap[this, $localinv] == System.Object;
    assert stack0o == null || $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == Types);
    $Heap[this, Types.next] := stack0o;
    call $UpdateOwnersForRep(this, Types, stack0o);
    assume IsHeap($Heap);
    // ----- branch
    goto block8500;

  block8432:
    // ----- call  ----- WhereMotivation.ssc(92,9)
    call stack0o := Types.SomeValue();
    // ----- store field  ----- WhereMotivation.ssc(92,9)
    assert this != null;
    assert !($Heap[this, $inv] <: Types) || $Heap[this, $localinv] == System.Object;
    assert stack0o == null || $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == Types);
    $Heap[this, Types.next] := stack0o;
    call $UpdateOwnersForRep(this, Types, stack0o);
    assume IsHeap($Heap);
    // ----- copy  ----- WhereMotivation.ssc(89,31)
    local3 := i;
    // ----- load constant 1  ----- WhereMotivation.ssc(89,31)
    stack0i := 1;
    // ----- binary operator  ----- WhereMotivation.ssc(89,31)
    stack0i := local3 + stack0i;
    // ----- copy  ----- WhereMotivation.ssc(89,31)
    i := stack0i;
    // ----- copy
    stack0i := local3;
    // ----- branch
    goto block8330;

  block8500:
    // ----- copy  ----- WhereMotivation.ssc(96,5)
    stack0o := local0;
    // ----- load token  ----- WhereMotivation.ssc(96,5)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Types);
    // ----- statically resolved GetTypeFromHandle call  ----- WhereMotivation.ssc(96,5)
    stack1o := TypeObject(Types);
    // ----- classic pack  ----- WhereMotivation.ssc(96,5)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == Types ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := Types;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block8466;

  block8466:
    // ----- return  ----- WhereMotivation.ssc(97,3)
    return;

  block8330$LoopPreheader:
    $Heap$block8330$LoopPreheader := $Heap;
    goto block8330;

}



procedure Types.SomeValue() returns ($result: ref where $Is($result, Types));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures $Heap[$result, $allocated] == true;
  free ensures $Is($result, Types);
  // user-declared postconditions
  ensures $Heap[$result, $ownerFrame] == $PeerGroupPlaceholder && (forall $fpc: ref :: $fpc != null && old($Heap)[$fpc, $allocated] == true ==> !($Heap[$fpc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$fpc, $ownerFrame] == $Heap[$result, $ownerFrame]));
  // return value is peer consistent
  ensures $result == null || (($Heap[$result, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame]) || $Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure Types.SLoop1(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || $f != Types.next) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Types.SLoop1(this: ref)
{
  var local0: ref where $Is(local0, Types), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType, i: int where InRange(i, System.Int32), stack0i: int, stack0b: bool, local2: int where InRange(local2, System.Int32), o: ref where $Is(o, System.Object), $Heap$block9571$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    goto block9469;

  block9469:
    goto block9537;

  block9537:
    // ----- copy  ----- WhereMotivation.ssc(102,22)
    local0 := this;
    // ----- copy  ----- WhereMotivation.ssc(102,22)
    stack0o := local0;
    // ----- load token  ----- WhereMotivation.ssc(102,22)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Types);
    // ----- statically resolved GetTypeFromHandle call  ----- WhereMotivation.ssc(102,22)
    stack1o := TypeObject(Types);
    // ----- classic unpack  ----- WhereMotivation.ssc(102,22)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == Types && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block9554;

  block9554:
    // ----- load constant 0  ----- WhereMotivation.ssc(103,12)
    i := 0;
    goto block9571$LoopPreheader;

  block9571:
    // ----- default loop invariant: allocation and ownership are stable  ----- WhereMotivation.ssc(103,23)
    assume (forall $o: ref :: $Heap$block9571$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block9571$LoopPreheader[$ot, $allocated] == true && $Heap$block9571$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block9571$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block9571$LoopPreheader[$ot, $ownerFrame]) && $Heap$block9571$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- WhereMotivation.ssc(103,23)
    assume (forall $o: ref :: ($Heap$block9571$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block9571$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block9571$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block9571$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- WhereMotivation.ssc(103,23)
    assert (forall $o: ref :: $o != null && $Heap$block9571$LoopPreheader[$o, $allocated] == true ==> $Heap$block9571$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block9571$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- load constant 10  ----- WhereMotivation.ssc(103,23)
    stack0i := 10;
    // ----- binary operator  ----- WhereMotivation.ssc(103,23)
    // ----- branch  ----- WhereMotivation.ssc(103,23)
    goto true9571to9605, false9571to9588;

  true9571to9605:
    assume i >= stack0i;
    goto block9605;

  false9571to9588:
    assume i < stack0i;
    goto block9588;

  block9605:
    // ----- load field  ----- WhereMotivation.ssc(107,7)
    assert this != null;
    o := $Heap[this, Types.next];
    // ----- serialized AssertStatement  ----- WhereMotivation.ssc(108,7)
    assert o == null || $IsNotNull(o, Types);
    goto block9707;

  block9588:
    // ----- call  ----- WhereMotivation.ssc(104,9)
    call stack0o := Types.SomeValue();
    // ----- store field  ----- WhereMotivation.ssc(104,9)
    assert this != null;
    assert !($Heap[this, $inv] <: Types) || $Heap[this, $localinv] == System.Object;
    assert stack0o == null || $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == Types);
    $Heap[this, Types.next] := stack0o;
    call $UpdateOwnersForRep(this, Types, stack0o);
    assume IsHeap($Heap);
    // ----- copy  ----- WhereMotivation.ssc(103,31)
    local2 := i;
    // ----- load constant 1  ----- WhereMotivation.ssc(103,31)
    stack0i := 1;
    // ----- binary operator  ----- WhereMotivation.ssc(103,31)
    stack0i := local2 + stack0i;
    // ----- copy  ----- WhereMotivation.ssc(103,31)
    i := stack0i;
    // ----- copy
    stack0i := local2;
    // ----- branch
    goto block9571;

  block9707:
    // ----- nop
    // ----- serialized AssertStatement  ----- WhereMotivation.ssc(109,7)
    assert $IsNotNull(o, Types);
    goto block9792;

  block9792:
    // ----- nop
    stack0o := null;
    // ----- store field  ----- WhereMotivation.ssc(111,7)
    assert this != null;
    assert !($Heap[this, $inv] <: Types) || $Heap[this, $localinv] == System.Object;
    assert stack0o == null || $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == Types);
    $Heap[this, Types.next] := stack0o;
    call $UpdateOwnersForRep(this, Types, stack0o);
    assume IsHeap($Heap);
    // ----- branch
    goto block9843;

  block9843:
    // ----- copy  ----- WhereMotivation.ssc(112,5)
    stack0o := local0;
    // ----- load token  ----- WhereMotivation.ssc(112,5)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Types);
    // ----- statically resolved GetTypeFromHandle call  ----- WhereMotivation.ssc(112,5)
    stack1o := TypeObject(Types);
    // ----- classic pack  ----- WhereMotivation.ssc(112,5)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == Types ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := Types;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block9809;

  block9809:
    // ----- return  ----- WhereMotivation.ssc(113,3)
    return;

  block9571$LoopPreheader:
    $Heap$block9571$LoopPreheader := $Heap;
    goto block9571;

}



implementation Types.SomeValue() returns ($result: ref)
{
  var stack50000o: ref, stack0o: ref, return.value: ref where $Is(return.value, Types), SS$Display.Return.Local: ref where $Is(SS$Display.Return.Local, Types);

  entry:
    goto block10710;

  block10710:
    goto block10727;

  block10727:
    // ----- new object  ----- WhereMotivation.ssc(118,5)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Types;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- WhereMotivation.ssc(118,5)
    assert stack50000o != null;
    call Types..ctor(stack50000o);
    // ----- copy  ----- WhereMotivation.ssc(118,5)
    stack0o := stack50000o;
    // ----- copy  ----- WhereMotivation.ssc(118,5)
    return.value := stack0o;
    // ----- branch
    goto block10829;

  block10829:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy  ----- WhereMotivation.ssc(119,3)
    stack0o := return.value;
    // ----- return  ----- WhereMotivation.ssc(119,3)
    $result := stack0o;
    return;

}



procedure Types.MCall(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
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



implementation Types.MCall(this: ref)
{
  var stack0o: ref, o: ref where $Is(o, System.Object);

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    goto block11322;

  block11322:
    goto block11339;

  block11339:
    // ----- serialized AssumeStatement  ----- WhereMotivation.ssc(122,5)
    assume $Heap[this, Types.next] != null;
    goto block11424;

  block11424:
    // ----- nop
    // ----- call  ----- WhereMotivation.ssc(124,5)
    assert this != null;
    call Types.M(this);
    // ----- load field  ----- WhereMotivation.ssc(126,5)
    assert this != null;
    o := $Heap[this, Types.next];
    // ----- serialized AssertStatement  ----- WhereMotivation.ssc(127,5)
    assert $IsNotNull(o, Types);
    goto block11509;

  block11509:
    // ----- nop
    // ----- return  ----- WhereMotivation.ssc(128,3)
    return;

}



implementation Types..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, Types.x] == 0;
    assume $Heap[this, Types.next] == null;
    goto block11866;

  block11866:
    goto block11883;

  block11883:
    // ----- call  ----- WhereMotivation.ssc(3,21)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == Types ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := Types;
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


