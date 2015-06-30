// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: -nologo /prover:blank /print:boogie_tmp.@TIME@.bpl /proverLog:boogie_tmp.@TIME@.simplify Strings.dll

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

const test3.XY.p: <ref>name;

const test3.MyStrings.abcString: <ref>name;

const test3.XY.o: <ref>name;

const System.Boolean: name;

const Microsoft.Contracts.GuardException: name;

const System.Runtime.InteropServices._Exception: name;

const System.Reflection.ICustomAttributeProvider: name;

const System.Runtime.InteropServices._MemberInfo: name;

const System.IComparable: name;

const System.Collections.IEnumerable: name;

const System.IConvertible: name;

const System.Reflection.MemberInfo: name;

const System.ICloneable: name;

const System.Reflection.IReflect: name;

const System.Exception: name;

const System.Collections.Generic.IEnumerable`1...System.Char: name;

const System.IEquatable`1...System.String: name;

const test3.MyStrings: name;

const Microsoft.Contracts.ObjectInvariantException: name;

const test3.XY: name;

const System.Runtime.Serialization.ISerializable: name;

const System.IComparable`1...System.String: name;

const System.Runtime.InteropServices._Type: name;

axiom !IsStaticField(test3.MyStrings.abcString);

axiom IsDirectlyModifiableField(test3.MyStrings.abcString);

axiom DeclType(test3.MyStrings.abcString) == test3.MyStrings;

axiom AsNonNullRefField(test3.MyStrings.abcString, System.String) == test3.MyStrings.abcString;

function #System.String.Insert$System.Int32$System.String$notnull([ref,<x>name]x, ref, int, ref) returns (ref);

function ##System.String.Insert$System.Int32$System.String$notnull(exposeVersionType, int, ref) returns (ref);

function #System.String.IndexOf$System.String$notnull([ref,<x>name]x, ref, ref) returns (int);

function ##System.String.IndexOf$System.String$notnull(exposeVersionType, ref) returns (int);

function #System.String.Concat$System.String$System.String([ref,<x>name]x, ref, ref) returns (ref);

axiom !IsStaticField(test3.XY.o);

axiom IsDirectlyModifiableField(test3.XY.o);

axiom AsRepField(test3.XY.o, test3.XY) == test3.XY.o;

axiom DeclType(test3.XY.o) == test3.XY;

axiom AsRefField(test3.XY.o, System.Object) == test3.XY.o;

axiom !IsStaticField(test3.XY.p);

axiom IsDirectlyModifiableField(test3.XY.p);

axiom AsPeerField(test3.XY.p) == test3.XY.p;

axiom DeclType(test3.XY.p) == test3.XY;

axiom AsRefField(test3.XY.p, System.Object) == test3.XY.p;

axiom test3.MyStrings <: test3.MyStrings;

axiom $BaseClass(test3.MyStrings) == System.Object;

axiom test3.MyStrings <: $BaseClass(test3.MyStrings) && AsDirectSubClass(test3.MyStrings, $BaseClass(test3.MyStrings)) == test3.MyStrings;

axiom !$IsImmutable(test3.MyStrings) && $AsMutable(test3.MyStrings) == test3.MyStrings;

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

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: test3.MyStrings } IsHeap($h) && $h[$oi, $inv] <: test3.MyStrings && $h[$oi, $localinv] != System.Object ==> $StringLength($h[$oi, test3.MyStrings.abcString]) == 3);

procedure test3.MyStrings.StringCoolness0(this: ref);
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



implementation test3.MyStrings.StringCoolness0(this: ref)
{
  var s: ref where $Is(s, System.String), stack0i: int, stack1o: ref, t: ref where $Is(t, System.String), stack0o: ref, idx: int where InRange(idx, System.Int32);

  entry:
    assume $IsNotNull(this, test3.MyStrings);
    assume $Heap[this, $allocated] == true;
    goto block1989;

  block1989:
    goto block2091;

  block2091:
    // ----- nop
    // ----- load constant "hi"  ----- Strings.ssc(11,7)
    s := $stringLiteral0;
    // ----- load constant 1  ----- Strings.ssc(12,7)
    stack0i := 1;
    // ----- load constant "foo"  ----- Strings.ssc(12,7)
    stack1o := $stringLiteral1;
    // ----- call  ----- Strings.ssc(12,7)
    assert s != null;
    call t := System.String.Insert$System.Int32$System.String$notnull(s, stack0i, stack1o);
    // ----- serialized AssertStatement  ----- Strings.ssc(13,7)
    assert $StringLength(t) == 5;
    goto block2176;

  block2176:
    // ----- nop
    // ----- load constant "f"  ----- Strings.ssc(14,7)
    stack0o := $stringLiteral3;
    // ----- call  ----- Strings.ssc(14,7)
    assert t != null;
    call idx := System.String.IndexOf$System.String$notnull(t, stack0o);
    // ----- copy  ----- Strings.ssc(15,7)
    stack0i := idx;
    // ----- load constant "hi"  ----- Strings.ssc(15,7)
    stack1o := $stringLiteral0;
    // ----- call  ----- Strings.ssc(15,7)
    assert t != null;
    call stack0o := System.String.Insert$System.Int32$System.String$notnull(t, stack0i, stack1o);
    // ----- return
    return;

}



axiom (forall $Heap: [ref,<x>name]x, this: ref, startIndex$in: int, value$in: ref :: { #System.String.Insert$System.Int32$System.String$notnull($Heap, this, startIndex$in, value$in) } IsHeap($Heap) && InRange(startIndex$in, System.Int32) && $IsNotNull(value$in, System.String) && value$in != null && 0 <= startIndex$in && startIndex$in <= $StringLength(this) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[value$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[value$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)) ==> $Heap[#System.String.Insert$System.Int32$System.String$notnull($Heap, this, startIndex$in, value$in), $allocated] == true && $IsNotNull(#System.String.Insert$System.Int32$System.String$notnull($Heap, this, startIndex$in, value$in), System.String) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[#System.String.Insert$System.Int32$System.String$notnull($Heap, this, startIndex$in, value$in), $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[#System.String.Insert$System.Int32$System.String$notnull($Heap, this, startIndex$in, value$in), $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));

axiom (forall $Heap: [ref,<x>name]x, this: ref, startIndex$in: int, value$in: ref :: { #System.String.Insert$System.Int32$System.String$notnull($Heap, this, startIndex$in, value$in) } this != null && $typeof(this) <: System.String && $Heap[this, $inv] == $typeof(this) && $Heap[this, $localinv] == $typeof(this) && IsHeap($Heap) && $Heap[this, $allocated] == true ==> #System.String.Insert$System.Int32$System.String$notnull($Heap, this, startIndex$in, value$in) == ##System.String.Insert$System.Int32$System.String$notnull($Heap[this, $exposeVersion], startIndex$in, value$in));

procedure System.String.Insert$System.Int32$System.String$notnull(this: ref, startIndex$in: int where InRange(startIndex$in, System.Int32), value$in: ref where $IsNotNull(value$in, System.String)) returns ($result: ref where $IsNotNull($result, System.String));
  free requires true;
  free requires $Heap[value$in, $allocated] == true;
  // user-declared preconditions
  requires value$in != null;
  requires 0 <= startIndex$in;
  requires startIndex$in <= $StringLength(this);
  requires (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(this) == this;
  requires (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[value$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[value$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(value$in) == value$in;
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures $Heap[$result, $allocated] == true;
  free ensures $IsNotNull($result, System.String);
  // user-declared postconditions
  ensures $StringLength($result) == $StringLength(this) + $StringLength(value$in);
  // return value is peer consistent
  ensures (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  free ensures $result == #System.String.Insert$System.Int32$System.String$notnull($Heap, this, startIndex$in, value$in);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



axiom (forall $Heap: [ref,<x>name]x, this: ref, value$in: ref :: { #System.String.IndexOf$System.String$notnull($Heap, this, value$in) } IsHeap($Heap) && $IsNotNull(value$in, System.String) && value$in != null && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[value$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[value$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)) ==> InRange(#System.String.IndexOf$System.String$notnull($Heap, this, value$in), System.Int32));

axiom (forall $Heap: [ref,<x>name]x, this: ref, value$in: ref :: { #System.String.IndexOf$System.String$notnull($Heap, this, value$in) } this != null && $typeof(this) <: System.String && $Heap[this, $inv] == $typeof(this) && $Heap[this, $localinv] == $typeof(this) && IsHeap($Heap) && $Heap[this, $allocated] == true ==> #System.String.IndexOf$System.String$notnull($Heap, this, value$in) == ##System.String.IndexOf$System.String$notnull($Heap[this, $exposeVersion], value$in));

procedure System.String.IndexOf$System.String$notnull(this: ref, value$in: ref where $IsNotNull(value$in, System.String)) returns ($result: int where InRange($result, System.Int32));
  free requires $Heap[value$in, $allocated] == true;
  // user-declared preconditions
  requires value$in != null;
  requires (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(this) == this;
  requires (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[value$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[value$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(value$in) == value$in;
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  // user-declared postconditions
  ensures -1 <= $result && $result < $StringLength(this);
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  free ensures $Heap == old($Heap);
  free ensures $result == #System.String.IndexOf$System.String$notnull($Heap, this, value$in);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure test3.MyStrings.StringCoolness1(this: ref);
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



implementation test3.MyStrings.StringCoolness1(this: ref)
{
  var s: ref where $Is(s, System.String), stack0i: int, stack1o: ref, t: ref where $Is(t, System.String), stack0o: ref, idx: int where InRange(idx, System.Int32), stack0b: bool;

  entry:
    assume $IsNotNull(this, test3.MyStrings);
    assume $Heap[this, $allocated] == true;
    goto block2822;

  block2822:
    goto block2924;

  block2924:
    // ----- nop
    // ----- load constant "hi"  ----- Strings.ssc(22,7)
    s := $stringLiteral0;
    // ----- load constant 1  ----- Strings.ssc(23,7)
    stack0i := 1;
    // ----- load constant "foo"  ----- Strings.ssc(23,7)
    stack1o := $stringLiteral1;
    // ----- call  ----- Strings.ssc(23,7)
    assert s != null;
    call t := System.String.Insert$System.Int32$System.String$notnull(s, stack0i, stack1o);
    // ----- serialized AssertStatement  ----- Strings.ssc(24,7)
    assert $StringLength(t) == 5;
    goto block3009;

  block3009:
    // ----- nop
    // ----- load constant "f"  ----- Strings.ssc(25,7)
    stack0o := $stringLiteral3;
    // ----- call  ----- Strings.ssc(25,7)
    assert t != null;
    call idx := System.String.IndexOf$System.String$notnull(t, stack0o);
    // ----- load constant -1  ----- Strings.ssc(26,7)
    stack0i := -1;
    // ----- binary operator  ----- Strings.ssc(26,7)
    // ----- branch  ----- Strings.ssc(26,7)
    goto true3009to3043, false3009to3026;

  true3009to3043:
    assume idx == stack0i;
    goto block3043;

  false3009to3026:
    assume idx != stack0i;
    goto block3026;

  block3043:
    // ----- return
    return;

  block3026:
    // ----- copy  ----- Strings.ssc(27,9)
    stack0i := idx;
    // ----- load constant "hi"  ----- Strings.ssc(27,9)
    stack1o := $stringLiteral0;
    // ----- call  ----- Strings.ssc(27,9)
    assert t != null;
    call stack0o := System.String.Insert$System.Int32$System.String$notnull(t, stack0i, stack1o);
    goto block3043;

}



axiom (forall $U: name :: { $U <: System.Boolean } $U <: System.Boolean ==> $U == System.Boolean);

procedure test3.MyStrings.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
  free requires true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures true;
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



implementation test3.MyStrings.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0o: ref, stack0i: int, stack1i: int, stack0b: bool, local0: bool where true, stack50000o: ref, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, test3.MyStrings);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block3655;

  block3655:
    goto block3672;

  block3672:
    // ----- load field  ----- Strings.ssc(34,5)
    assert this != null;
    stack0o := $Heap[this, test3.MyStrings.abcString];
    // ----- string length  ----- Strings.ssc(34,5)
    assert stack0o != null;
    stack0i := $StringLength(stack0o);
    // ----- load constant 3  ----- Strings.ssc(34,5)
    stack1i := 3;
    // ----- binary operator  ----- Strings.ssc(34,5)
    // ----- branch  ----- Strings.ssc(34,5)
    goto true3672to3774, false3672to3689;

  true3672to3774:
    assume stack0i == stack1i;
    goto block3774;

  false3672to3689:
    assume stack0i != stack1i;
    goto block3689;

  block3774:
    // ----- load constant 1
    local0 := true;
    // ----- branch
    goto block3791;

  block3689:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true3689to3740, false3689to3706;

  true3689to3740:
    assume !stack0b;
    goto block3740;

  false3689to3706:
    assume stack0b;
    goto block3706;

  block3740:
    // ----- load constant 0
    local0 := false;
    // ----- branch
    goto block3791;

  block3706:
    assume false;
    // ----- new object
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy
    stack0o := stack50000o;
    // ----- throw
    assert stack0o != null;
    assume false;
    return;

  block3791:
    // ----- copy
    SS$Display.Return.Local := local0;
    // ----- copy
    stack0b := local0;
    // ----- return
    $result := stack0b;
    return;

}



axiom Microsoft.Contracts.ObjectInvariantException <: Microsoft.Contracts.ObjectInvariantException;

axiom Microsoft.Contracts.GuardException <: Microsoft.Contracts.GuardException;

axiom System.Exception <: System.Exception;

axiom $BaseClass(System.Exception) == System.Object;

axiom System.Exception <: $BaseClass(System.Exception) && AsDirectSubClass(System.Exception, $BaseClass(System.Exception)) == System.Exception;

axiom !$IsImmutable(System.Exception) && $AsMutable(System.Exception) == System.Exception;

axiom System.Runtime.Serialization.ISerializable <: System.Object;

axiom $IsMemberlessType(System.Runtime.Serialization.ISerializable);

axiom System.Exception <: System.Runtime.Serialization.ISerializable;

axiom System.Runtime.InteropServices._Exception <: System.Object;

axiom $IsMemberlessType(System.Runtime.InteropServices._Exception);

axiom System.Exception <: System.Runtime.InteropServices._Exception;

axiom $BaseClass(Microsoft.Contracts.GuardException) == System.Exception;

axiom Microsoft.Contracts.GuardException <: $BaseClass(Microsoft.Contracts.GuardException) && AsDirectSubClass(Microsoft.Contracts.GuardException, $BaseClass(Microsoft.Contracts.GuardException)) == Microsoft.Contracts.GuardException;

axiom !$IsImmutable(Microsoft.Contracts.GuardException) && $AsMutable(Microsoft.Contracts.GuardException) == Microsoft.Contracts.GuardException;

axiom $BaseClass(Microsoft.Contracts.ObjectInvariantException) == Microsoft.Contracts.GuardException;

axiom Microsoft.Contracts.ObjectInvariantException <: $BaseClass(Microsoft.Contracts.ObjectInvariantException) && AsDirectSubClass(Microsoft.Contracts.ObjectInvariantException, $BaseClass(Microsoft.Contracts.ObjectInvariantException)) == Microsoft.Contracts.ObjectInvariantException;

axiom !$IsImmutable(Microsoft.Contracts.ObjectInvariantException) && $AsMutable(Microsoft.Contracts.ObjectInvariantException) == Microsoft.Contracts.ObjectInvariantException;

procedure Microsoft.Contracts.ObjectInvariantException..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Microsoft.Contracts.ObjectInvariantException && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Microsoft.Contracts.ObjectInvariantException <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure test3.MyStrings.StringCoolness2$System.Boolean(this: ref, choice$in: bool where true);
  free requires true;
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



implementation test3.MyStrings.StringCoolness2$System.Boolean(this: ref, choice$in: bool)
{
  var choice: bool where true, s: ref where $Is(s, System.String), stack0b: bool, stack0i: int, stack1o: ref, t: ref where $Is(t, System.String), stack0o: ref, idx: int where InRange(idx, System.Int32);

  entry:
    assume $IsNotNull(this, test3.MyStrings);
    assume $Heap[this, $allocated] == true;
    choice := choice$in;
    goto block4488;

  block4488:
    goto block4590;

  block4590:
    // ----- nop
    // ----- load constant "hi"  ----- Strings.ssc(39,7)
    s := $stringLiteral0;
    // ----- copy  ----- Strings.ssc(41,7)
    stack0b := choice;
    // ----- unary operator  ----- Strings.ssc(41,7)
    // ----- branch  ----- Strings.ssc(41,7)
    goto true4590to4624, false4590to4607;

  true4590to4624:
    assume !stack0b;
    goto block4624;

  false4590to4607:
    assume stack0b;
    goto block4607;

  block4624:
    // ----- load constant 1  ----- Strings.ssc(44,9)
    stack0i := 1;
    // ----- load field  ----- Strings.ssc(44,9)
    assert this != null;
    stack1o := $Heap[this, test3.MyStrings.abcString];
    // ----- call  ----- Strings.ssc(44,9)
    assert s != null;
    call t := System.String.Insert$System.Int32$System.String$notnull(s, stack0i, stack1o);
    // ----- nop  ----- Strings.ssc(46,7)
    goto block4641;

  block4607:
    // ----- load constant 1  ----- Strings.ssc(42,9)
    stack0i := 1;
    // ----- load constant "foo"  ----- Strings.ssc(42,9)
    stack1o := $stringLiteral1;
    // ----- call  ----- Strings.ssc(42,9)
    assert s != null;
    call t := System.String.Insert$System.Int32$System.String$notnull(s, stack0i, stack1o);
    // ----- branch  ----- Strings.ssc(43,9)
    goto block4641;

  block4641:
    // ----- serialized AssertStatement  ----- Strings.ssc(46,7)
    assert $StringLength(t) == 5;
    goto block4726;

  block4726:
    // ----- nop
    // ----- load constant "f"  ----- Strings.ssc(47,7)
    stack0o := $stringLiteral3;
    // ----- call  ----- Strings.ssc(47,7)
    assert t != null;
    call idx := System.String.IndexOf$System.String$notnull(t, stack0o);
    // ----- load constant -1  ----- Strings.ssc(48,7)
    stack0i := -1;
    // ----- binary operator  ----- Strings.ssc(48,7)
    // ----- branch  ----- Strings.ssc(48,7)
    goto true4726to4760, false4726to4743;

  true4726to4760:
    assume idx == stack0i;
    goto block4760;

  false4726to4743:
    assume idx != stack0i;
    goto block4743;

  block4760:
    // ----- return
    return;

  block4743:
    // ----- copy  ----- Strings.ssc(49,9)
    stack0i := idx;
    // ----- load constant "hi"  ----- Strings.ssc(49,9)
    stack1o := $stringLiteral0;
    // ----- call  ----- Strings.ssc(49,9)
    assert t != null;
    call stack0o := System.String.Insert$System.Int32$System.String$notnull(t, stack0i, stack1o);
    goto block4760;

}



procedure test3.MyStrings.StringCoolness3(this: ref) returns ($result: ref where $IsNotNull($result, System.String));
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures $Heap[$result, $allocated] == true;
  free ensures $IsNotNull($result, System.String);
  // user-declared postconditions
  ensures $StringLength($result) == 8;
  // return value is peer consistent
  ensures ($Heap[$result, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame]) || $Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation test3.MyStrings.StringCoolness3(this: ref) returns ($result: ref)
{
  var stack0o: ref, stack1o: ref, s: ref where $Is(s, System.String), return.value: ref where $Is(return.value, System.String), SS$Display.Return.Local: ref where $Is(SS$Display.Return.Local, System.String);

  entry:
    assume $IsNotNull(this, test3.MyStrings);
    assume $Heap[this, $allocated] == true;
    goto block5831;

  block5831:
    goto block5933;

  block5933:
    // ----- nop
    // ----- load constant "hi"  ----- Strings.ssc(56,7)
    stack0o := $stringLiteral0;
    // ----- load field  ----- Strings.ssc(56,7)
    assert this != null;
    stack1o := $Heap[this, test3.MyStrings.abcString];
    // ----- call  ----- Strings.ssc(56,7)
    call stack0o := System.String.Concat$System.String$System.String(stack0o, stack1o);
    // ----- load constant "foo"  ----- Strings.ssc(56,7)
    stack1o := $stringLiteral1;
    // ----- call  ----- Strings.ssc(56,7)
    call s := System.String.Concat$System.String$System.String(stack0o, stack1o);
    // ----- copy  ----- Strings.ssc(57,7)
    stack0o := s;
    assert stack0o != null;
    return.value := stack0o;
    // ----- branch
    goto block6035;

  block6035:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0o := return.value;
    // ----- return
    $result := stack0o;
    return;

}



axiom (forall $Heap: [ref,<x>name]x, str0$in: ref, str1$in: ref :: { #System.String.Concat$System.String$System.String($Heap, str0$in, str1$in) } IsHeap($Heap) && $Is(str0$in, System.String) && $Is(str1$in, System.String) && (str0$in == null || (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[str0$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[str0$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc))) && (str1$in == null || (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[str1$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[str1$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc))) ==> $Heap[#System.String.Concat$System.String$System.String($Heap, str0$in, str1$in), $allocated] == true && $IsNotNull(#System.String.Concat$System.String$System.String($Heap, str0$in, str1$in), System.String) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[#System.String.Concat$System.String$System.String($Heap, str0$in, str1$in), $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[#System.String.Concat$System.String$System.String($Heap, str0$in, str1$in), $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));

procedure System.String.Concat$System.String$System.String(str0$in: ref where $Is(str0$in, System.String), str1$in: ref where $Is(str1$in, System.String)) returns ($result: ref where $IsNotNull($result, System.String));
  free requires $Heap[str0$in, $allocated] == true;
  free requires $Heap[str1$in, $allocated] == true;
  requires str0$in == null || (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[str0$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[str0$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(str0$in) == str0$in;
  requires str1$in == null || (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[str1$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[str1$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // parameter of a pure method
  free requires $AsPureObject(str1$in) == str1$in;
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures $Heap[$result, $allocated] == true;
  free ensures $IsNotNull($result, System.String);
  // user-declared postconditions
  ensures $StringLength($result) == cast($IfThenElse(str0$in == null, 0, $StringLength(str0$in)),int) + cast($IfThenElse(str1$in == null, 0, $StringLength(str1$in)),int);
  // return value is peer consistent
  ensures (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  free ensures $result == #System.String.Concat$System.String$System.String($Heap, str0$in, str1$in);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure test3.MyStrings.MyStringInsert$System.String$notnull$System.Int32$System.String$notnull(this: ref, a$in: ref where $IsNotNull(a$in, System.String), i$in: int where InRange(i$in, System.Int32), b$in: ref where $IsNotNull(b$in, System.String)) returns ($result: ref where $IsNotNull($result, System.String));
  free requires $Heap[a$in, $allocated] == true;
  free requires true;
  free requires $Heap[b$in, $allocated] == true;
  // user-declared preconditions
  requires 0 <= i$in;
  requires i$in <= $StringLength(a$in);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[a$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[a$in, $ownerRef], $inv] <: $Heap[a$in, $ownerFrame]) || $Heap[$Heap[a$in, $ownerRef], $localinv] == $BaseClass($Heap[a$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[a$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[a$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[b$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[b$in, $ownerRef], $inv] <: $Heap[b$in, $ownerFrame]) || $Heap[$Heap[b$in, $ownerRef], $localinv] == $BaseClass($Heap[b$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[b$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[b$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures $Heap[$result, $allocated] == true;
  free ensures $IsNotNull($result, System.String);
  // user-declared postconditions
  ensures $StringLength($result) == $StringLength(a$in) + $StringLength(b$in);
  // return value is peer consistent
  ensures ($Heap[$result, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame]) || $Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation test3.MyStrings.MyStringInsert$System.String$notnull$System.Int32$System.String$notnull(this: ref, a$in: ref, i$in: int, b$in: ref) returns ($result: ref)
{
  var a: ref where $IsNotNull(a, System.String), i: int where InRange(i, System.Int32), b: ref where $IsNotNull(b, System.String), stack0i: int, stack1o: ref, r: ref where $Is(r, System.String), stack0o: ref, return.value: ref where $Is(return.value, System.String), SS$Display.Return.Local: ref where $Is(SS$Display.Return.Local, System.String);

  entry:
    assume $IsNotNull(this, test3.MyStrings);
    assume $Heap[this, $allocated] == true;
    a := a$in;
    i := i$in;
    b := b$in;
    goto block7021;

  block7021:
    goto block7327;

  block7327:
    // ----- nop
    // ----- copy  ----- Strings.ssc(65,7)
    stack0i := i;
    // ----- copy  ----- Strings.ssc(65,7)
    stack1o := b;
    // ----- call  ----- Strings.ssc(65,7)
    assert a != null;
    call r := System.String.Insert$System.Int32$System.String$notnull(a, stack0i, stack1o);
    // ----- serialized AssertStatement  ----- Strings.ssc(66,7)
    assert r != null;
    goto block7412;

  block7412:
    // ----- nop
    // ----- serialized AssertStatement  ----- Strings.ssc(67,7)
    assert $StringLength(r) == $StringLength(a) + $StringLength(b);
    goto block7497;

  block7497:
    // ----- nop
    // ----- copy  ----- Strings.ssc(68,7)
    stack0o := r;
    assert stack0o != null;
    return.value := stack0o;
    // ----- branch
    goto block7599;

  block7599:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0o := return.value;
    // ----- return
    $result := stack0o;
    return;

}



procedure test3.MyStrings.MyStringIndexOf$System.String$notnull$System.String$notnull(this: ref, a$in: ref where $IsNotNull(a$in, System.String), b$in: ref where $IsNotNull(b$in, System.String)) returns ($result: int where InRange($result, System.Int32));
  free requires $Heap[a$in, $allocated] == true;
  free requires $Heap[b$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[a$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[a$in, $ownerRef], $inv] <: $Heap[a$in, $ownerFrame]) || $Heap[$Heap[a$in, $ownerRef], $localinv] == $BaseClass($Heap[a$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[a$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[a$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[b$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[b$in, $ownerRef], $inv] <: $Heap[b$in, $ownerFrame]) || $Heap[$Heap[b$in, $ownerRef], $localinv] == $BaseClass($Heap[b$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[b$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[b$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures true;
  free ensures InRange($result, System.Int32);
  // user-declared postconditions
  ensures -1 <= $result && $result < $StringLength(a$in);
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



implementation test3.MyStrings.MyStringIndexOf$System.String$notnull$System.String$notnull(this: ref, a$in: ref, b$in: ref) returns ($result: int)
{
  var a: ref where $IsNotNull(a, System.String), b: ref where $IsNotNull(b, System.String), stack0o: ref, r: int where InRange(r, System.Int32), return.value: int where InRange(return.value, System.Int32), SS$Display.Return.Local: int where InRange(SS$Display.Return.Local, System.Int32), stack0i: int;

  entry:
    assume $IsNotNull(this, test3.MyStrings);
    assume $Heap[this, $allocated] == true;
    a := a$in;
    b := b$in;
    goto block8585;

  block8585:
    goto block8789;

  block8789:
    // ----- nop
    // ----- copy  ----- Strings.ssc(74,7)
    stack0o := b;
    // ----- call  ----- Strings.ssc(74,7)
    assert a != null;
    call r := System.String.IndexOf$System.String$notnull(a, stack0o);
    // ----- serialized AssertStatement  ----- Strings.ssc(75,7)
    assert -1 <= r && r < $StringLength(a);
    goto block8908;

  block8908:
    // ----- nop
    // ----- copy  ----- Strings.ssc(76,7)
    return.value := r;
    // ----- branch
    goto block9027;

  block9027:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0i := return.value;
    // ----- return
    $result := stack0i;
    return;

}



procedure test3.MyStrings.MyStringConcat$System.String$System.String(this: ref, str0$in: ref where $Is(str0$in, System.String), str1$in: ref where $Is(str1$in, System.String)) returns ($result: ref where $IsNotNull($result, System.String));
  free requires $Heap[str0$in, $allocated] == true;
  free requires $Heap[str1$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires str0$in == null || (($Heap[str0$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[str0$in, $ownerRef], $inv] <: $Heap[str0$in, $ownerFrame]) || $Heap[$Heap[str0$in, $ownerRef], $localinv] == $BaseClass($Heap[str0$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[str0$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[str0$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
  requires str1$in == null || (($Heap[str1$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[str1$in, $ownerRef], $inv] <: $Heap[str1$in, $ownerFrame]) || $Heap[$Heap[str1$in, $ownerRef], $localinv] == $BaseClass($Heap[str1$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[str1$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[str1$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
  free requires $BeingConstructed == null;
  modifies $Heap;
  free ensures $Heap[$result, $allocated] == true;
  free ensures $IsNotNull($result, System.String);
  // user-declared postconditions
  ensures $StringLength($result) == cast($IfThenElse(str0$in == null, 0, $StringLength(str0$in)),int) + cast($IfThenElse(str1$in == null, 0, $StringLength(str1$in)),int);
  // return value is peer consistent
  ensures ($Heap[$result, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[$result, $ownerRef], $inv] <: $Heap[$result, $ownerFrame]) || $Heap[$Heap[$result, $ownerRef], $localinv] == $BaseClass($Heap[$result, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[$result, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[$result, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation test3.MyStrings.MyStringConcat$System.String$System.String(this: ref, str0$in: ref, str1$in: ref) returns ($result: ref)
{
  var str0: ref where $Is(str0, System.String), str1: ref where $Is(str1, System.String), stack0o: ref, stack1o: ref, r: ref where $Is(r, System.String), return.value: ref where $Is(return.value, System.String), SS$Display.Return.Local: ref where $Is(SS$Display.Return.Local, System.String);

  entry:
    assume $IsNotNull(this, test3.MyStrings);
    assume $Heap[this, $allocated] == true;
    str0 := str0$in;
    str1 := str1$in;
    goto block10030;

  block10030:
    goto block10132;

  block10132:
    // ----- nop
    // ----- copy  ----- Strings.ssc(84,7)
    stack0o := str0;
    // ----- copy  ----- Strings.ssc(84,7)
    stack1o := str1;
    // ----- call  ----- Strings.ssc(84,7)
    call r := System.String.Concat$System.String$System.String(stack0o, stack1o);
    // ----- serialized AssertStatement  ----- Strings.ssc(85,7)
    assert r != null;
    goto block10217;

  block10217:
    // ----- nop
    // ----- serialized AssertStatement  ----- Strings.ssc(86,7)
    assert $StringLength(r) == cast($IfThenElse(str0 == null, 0, $StringLength(str0)),int) + cast($IfThenElse(str1 == null, 0, $StringLength(str1)),int);
    goto block10404;

  block10404:
    // ----- nop
    // ----- copy  ----- Strings.ssc(89,7)
    stack0o := r;
    assert stack0o != null;
    return.value := stack0o;
    // ----- branch
    goto block10608;

  block10608:
    // ----- nop
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0o := return.value;
    // ----- return
    $result := stack0o;
    return;

}



procedure test3.MyStrings.UnpackString$System.String$notnull(this: ref, s$in: ref where $IsNotNull(s$in, System.String));
  free requires $Heap[s$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[s$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[s$in, $ownerRef], $inv] <: $Heap[s$in, $ownerFrame]) || $Heap[$Heap[s$in, $ownerRef], $localinv] == $BaseClass($Heap[s$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[s$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[s$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation test3.MyStrings.UnpackString$System.String$notnull(this: ref, s$in: ref)
{
  var s: ref where $IsNotNull(s, System.String), local1: ref where $Is(local1, System.String), stack0o: ref, stack1s: struct, stack1o: ref;

  entry:
    assume $IsNotNull(this, test3.MyStrings);
    assume $Heap[this, $allocated] == true;
    s := s$in;
    goto block11679;

  block11679:
    goto block11883;

  block11883:
    // ----- nop
    // ----- copy  ----- Strings.ssc(93,24)
    local1 := s;
    // ----- copy  ----- Strings.ssc(93,24)
    stack0o := local1;
    // ----- load token  ----- Strings.ssc(93,24)
    havoc stack1s;
    assume $IsTokenForType(stack1s, System.String);
    // ----- statically resolved GetTypeFromHandle call  ----- Strings.ssc(93,24)
    stack1o := TypeObject(System.String);
    // ----- classic unpack  ----- Strings.ssc(93,24)
    assert stack0o != null;
    assert false;
    goto block11900;

  block11900:
    // ----- branch
    goto block11951;

  block11951:
    // ----- copy  ----- Strings.ssc(99,7)
    stack0o := local1;
    // ----- load token  ----- Strings.ssc(99,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, System.String);
    // ----- statically resolved GetTypeFromHandle call  ----- Strings.ssc(99,7)
    stack1o := TypeObject(System.String);
    // ----- classic pack  ----- Strings.ssc(99,7)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == System.String ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := System.String;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block11917;

  block11917:
    // ----- return
    return;

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

procedure test3.MyStrings..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == test3.MyStrings && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(test3.MyStrings <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation test3.MyStrings..ctor(this: ref)
{
  var stack0o: ref, temp0: ref;

  entry:
    assume $IsNotNull(this, test3.MyStrings);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block12427;

  block12427:
    goto block12444;

  block12444:
    // ----- load constant "abc"  ----- Strings.ssc(33,5)
    stack0o := $stringLiteral8;
    // ----- store field  ----- Strings.ssc(33,5)
    assert this != null;
    assert !($Heap[this, $inv] <: test3.MyStrings) || $Heap[this, $localinv] == System.Object;
    $Heap[this, test3.MyStrings.abcString] := stack0o;
    assume IsHeap($Heap);
    // ----- call  ----- Strings.ssc(7,16)
    assert this != null;
    call System.Object..ctor(this);
    goto block12512;

  block12512:
    // ----- FrameGuard processing  ----- Strings.ssc(7,24)
    temp0 := this;
    // ----- classic pack  ----- Strings.ssc(7,24)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert $StringLength($Heap[temp0, test3.MyStrings.abcString]) == 3;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == test3.MyStrings ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := test3.MyStrings;
    assume IsHeap($Heap);
    // ----- return
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



procedure test3.MyStrings..cctor();
  free requires $BeingConstructed == null;
  modifies $Heap;
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



implementation test3.MyStrings..cctor()
{

  entry:
    goto block12835;

  block12835:
    goto block12886;

  block12886:
    // ----- nop
    // ----- return
    return;

}



axiom test3.XY <: test3.XY;

axiom $BaseClass(test3.XY) == System.Object;

axiom test3.XY <: $BaseClass(test3.XY) && AsDirectSubClass(test3.XY, $BaseClass(test3.XY)) == test3.XY;

axiom !$IsImmutable(test3.XY) && $AsMutable(test3.XY) == test3.XY;

procedure test3.XY..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == test3.XY && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(test3.XY <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation test3.XY..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, test3.XY);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, test3.XY.o] == null;
    assume $Heap[this, test3.XY.p] == null;
    goto block13090;

  block13090:
    goto block13107;

  block13107:
    // ----- call  ----- Strings.ssc(108,7)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return  ----- Strings.ssc(109,5)
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == test3.XY ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := test3.XY;
    assume IsHeap($Heap);
    return;

}



procedure test3.XY.M0$System.String$notnull(this: ref, s$in: ref where $IsNotNull(s$in, System.String));
  free requires $Heap[s$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == test3.XY && $Heap[this, $localinv] == $typeof(this);
  requires ($Heap[s$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[s$in, $ownerRef], $inv] <: $Heap[s$in, $ownerFrame]) || $Heap[$Heap[s$in, $ownerRef], $localinv] == $BaseClass($Heap[s$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[s$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[s$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation test3.XY.M0$System.String$notnull(this: ref, s$in: ref)
{
  var s: ref where $IsNotNull(s, System.String), local1: ref where $Is(local1, test3.XY), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType;

  entry:
    assume $IsNotNull(this, test3.XY);
    assume $Heap[this, $allocated] == true;
    s := s$in;
    goto block13430;

  block13430:
    goto block13583;

  block13583:
    // ----- nop
    // ----- copy  ----- Strings.ssc(112,24)
    local1 := this;
    // ----- copy  ----- Strings.ssc(112,24)
    stack0o := local1;
    // ----- load token  ----- Strings.ssc(112,24)
    havoc stack1s;
    assume $IsTokenForType(stack1s, test3.XY);
    // ----- statically resolved GetTypeFromHandle call  ----- Strings.ssc(112,24)
    stack1o := TypeObject(test3.XY);
    // ----- classic unpack  ----- Strings.ssc(112,24)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == test3.XY && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block13600;

  block13600:
    // ----- store field  ----- Strings.ssc(113,9)
    assert this != null;
    assert !($Heap[this, $inv] <: test3.XY) || $Heap[this, $localinv] == System.Object;
    assert s == null || $Heap[s, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[s, $ownerRef] == this && $Heap[s, $ownerFrame] == test3.XY);
    assert s == null || !$IsImmutable($typeof(s));
    $Heap[this, test3.XY.o] := s;
    call $UpdateOwnersForRep(this, test3.XY, s);
    assume IsHeap($Heap);
    // ----- branch
    goto block13651;

  block13651:
    // ----- copy  ----- Strings.ssc(114,7)
    stack0o := local1;
    // ----- load token  ----- Strings.ssc(114,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, test3.XY);
    // ----- statically resolved GetTypeFromHandle call  ----- Strings.ssc(114,7)
    stack1o := TypeObject(test3.XY);
    // ----- classic pack  ----- Strings.ssc(114,7)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == test3.XY ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := test3.XY;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block13617;

  block13617:
    // ----- return
    return;

}



procedure test3.XY.M1$System.String(this: ref, s$in: ref where $Is(s$in, System.String));
  free requires $Heap[s$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == test3.XY && $Heap[this, $localinv] == $typeof(this);
  requires s$in == null || (($Heap[s$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[s$in, $ownerRef], $inv] <: $Heap[s$in, $ownerFrame]) || $Heap[$Heap[s$in, $ownerRef], $localinv] == $BaseClass($Heap[s$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[s$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[s$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
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



implementation test3.XY.M1$System.String(this: ref, s$in: ref)
{
  var s: ref where $Is(s, System.String), local0: ref where $Is(local0, test3.XY), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType, temp1: exposeVersionType;

  entry:
    assume $IsNotNull(this, test3.XY);
    assume $Heap[this, $allocated] == true;
    s := s$in;
    goto block14144;

  block14144:
    goto block14212;

  block14212:
    // ----- copy  ----- Strings.ssc(118,24)
    local0 := this;
    // ----- copy  ----- Strings.ssc(118,24)
    stack0o := local0;
    // ----- load token  ----- Strings.ssc(118,24)
    havoc stack1s;
    assume $IsTokenForType(stack1s, test3.XY);
    // ----- statically resolved GetTypeFromHandle call  ----- Strings.ssc(118,24)
    stack1o := TypeObject(test3.XY);
    // ----- classic unpack  ----- Strings.ssc(118,24)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == test3.XY && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block14229;

  block14229:
    // ----- store field  ----- Strings.ssc(119,9)
    assert this != null;
    havoc temp1;
    $Heap[this, $exposeVersion] := temp1;
    assert s == null || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && $Heap[s, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[s, $ownerRef], $inv] <: $Heap[s, $ownerFrame]) || $Heap[$Heap[s, $ownerRef], $localinv] == $BaseClass($Heap[s, $ownerFrame]))) || ((!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[s, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerRef] == $Heap[s, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[s, $ownerFrame]);
    assert s == null || !$IsImmutable($typeof(s));
    $Heap[this, test3.XY.p] := s;
    call $UpdateOwnersForPeer(this, s);
    assume IsHeap($Heap);
    // ----- branch
    goto block14280;

  block14280:
    // ----- copy  ----- Strings.ssc(120,7)
    stack0o := local0;
    // ----- load token  ----- Strings.ssc(120,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, test3.XY);
    // ----- statically resolved GetTypeFromHandle call  ----- Strings.ssc(120,7)
    stack1o := TypeObject(test3.XY);
    // ----- classic pack  ----- Strings.ssc(120,7)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == test3.XY ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := test3.XY;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block14246;

  block14246:
    // ----- return  ----- Strings.ssc(121,5)
    return;

}



procedure test3.XY.M2(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == test3.XY && $Heap[this, $localinv] == $typeof(this);
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



implementation test3.XY.M2(this: ref)
{
  var local0: ref where $Is(local0, test3.XY), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType, temp1: exposeVersionType;

  entry:
    assume $IsNotNull(this, test3.XY);
    assume $Heap[this, $allocated] == true;
    goto block14722;

  block14722:
    goto block14790;

  block14790:
    // ----- copy  ----- Strings.ssc(124,24)
    local0 := this;
    // ----- copy  ----- Strings.ssc(124,24)
    stack0o := local0;
    // ----- load token  ----- Strings.ssc(124,24)
    havoc stack1s;
    assume $IsTokenForType(stack1s, test3.XY);
    // ----- statically resolved GetTypeFromHandle call  ----- Strings.ssc(124,24)
    stack1o := TypeObject(test3.XY);
    // ----- classic unpack  ----- Strings.ssc(124,24)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == test3.XY && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block14807;

  block14807:
    stack0o := null;
    // ----- store field  ----- Strings.ssc(125,9)
    assert this != null;
    assert !($Heap[this, $inv] <: test3.XY) || $Heap[this, $localinv] == System.Object;
    assert stack0o == null || $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[stack0o, $ownerRef] == this && $Heap[stack0o, $ownerFrame] == test3.XY);
    assert stack0o == null || !$IsImmutable($typeof(stack0o));
    $Heap[this, test3.XY.o] := stack0o;
    call $UpdateOwnersForRep(this, test3.XY, stack0o);
    assume IsHeap($Heap);
    stack0o := null;
    // ----- store field  ----- Strings.ssc(126,9)
    assert this != null;
    havoc temp1;
    $Heap[this, $exposeVersion] := temp1;
    assert stack0o == null || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) || ((!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerRef] == $Heap[stack0o, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[stack0o, $ownerFrame]);
    assert stack0o == null || !$IsImmutable($typeof(stack0o));
    $Heap[this, test3.XY.p] := stack0o;
    call $UpdateOwnersForPeer(this, stack0o);
    assume IsHeap($Heap);
    // ----- branch
    goto block14858;

  block14858:
    // ----- copy  ----- Strings.ssc(127,7)
    stack0o := local0;
    // ----- load token  ----- Strings.ssc(127,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, test3.XY);
    // ----- statically resolved GetTypeFromHandle call  ----- Strings.ssc(127,7)
    stack1o := TypeObject(test3.XY);
    // ----- classic pack  ----- Strings.ssc(127,7)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == test3.XY ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := test3.XY;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block14824;

  block14824:
    // ----- return  ----- Strings.ssc(128,5)
    return;

}



procedure test3.XY.M3$System.Object$notnull(this: ref, x$in: ref where $IsNotNull(x$in, System.Object));
  requires $Heap[x$in, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $Heap[x$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == test3.XY && $Heap[this, $localinv] == $typeof(this);
  requires ($Heap[x$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[x$in, $ownerRef], $inv] <: $Heap[x$in, $ownerFrame]) || $Heap[$Heap[x$in, $ownerRef], $localinv] == $BaseClass($Heap[x$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[x$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[x$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerRef] != old($Heap)[x$in, $ownerRef] || old($Heap)[$o, $ownerFrame] != old($Heap)[x$in, $ownerFrame]) ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && !(($f == $ownerRef || $f == $ownerFrame) && old($Heap[$o, $ownerRef] == $Heap[x$in, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[x$in, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation test3.XY.M3$System.Object$notnull(this: ref, x$in: ref)
{
  var x: ref where $IsNotNull(x, System.Object), local1: ref where $Is(local1, test3.XY), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType;

  entry:
    assume $IsNotNull(this, test3.XY);
    assume $Heap[this, $allocated] == true;
    x := x$in;
    goto block15436;

  block15436:
    goto block15589;

  block15589:
    // ----- nop
    // ----- copy  ----- Strings.ssc(131,24)
    local1 := this;
    // ----- copy  ----- Strings.ssc(131,24)
    stack0o := local1;
    // ----- load token  ----- Strings.ssc(131,24)
    havoc stack1s;
    assume $IsTokenForType(stack1s, test3.XY);
    // ----- statically resolved GetTypeFromHandle call  ----- Strings.ssc(131,24)
    stack1o := TypeObject(test3.XY);
    // ----- classic unpack  ----- Strings.ssc(131,24)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == test3.XY && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block15606;

  block15606:
    // ----- store field  ----- Strings.ssc(132,9)
    assert this != null;
    assert !($Heap[this, $inv] <: test3.XY) || $Heap[this, $localinv] == System.Object;
    assert x == null || $Heap[x, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[x, $ownerRef] == this && $Heap[x, $ownerFrame] == test3.XY);
    assert x == null || !$IsImmutable($typeof(x));
    $Heap[this, test3.XY.o] := x;
    call $UpdateOwnersForRep(this, test3.XY, x);
    assume IsHeap($Heap);
    // ----- branch
    goto block15657;

  block15657:
    // ----- copy  ----- Strings.ssc(133,7)
    stack0o := local1;
    // ----- load token  ----- Strings.ssc(133,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, test3.XY);
    // ----- statically resolved GetTypeFromHandle call  ----- Strings.ssc(133,7)
    stack1o := TypeObject(test3.XY);
    // ----- classic pack  ----- Strings.ssc(133,7)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == test3.XY ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := test3.XY;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block15623;

  block15623:
    // ----- return
    return;

}



procedure test3.XY.M4$System.Object(this: ref, x$in: ref where $Is(x$in, System.Object));
  requires x$in == null || $Heap[x$in, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $Heap[x$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == test3.XY && $Heap[this, $localinv] == $typeof(this);
  requires x$in == null || (($Heap[x$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[x$in, $ownerRef], $inv] <: $Heap[x$in, $ownerFrame]) || $Heap[$Heap[x$in, $ownerRef], $localinv] == $BaseClass($Heap[x$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[x$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[x$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true && (x$in == null || old($Heap)[$o, $ownerRef] != old($Heap)[x$in, $ownerRef] || old($Heap)[$o, $ownerFrame] != old($Heap)[x$in, $ownerFrame]) ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && !(($f == $ownerRef || $f == $ownerFrame) && old($Heap[$o, $ownerRef] == $Heap[x$in, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[x$in, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation test3.XY.M4$System.Object(this: ref, x$in: ref)
{
  var x: ref where $Is(x, System.Object), stack0o: ref, stack0b: bool, temp0: exposeVersionType;

  entry:
    assume $IsNotNull(this, test3.XY);
    assume $Heap[this, $allocated] == true;
    x := x$in;
    goto block16133;

  block16133:
    goto block16150;

  block16150:
    // ----- is instance  ----- Strings.ssc(137,7)
    stack0o := $As(x, System.String);
    // ----- unary operator  ----- Strings.ssc(137,7)
    // ----- branch  ----- Strings.ssc(137,7)
    goto true16150to16184, false16150to16167;

  true16150to16184:
    assume stack0o == null;
    goto block16184;

  false16150to16167:
    assume stack0o != null;
    goto block16167;

  block16184:
    // ----- store field  ----- Strings.ssc(139,9)
    assert this != null;
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    assert x == null || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && $Heap[x, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[x, $ownerRef], $inv] <: $Heap[x, $ownerFrame]) || $Heap[$Heap[x, $ownerRef], $localinv] == $BaseClass($Heap[x, $ownerFrame]))) || ((!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[x, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerRef] == $Heap[x, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[x, $ownerFrame]);
    assert x == null || !$IsImmutable($typeof(x));
    $Heap[this, test3.XY.p] := x;
    call $UpdateOwnersForPeer(this, x);
    assume IsHeap($Heap);
    // ----- nop  ----- Strings.ssc(141,5)
    goto block16201;

  block16167:
    // ----- branch  ----- Strings.ssc(138,9)
    goto block16201;

  block16201:
    // ----- return  ----- Strings.ssc(141,5)
    return;

}



procedure test3.XY.N0$System.Object$notnull$System.Object$notnull(x$in: ref where $IsNotNull(x$in, System.Object), y$in: ref where $IsNotNull(y$in, System.Object));
  requires $Heap[x$in, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $Heap[x$in, $allocated] == true;
  requires $Heap[y$in, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $Heap[y$in, $allocated] == true;
  // user-declared preconditions
  requires ($Heap[x$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[x$in, $ownerRef], $inv] <: $Heap[x$in, $ownerFrame]) || $Heap[$Heap[x$in, $ownerRef], $localinv] == $BaseClass($Heap[x$in, $ownerFrame])) && $Heap[x$in, $inv] == System.Object && $Heap[x$in, $localinv] == $typeof(x$in);
  requires $Heap[y$in, $inv] <: System.Object && !(($Heap[y$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[y$in, $ownerRef], $inv] <: $Heap[y$in, $ownerFrame]) || $Heap[$Heap[y$in, $ownerRef], $localinv] == $BaseClass($Heap[y$in, $ownerFrame])) && $Heap[y$in, $inv] == $typeof(y$in) && $Heap[y$in, $localinv] == $typeof(y$in));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerRef] != old($Heap)[x$in, $ownerRef] || old($Heap)[$o, $ownerFrame] != old($Heap)[x$in, $ownerFrame]) && (old($Heap)[$o, $ownerRef] != old($Heap)[y$in, $ownerRef] || old($Heap)[$o, $ownerFrame] != old($Heap)[y$in, $ownerFrame]) ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && !(($f == $ownerRef || $f == $ownerFrame) && (old($Heap[$o, $ownerRef] == $Heap[x$in, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[x$in, $ownerFrame]) || old($Heap[$o, $ownerRef] == $Heap[y$in, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[y$in, $ownerFrame]))) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation test3.XY.N0$System.Object$notnull$System.Object$notnull(x$in: ref, y$in: ref)
{
  var x: ref where $IsNotNull(x, System.Object), y: ref where $IsNotNull(y, System.Object), local1: ref where $Is(local1, System.Object), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType, stack2o: ref;

  entry:
    x := x$in;
    y := y$in;
    goto block16745;

  block16745:
    goto block17068;

  block17068:
    // ----- nop
    // ----- copy  ----- Strings.ssc(148,24)
    local1 := x;
    // ----- copy  ----- Strings.ssc(148,24)
    stack0o := local1;
    // ----- load token  ----- Strings.ssc(148,24)
    havoc stack1s;
    assume $IsTokenForType(stack1s, System.Object);
    // ----- statically resolved GetTypeFromHandle call  ----- Strings.ssc(148,24)
    stack1o := TypeObject(System.Object);
    // ----- classic unpack  ----- Strings.ssc(148,24)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block17085;

  block17085:
    // ----- copy  ----- Strings.ssc(149,9)
    stack0o := x;
    // ----- copy  ----- Strings.ssc(149,9)
    stack1o := y;
    // ----- System.Object.GetType  ----- Strings.ssc(149,9)
    stack2o := TypeObject($typeof(y));
    // ----- Owner.Assign  ----- Strings.ssc(149,9)
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assert !$IsImmutable($typeof(stack0o));
    assert $typeof(stack1o) <: TypeName(stack2o);
    assert !($Heap[stack1o, $inv] <: TypeName(stack2o));
    call $SetOwner(stack0o, stack1o, TypeName(stack2o));
    // ----- branch
    goto block17136;

  block17136:
    // ----- copy  ----- Strings.ssc(150,7)
    stack0o := local1;
    // ----- load token  ----- Strings.ssc(150,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, System.Object);
    // ----- statically resolved GetTypeFromHandle call  ----- Strings.ssc(150,7)
    stack1o := TypeObject(System.Object);
    // ----- classic pack  ----- Strings.ssc(150,7)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    // ----- nop
    // ----- branch
    goto block17102;

  block17102:
    // ----- return
    return;

}



procedure test3.XY.N1$test3.XY$notnull$System.Object$notnull(x$in: ref where $IsNotNull(x$in, test3.XY), y$in: ref where $IsNotNull(y$in, System.Object));
  requires $Heap[x$in, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $Heap[x$in, $allocated] == true;
  free requires $Heap[y$in, $allocated] == true;
  requires ($Heap[x$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[x$in, $ownerRef], $inv] <: $Heap[x$in, $ownerFrame]) || $Heap[$Heap[x$in, $ownerRef], $localinv] == $BaseClass($Heap[x$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[x$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[x$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[y$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[y$in, $ownerRef], $inv] <: $Heap[y$in, $ownerFrame]) || $Heap[$Heap[y$in, $ownerRef], $localinv] == $BaseClass($Heap[y$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[y$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[y$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerRef] != old($Heap)[x$in, $ownerRef] || old($Heap)[$o, $ownerFrame] != old($Heap)[x$in, $ownerFrame]) ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && !(($f == $ownerRef || $f == $ownerFrame) && old($Heap[$o, $ownerRef] == $Heap[x$in, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[x$in, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation test3.XY.N1$test3.XY$notnull$System.Object$notnull(x$in: ref, y$in: ref)
{
  var x: ref where $IsNotNull(x, test3.XY), y: ref where $IsNotNull(y, System.Object), stack0o: ref, stack1o: ref;

  entry:
    x := x$in;
    y := y$in;
    goto block17748;

  block17748:
    goto block17901;

  block17901:
    // ----- nop
    // ----- copy  ----- Strings.ssc(155,7)
    stack0o := x;
    // ----- copy  ----- Strings.ssc(155,7)
    stack1o := y;
    // ----- Owner.AssignSame  ----- Strings.ssc(155,7)
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assert !$IsImmutable($typeof(stack0o));
    assert !$IsImmutable($typeof(stack1o));
    assert $Heap[stack1o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack1o, $ownerRef], $inv] <: $Heap[stack1o, $ownerFrame]) || $Heap[$Heap[stack1o, $ownerRef], $localinv] == $BaseClass($Heap[stack1o, $ownerFrame]);
    call $SetOwner(stack0o, $Heap[stack1o, $ownerRef], $Heap[stack1o, $ownerFrame]);
    // ----- return
    return;

}



procedure test3.XY.N2$System.Object$notnull$test3.XY$notnull(x$in: ref where $IsNotNull(x$in, System.Object), y$in: ref where $IsNotNull(y$in, test3.XY));
  requires $Heap[x$in, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $Heap[x$in, $allocated] == true;
  free requires $Heap[y$in, $allocated] == true;
  requires ($Heap[x$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[x$in, $ownerRef], $inv] <: $Heap[x$in, $ownerFrame]) || $Heap[$Heap[x$in, $ownerRef], $localinv] == $BaseClass($Heap[x$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[x$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[x$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[y$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[y$in, $ownerRef], $inv] <: $Heap[y$in, $ownerFrame]) || $Heap[$Heap[y$in, $ownerRef], $localinv] == $BaseClass($Heap[y$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[y$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[y$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerRef] != old($Heap)[x$in, $ownerRef] || old($Heap)[$o, $ownerFrame] != old($Heap)[x$in, $ownerFrame]) ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && !(($f == $ownerRef || $f == $ownerFrame) && old($Heap[$o, $ownerRef] == $Heap[x$in, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[x$in, $ownerFrame])) && old(true) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation test3.XY.N2$System.Object$notnull$test3.XY$notnull(x$in: ref, y$in: ref)
{
  var x: ref where $IsNotNull(x, System.Object), y: ref where $IsNotNull(y, test3.XY), stack0o: ref, stack1o: ref;

  entry:
    x := x$in;
    y := y$in;
    goto block18292;

  block18292:
    goto block18445;

  block18445:
    // ----- nop
    // ----- copy  ----- Strings.ssc(160,7)
    stack0o := x;
    // ----- copy  ----- Strings.ssc(160,7)
    stack1o := y;
    // ----- Owner.AssignSame  ----- Strings.ssc(160,7)
    assert $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assert !$IsImmutable($typeof(stack0o));
    assert !$IsImmutable($typeof(stack1o));
    assert $Heap[stack1o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack1o, $ownerRef], $inv] <: $Heap[stack1o, $ownerFrame]) || $Heap[$Heap[stack1o, $ownerRef], $localinv] == $BaseClass($Heap[stack1o, $ownerFrame]);
    call $SetOwner(stack0o, $Heap[stack1o, $ownerRef], $Heap[stack1o, $ownerFrame]);
    // ----- return
    return;

}



const $stringLiteral0: ref;

axiom (forall heap: [ref,<x>name]x :: { heap[$stringLiteral0, $allocated] } IsHeap(heap) ==> heap[$stringLiteral0, $allocated]) && $IsNotNull($stringLiteral0, System.String) && $StringLength($stringLiteral0) == 2;

axiom (forall heap: [ref,<x>name]x :: { heap[$stringLiteral0, $allocated] } IsHeap(heap) ==> heap[$stringLiteral0, $allocated]) && $IsNotNull($stringLiteral0, System.String) && #System.String.IsInterned$System.String$notnull($stringLiteral0) == $stringLiteral0;

const $stringLiteral1: ref;

axiom (forall heap: [ref,<x>name]x :: { heap[$stringLiteral1, $allocated] } IsHeap(heap) ==> heap[$stringLiteral1, $allocated]) && $IsNotNull($stringLiteral1, System.String) && $StringLength($stringLiteral1) == 3;

axiom (forall heap: [ref,<x>name]x :: { heap[$stringLiteral1, $allocated] } IsHeap(heap) ==> heap[$stringLiteral1, $allocated]) && $IsNotNull($stringLiteral1, System.String) && #System.String.IsInterned$System.String$notnull($stringLiteral1) == $stringLiteral1;

const $stringLiteral3: ref;

axiom (forall heap: [ref,<x>name]x :: { heap[$stringLiteral3, $allocated] } IsHeap(heap) ==> heap[$stringLiteral3, $allocated]) && $IsNotNull($stringLiteral3, System.String) && $StringLength($stringLiteral3) == 1;

axiom (forall heap: [ref,<x>name]x :: { heap[$stringLiteral3, $allocated] } IsHeap(heap) ==> heap[$stringLiteral3, $allocated]) && $IsNotNull($stringLiteral3, System.String) && #System.String.IsInterned$System.String$notnull($stringLiteral3) == $stringLiteral3;

const $stringLiteral8: ref;

axiom (forall heap: [ref,<x>name]x :: { heap[$stringLiteral8, $allocated] } IsHeap(heap) ==> heap[$stringLiteral8, $allocated]) && $IsNotNull($stringLiteral8, System.String) && $StringLength($stringLiteral8) == 3;

axiom (forall heap: [ref,<x>name]x :: { heap[$stringLiteral8, $allocated] } IsHeap(heap) ==> heap[$stringLiteral8, $allocated]) && $IsNotNull($stringLiteral8, System.String) && #System.String.IsInterned$System.String$notnull($stringLiteral8) == $stringLiteral8;
