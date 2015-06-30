// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: -nologo /prover:blank /print:boogie_tmp.@TIME@.bpl /proverLog:boogie_tmp.@TIME@.simplify /proverMatchDepth:5 PeerFields.dll

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

const PeerFields.s: <ref>name;

const PeerFields.p: <ref>name;

const PeerFields.a: <ref>name;

const Parent.ch: <ref>name;

const Child.sibling: <ref>name;

const System.Reflection.IReflect: name;

const System.IComparable`1...System.String: name;

const Parent: name;

const Child: name;

const System.Collections.IEnumerable: name;

const System.IConvertible: name;

const System.Reflection.ICustomAttributeProvider: name;

const System.Reflection.MemberInfo: name;

const System.ICloneable: name;

const System.Collections.Generic.IEnumerable`1...System.Char: name;

const System.Runtime.InteropServices._MemberInfo: name;

const System.IComparable: name;

const PeerFields: name;

const System.Runtime.InteropServices._Type: name;

const System.IEquatable`1...System.String: name;

axiom !IsStaticField(PeerFields.p);

axiom IsDirectlyModifiableField(PeerFields.p);

axiom AsPeerField(PeerFields.p) == PeerFields.p;

axiom DeclType(PeerFields.p) == PeerFields;

axiom AsRefField(PeerFields.p, PeerFields) == PeerFields.p;

axiom !IsStaticField(PeerFields.s);

axiom IsDirectlyModifiableField(PeerFields.s);

axiom AsPeerField(PeerFields.s) == PeerFields.s;

axiom DeclType(PeerFields.s) == PeerFields;

axiom AsRefField(PeerFields.s, System.Object) == PeerFields.s;

axiom !IsStaticField(PeerFields.a);

axiom IsDirectlyModifiableField(PeerFields.a);

axiom AsPeerField(PeerFields.a) == PeerFields.a;

axiom DeclType(PeerFields.a) == PeerFields;

axiom AsNonNullRefField(PeerFields.a, ValueArray(System.Int32, 1)) == PeerFields.a;

axiom !IsStaticField(Parent.ch);

axiom IsDirectlyModifiableField(Parent.ch);

axiom AsRepField(Parent.ch, Parent) == Parent.ch;

axiom DeclType(Parent.ch) == Parent;

axiom AsRefField(Parent.ch, Child) == Parent.ch;

axiom !IsStaticField(Child.sibling);

axiom IsDirectlyModifiableField(Child.sibling);

axiom AsPeerField(Child.sibling) == Child.sibling;

axiom DeclType(Child.sibling) == Child;

axiom AsRefField(Child.sibling, Child) == Child.sibling;

axiom PeerFields <: PeerFields;

axiom $BaseClass(PeerFields) == System.Object;

axiom PeerFields <: $BaseClass(PeerFields) && AsDirectSubClass(PeerFields, $BaseClass(PeerFields)) == PeerFields;

axiom !$IsImmutable(PeerFields) && $AsMutable(PeerFields) == PeerFields;

axiom (forall $U: name :: { $U <: PeerFields } $U <: PeerFields ==> $U == PeerFields);

procedure PeerFields..ctor$System.Int32(this: ref, x$in: int where InRange(x$in, System.Int32));
  free requires true;
  // user-declared preconditions
  requires 0 <= x$in;
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == PeerFields && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(PeerFields <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation PeerFields..ctor$System.Int32(this: ref, x$in: int)
{
  var x: int where InRange(x, System.Int32), stack0i: int, stack0b: bool, stack50000o: ref, stack0o: ref, temp0: exposeVersionType, temp1: exposeVersionType;

  entry:
    assume $IsNotNull(this, PeerFields);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    x := x$in;
    assume $Heap[this, PeerFields.p] == null;
    assume $Heap[this, PeerFields.s] == null;
    goto block1615;

  block1615:
    goto block1717;

  block1717:
    // ----- nop
    // ----- load constant 10  ----- PeerFields.ssc(13,5)
    stack0i := 10;
    // ----- binary operator  ----- PeerFields.ssc(13,5)
    // ----- branch  ----- PeerFields.ssc(13,5)
    goto true1717to1751, false1717to1734;

  true1717to1751:
    assume x >= stack0i;
    goto block1751;

  false1717to1734:
    assume x < stack0i;
    goto block1734;

  block1751:
    // ----- copy  ----- PeerFields.ssc(16,5)
    stack0i := x;
    // ----- new array  ----- PeerFields.ssc(16,5)
    assert 0 <= stack0i;
    havoc stack0o;
    assume $Heap[stack0o, $allocated] == false && $Length(stack0o) == stack0i;
    assume $IsNotNull(stack0o, ValueArray(System.Int32, 1));
    assume $Heap[stack0o, $ownerRef] == stack0o && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder;
    assume $Heap[stack0o, $inv] == ValueArray(System.Int32, 1) && $Heap[stack0o, $localinv] == ValueArray(System.Int32, 1) && ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]));
    assume (forall $i: int :: cast(ValueArrayGet($Heap[stack0o, $elements], $i),int) == 0);
    $Heap[stack0o, $allocated] := true;
    assume IsHeap($Heap);
    // ----- store field  ----- PeerFields.ssc(16,5)
    assert this != null;
    havoc temp1;
    $Heap[this, $exposeVersion] := temp1;
    assert ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) || ((!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerRef] == $Heap[stack0o, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[stack0o, $ownerFrame]);
    $Heap[this, PeerFields.a] := stack0o;
    call $UpdateOwnersForPeer(this, stack0o);
    assume IsHeap($Heap);
    // ----- call  ----- PeerFields.ssc(17,5)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == PeerFields ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := PeerFields;
    assume IsHeap($Heap);
    return;

  block1734:
    // ----- load constant 1  ----- PeerFields.ssc(14,7)
    stack0i := 1;
    // ----- binary operator  ----- PeerFields.ssc(14,7)
    stack0i := x + stack0i;
    // ----- new object  ----- PeerFields.ssc(14,7)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == PeerFields;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- PeerFields.ssc(14,7)
    assert stack50000o != null;
    call PeerFields..ctor$System.Int32(stack50000o, stack0i);
    // ----- copy  ----- PeerFields.ssc(14,7)
    stack0o := stack50000o;
    // ----- store field  ----- PeerFields.ssc(14,7)
    assert this != null;
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    assert stack0o == null || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) || ((!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerRef] == $Heap[stack0o, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[stack0o, $ownerFrame]);
    $Heap[this, PeerFields.p] := stack0o;
    call $UpdateOwnersForPeer(this, stack0o);
    assume IsHeap($Heap);
    goto block1751;

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



procedure PeerFields.Ouch(this: ref);
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



implementation PeerFields.Ouch(this: ref)
{
  var local0: ref where $Is(local0, PeerFields), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType, temp1: exposeVersionType;

  entry:
    assume $IsNotNull(this, PeerFields);
    assume $Heap[this, $allocated] == true;
    goto block2516;

  block2516:
    goto block2584;

  block2584:
    // ----- copy  ----- PeerFields.ssc(21,22)
    local0 := this;
    // ----- copy  ----- PeerFields.ssc(21,22)
    stack0o := local0;
    // ----- load token  ----- PeerFields.ssc(21,22)
    havoc stack1s;
    assume $IsTokenForType(stack1s, PeerFields);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(21,22)
    stack1o := TypeObject(PeerFields);
    // ----- classic unpack  ----- PeerFields.ssc(21,22)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == PeerFields && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block2601;

  block2601:
    // ----- load constant "hello"  ----- PeerFields.ssc(22,7)
    stack0o := $stringLiteral0;
    // ----- store field  ----- PeerFields.ssc(22,7)
    assert this != null;
    havoc temp1;
    $Heap[this, $exposeVersion] := temp1;
    assert stack0o == null || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) || ((!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerRef] == $Heap[stack0o, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[stack0o, $ownerFrame]);
    assert stack0o == null || !$IsImmutable($typeof(stack0o));
    $Heap[this, PeerFields.s] := stack0o;
    call $UpdateOwnersForPeer(this, stack0o);
    assume IsHeap($Heap);
    // ----- branch
    goto block2652;

  block2652:
    // ----- copy  ----- PeerFields.ssc(23,5)
    stack0o := local0;
    // ----- load token  ----- PeerFields.ssc(23,5)
    havoc stack1s;
    assume $IsTokenForType(stack1s, PeerFields);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(23,5)
    stack1o := TypeObject(PeerFields);
    // ----- classic pack  ----- PeerFields.ssc(23,5)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == PeerFields ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := PeerFields;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block2618;

  block2618:
    // ----- return  ----- PeerFields.ssc(24,3)
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

procedure PeerFields.M$System.Int32(this: ref, x$in: int where InRange(x$in, System.Int32));
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



implementation PeerFields.M$System.Int32(this: ref, x$in: int)
{
  var x: int where InRange(x, System.Int32), stack0i: int, stack0b: bool, stack0o: ref, stack1o: ref, stack1i: int;

  entry:
    assume $IsNotNull(this, PeerFields);
    assume $Heap[this, $allocated] == true;
    x := x$in;
    goto block3094;

  block3094:
    goto block3111;

  block3111:
    // ----- load constant 10  ----- PeerFields.ssc(28,5)
    stack0i := 10;
    // ----- binary operator  ----- PeerFields.ssc(28,5)
    // ----- branch  ----- PeerFields.ssc(28,5)
    goto true3111to3162, false3111to3128;

  true3111to3162:
    assume x >= stack0i;
    goto block3162;

  false3111to3128:
    assume x < stack0i;
    goto block3128;

  block3162:
    // ----- return  ----- PeerFields.ssc(38,3)
    return;

  block3128:
    // ----- load constant 1  ----- PeerFields.ssc(29,7)
    stack0i := 1;
    // ----- binary operator  ----- PeerFields.ssc(29,7)
    stack0i := x + stack0i;
    // ----- call  ----- PeerFields.ssc(29,7)
    assert this != null;
    call PeerFields.M$System.Int32(this, stack0i);
    // ----- copy  ----- PeerFields.ssc(30,7)
    stack0i := x;
    // ----- call  ----- PeerFields.ssc(30,7)
    assert this != null;
    call PeerFields.N$System.Int32(this, stack0i);
    // ----- copy  ----- PeerFields.ssc(31,7)
    stack0i := x;
    // ----- call  ----- PeerFields.ssc(31,7)
    assert this != null;
    call PeerFields.P$System.Int32$.Virtual.$(this, stack0i);
    // ----- load field  ----- PeerFields.ssc(32,7)
    assert this != null;
    stack0o := $Heap[this, PeerFields.p];
    stack1o := null;
    // ----- binary operator  ----- PeerFields.ssc(32,7)
    // ----- branch  ----- PeerFields.ssc(32,7)
    goto true3128to3162, false3128to3145;

  true3128to3162:
    assume stack0o == stack1o;
    goto block3162;

  false3128to3145:
    assume stack0o != stack1o;
    goto block3145;

  block3145:
    // ----- load field  ----- PeerFields.ssc(33,9)
    assert this != null;
    stack0o := $Heap[this, PeerFields.p];
    // ----- load constant 1  ----- PeerFields.ssc(33,9)
    stack1i := 1;
    // ----- binary operator  ----- PeerFields.ssc(33,9)
    stack1i := x + stack1i;
    // ----- call  ----- PeerFields.ssc(33,9)
    assert stack0o != null;
    call PeerFields.M$System.Int32(stack0o, stack1i);
    // ----- load field  ----- PeerFields.ssc(34,9)
    assert this != null;
    stack0o := $Heap[this, PeerFields.p];
    // ----- copy  ----- PeerFields.ssc(34,9)
    stack1i := x;
    // ----- call  ----- PeerFields.ssc(34,9)
    assert stack0o != null;
    call PeerFields.N$System.Int32(stack0o, stack1i);
    // ----- load field  ----- PeerFields.ssc(35,9)
    assert this != null;
    stack0o := $Heap[this, PeerFields.p];
    // ----- copy  ----- PeerFields.ssc(35,9)
    stack1i := x;
    // ----- call  ----- PeerFields.ssc(35,9)
    assert stack0o != null;
    call PeerFields.P$System.Int32$.Virtual.$(stack0o, stack1i);
    goto block3162;

}



procedure PeerFields.N$System.Int32(this: ref, x$in: int where InRange(x$in, System.Int32));
  free requires true;
  // user-declared preconditions
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == $typeof(this) && $Heap[this, $localinv] == $typeof(this);
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



procedure PeerFields.P$System.Int32$.Virtual.$(this: ref, x$in: int where InRange(x$in, System.Int32));
  free requires true;
  // target object is consistent
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == $typeof(this) && $Heap[this, $localinv] == $typeof(this);
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



implementation PeerFields.N$System.Int32(this: ref, x$in: int)
{
  var x: int where InRange(x, System.Int32), stack0i: int, stack0b: bool, stack0o: ref, stack1o: ref, stack1i: int;

  entry:
    assume $IsNotNull(this, PeerFields);
    assume $Heap[this, $allocated] == true;
    x := x$in;
    goto block3859;

  block3859:
    goto block3961;

  block3961:
    // ----- nop
    // ----- load constant 10  ----- PeerFields.ssc(44,5)
    stack0i := 10;
    // ----- binary operator  ----- PeerFields.ssc(44,5)
    // ----- branch  ----- PeerFields.ssc(44,5)
    goto true3961to4012, false3961to3978;

  true3961to4012:
    assume x >= stack0i;
    goto block4012;

  false3961to3978:
    assume x < stack0i;
    goto block3978;

  block4012:
    // ----- return
    return;

  block3978:
    // ----- load field
    assert this != null;
    stack0o := $Heap[this, PeerFields.p];
    stack1o := null;
    // ----- binary operator
    // ----- branch
    goto true3978to4012, false3978to3995;

  true3978to4012:
    assume stack0o == stack1o;
    goto block4012;

  false3978to3995:
    assume stack0o != stack1o;
    goto block3995;

  block3995:
    // ----- load field  ----- PeerFields.ssc(45,7)
    assert this != null;
    stack0o := $Heap[this, PeerFields.p];
    // ----- load constant 1  ----- PeerFields.ssc(45,7)
    stack1i := 1;
    // ----- binary operator  ----- PeerFields.ssc(45,7)
    stack1i := x + stack1i;
    // ----- call  ----- PeerFields.ssc(45,7)
    assert stack0o != null;
    call PeerFields.N$System.Int32(stack0o, stack1i);
    goto block4012;

}



procedure PeerFields.P$System.Int32(this: ref, x$in: int where InRange(x$in, System.Int32));
  free requires true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == PeerFields && $Heap[this, $localinv] == $typeof(this);
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



implementation PeerFields.P$System.Int32(this: ref, x$in: int)
{
  var x: int where InRange(x, System.Int32), stack0i: int;

  entry:
    assume $IsNotNull(this, PeerFields);
    assume $Heap[this, $allocated] == true;
    x := x$in;
    goto block4403;

  block4403:
    goto block4420;

  block4420:
    // ----- copy  ----- PeerFields.ssc(51,5)
    stack0i := x;
    // ----- call  ----- PeerFields.ssc(51,5)
    assert this != null;
    call PeerFields.M$System.Int32(this, stack0i);
    // ----- return  ----- PeerFields.ssc(52,3)
    return;

}



procedure PeerFields.Q$System.Int32(this: ref, x$in: int where InRange(x$in, System.Int32));
  free requires true;
  // user-declared preconditions
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == $typeof(this) && $Heap[this, $localinv] == $typeof(this);
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



implementation PeerFields.Q$System.Int32(this: ref, x$in: int)
{
  var x: int where InRange(x, System.Int32), stack0i: int;

  entry:
    assume $IsNotNull(this, PeerFields);
    assume $Heap[this, $allocated] == true;
    x := x$in;
    goto block4692;

  block4692:
    goto block4794;

  block4794:
    // ----- nop
    // ----- copy  ----- PeerFields.ssc(58,5)
    stack0i := x;
    // ----- call  ----- PeerFields.ssc(58,5)
    assert this != null;
    call PeerFields.M$System.Int32(this, stack0i);
    // ----- return
    return;

}



procedure PeerFields.R$System.Int32(this: ref, x$in: int where InRange(x$in, System.Int32));
  free requires true;
  // user-declared preconditions
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == $typeof(this) && $Heap[this, $localinv] == $typeof(this);
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



implementation PeerFields.R$System.Int32(this: ref, x$in: int)
{
  var x: int where InRange(x, System.Int32), stack0o: ref, stack1o: ref, stack0b: bool, stack1i: int;

  entry:
    assume $IsNotNull(this, PeerFields);
    assume $Heap[this, $allocated] == true;
    x := x$in;
    goto block5151;

  block5151:
    goto block5253;

  block5253:
    // ----- nop
    // ----- load field  ----- PeerFields.ssc(65,5)
    assert this != null;
    stack0o := $Heap[this, PeerFields.p];
    stack1o := null;
    // ----- binary operator  ----- PeerFields.ssc(65,5)
    // ----- branch  ----- PeerFields.ssc(65,5)
    goto true5253to5287, false5253to5270;

  true5253to5287:
    assume stack0o == stack1o;
    goto block5287;

  false5253to5270:
    assume stack0o != stack1o;
    goto block5270;

  block5287:
    // ----- return
    return;

  block5270:
    // ----- load field  ----- PeerFields.ssc(66,7)
    assert this != null;
    stack0o := $Heap[this, PeerFields.p];
    // ----- copy  ----- PeerFields.ssc(66,7)
    stack1i := x;
    // ----- call  ----- PeerFields.ssc(66,7)
    assert stack0o != null;
    call PeerFields.M$System.Int32(stack0o, stack1i);
    goto block5287;

}



procedure PeerFields.S$System.Int32(this: ref, x$in: int where InRange(x$in, System.Int32));
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



implementation PeerFields.S$System.Int32(this: ref, x$in: int)
{
  var x: int where InRange(x, System.Int32), stack0o: ref, stack1o: ref, stack0b: bool, stack1i: int, local0: ref where $Is(local0, PeerFields), stack1s: struct, temp0: exposeVersionType;

  entry:
    assume $IsNotNull(this, PeerFields);
    assume $Heap[this, $allocated] == true;
    x := x$in;
    goto block5695;

  block5695:
    goto block5763;

  block5763:
    // ----- load field  ----- PeerFields.ssc(72,5)
    assert this != null;
    stack0o := $Heap[this, PeerFields.p];
    stack1o := null;
    // ----- binary operator  ----- PeerFields.ssc(72,5)
    // ----- branch  ----- PeerFields.ssc(72,5)
    goto true5763to5814, false5763to5780;

  true5763to5814:
    assume stack0o == stack1o;
    goto block5814;

  false5763to5780:
    assume stack0o != stack1o;
    goto block5780;

  block5814:
    // ----- return  ----- PeerFields.ssc(78,3)
    return;

  block5780:
    // ----- load field  ----- PeerFields.ssc(73,7)
    assert this != null;
    stack0o := $Heap[this, PeerFields.p];
    // ----- copy  ----- PeerFields.ssc(73,7)
    stack1i := x;
    // ----- call  ----- PeerFields.ssc(73,7)
    assert stack0o != null;
    call PeerFields.M$System.Int32(stack0o, stack1i);
    // ----- copy  ----- PeerFields.ssc(74,24)
    local0 := this;
    // ----- copy  ----- PeerFields.ssc(74,24)
    stack0o := local0;
    // ----- load token  ----- PeerFields.ssc(74,24)
    havoc stack1s;
    assume $IsTokenForType(stack1s, PeerFields);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(74,24)
    stack1o := TypeObject(PeerFields);
    // ----- classic unpack  ----- PeerFields.ssc(74,24)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == PeerFields && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block5797;

  block5797:
    // ----- load field  ----- PeerFields.ssc(75,9)
    assert this != null;
    stack0o := $Heap[this, PeerFields.p];
    // ----- copy  ----- PeerFields.ssc(75,9)
    stack1i := x;
    // ----- call  ----- PeerFields.ssc(75,9)
    assert stack0o != null;
    call PeerFields.M$System.Int32(stack0o, stack1i);
    // ----- branch
    goto block5848;

  block5848:
    // ----- copy  ----- PeerFields.ssc(76,7)
    stack0o := local0;
    // ----- load token  ----- PeerFields.ssc(76,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, PeerFields);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(76,7)
    stack1o := TypeObject(PeerFields);
    // ----- classic pack  ----- PeerFields.ssc(76,7)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == PeerFields ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := PeerFields;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block5814;

}



procedure PeerFields.Assign0(this: ref);
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



implementation PeerFields.Assign0(this: ref)
{
  var local0: ref where $Is(local0, PeerFields), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType, stack0i: int, stack50000o: ref, temp1: exposeVersionType;

  entry:
    assume $IsNotNull(this, PeerFields);
    assume $Heap[this, $allocated] == true;
    goto block6443;

  block6443:
    goto block6511;

  block6511:
    // ----- copy  ----- PeerFields.ssc(82,22)
    local0 := this;
    // ----- copy  ----- PeerFields.ssc(82,22)
    stack0o := local0;
    // ----- load token  ----- PeerFields.ssc(82,22)
    havoc stack1s;
    assume $IsTokenForType(stack1s, PeerFields);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(82,22)
    stack1o := TypeObject(PeerFields);
    // ----- classic unpack  ----- PeerFields.ssc(82,22)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == PeerFields && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block6528;

  block6528:
    // ----- load constant 8  ----- PeerFields.ssc(83,7)
    stack0i := 8;
    // ----- new object  ----- PeerFields.ssc(83,7)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == PeerFields;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- PeerFields.ssc(83,7)
    assert stack50000o != null;
    call PeerFields..ctor$System.Int32(stack50000o, stack0i);
    // ----- copy  ----- PeerFields.ssc(83,7)
    stack0o := stack50000o;
    // ----- store field  ----- PeerFields.ssc(83,7)
    assert this != null;
    havoc temp1;
    $Heap[this, $exposeVersion] := temp1;
    assert stack0o == null || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) || ((!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerRef] == $Heap[stack0o, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[stack0o, $ownerFrame]);
    $Heap[this, PeerFields.p] := stack0o;
    call $UpdateOwnersForPeer(this, stack0o);
    assume IsHeap($Heap);
    // ----- branch
    goto block6579;

  block6579:
    // ----- copy  ----- PeerFields.ssc(84,5)
    stack0o := local0;
    // ----- load token  ----- PeerFields.ssc(84,5)
    havoc stack1s;
    assume $IsTokenForType(stack1s, PeerFields);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(84,5)
    stack1o := TypeObject(PeerFields);
    // ----- classic pack  ----- PeerFields.ssc(84,5)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == PeerFields ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := PeerFields;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block6545;

  block6545:
    // ----- return  ----- PeerFields.ssc(85,3)
    return;

}



procedure PeerFields.Assign1$PeerFields(this: ref, p$in: ref where $Is(p$in, PeerFields));
  requires p$in == null || $Heap[p$in, $ownerFrame] == $PeerGroupPlaceholder;
  free requires $Heap[p$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires p$in == null || (($Heap[p$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[p$in, $ownerRef], $inv] <: $Heap[p$in, $ownerFrame]) || $Heap[$Heap[p$in, $ownerRef], $localinv] == $BaseClass($Heap[p$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[p$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[p$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true && (p$in == null || old($Heap)[$o, $ownerRef] != old($Heap)[p$in, $ownerRef] || old($Heap)[$o, $ownerFrame] != old($Heap)[p$in, $ownerFrame]) ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && !(($f == $ownerRef || $f == $ownerFrame) && old($Heap[$o, $ownerRef] == $Heap[p$in, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[p$in, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation PeerFields.Assign1$PeerFields(this: ref, p$in: ref)
{
  var p: ref where $Is(p, PeerFields), local0: ref where $Is(local0, PeerFields), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType, temp1: exposeVersionType;

  entry:
    assume $IsNotNull(this, PeerFields);
    assume $Heap[this, $allocated] == true;
    p := p$in;
    goto block7089;

  block7089:
    goto block7157;

  block7157:
    // ----- copy  ----- PeerFields.ssc(89,22)
    local0 := this;
    // ----- copy  ----- PeerFields.ssc(89,22)
    stack0o := local0;
    // ----- load token  ----- PeerFields.ssc(89,22)
    havoc stack1s;
    assume $IsTokenForType(stack1s, PeerFields);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(89,22)
    stack1o := TypeObject(PeerFields);
    // ----- classic unpack  ----- PeerFields.ssc(89,22)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == PeerFields && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block7174;

  block7174:
    // ----- store field  ----- PeerFields.ssc(90,7)
    assert this != null;
    havoc temp1;
    $Heap[this, $exposeVersion] := temp1;
    assert p == null || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && $Heap[p, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[p, $ownerRef], $inv] <: $Heap[p, $ownerFrame]) || $Heap[$Heap[p, $ownerRef], $localinv] == $BaseClass($Heap[p, $ownerFrame]))) || ((!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[p, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerRef] == $Heap[p, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[p, $ownerFrame]);
    $Heap[this, PeerFields.p] := p;
    call $UpdateOwnersForPeer(this, p);
    assume IsHeap($Heap);
    // ----- branch
    goto block7225;

  block7225:
    // ----- copy  ----- PeerFields.ssc(91,5)
    stack0o := local0;
    // ----- load token  ----- PeerFields.ssc(91,5)
    havoc stack1s;
    assume $IsTokenForType(stack1s, PeerFields);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(91,5)
    stack1o := TypeObject(PeerFields);
    // ----- classic pack  ----- PeerFields.ssc(91,5)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == PeerFields ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := PeerFields;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block7191;

  block7191:
    // ----- return  ----- PeerFields.ssc(92,3)
    return;

}



procedure PeerFields.Assign2$PeerFields(this: ref, p$in: ref where $Is(p$in, PeerFields));
  free requires $Heap[p$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires p$in == null || (($Heap[p$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[p$in, $ownerRef], $inv] <: $Heap[p$in, $ownerFrame]) || $Heap[$Heap[p$in, $ownerRef], $localinv] == $BaseClass($Heap[p$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[p$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[p$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
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



implementation PeerFields.Assign2$PeerFields(this: ref, p$in: ref)
{
  var p: ref where $Is(p, PeerFields), local0: ref where $Is(local0, PeerFields), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType, temp1: exposeVersionType;

  entry:
    assume $IsNotNull(this, PeerFields);
    assume $Heap[this, $allocated] == true;
    p := p$in;
    goto block7667;

  block7667:
    goto block7735;

  block7735:
    // ----- copy  ----- PeerFields.ssc(96,22)
    local0 := this;
    // ----- copy  ----- PeerFields.ssc(96,22)
    stack0o := local0;
    // ----- load token  ----- PeerFields.ssc(96,22)
    havoc stack1s;
    assume $IsTokenForType(stack1s, PeerFields);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(96,22)
    stack1o := TypeObject(PeerFields);
    // ----- classic unpack  ----- PeerFields.ssc(96,22)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == PeerFields && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block7752;

  block7752:
    // ----- store field  ----- PeerFields.ssc(97,7)
    assert this != null;
    havoc temp1;
    $Heap[this, $exposeVersion] := temp1;
    assert p == null || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && $Heap[p, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[p, $ownerRef], $inv] <: $Heap[p, $ownerFrame]) || $Heap[$Heap[p, $ownerRef], $localinv] == $BaseClass($Heap[p, $ownerFrame]))) || ((!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[p, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerRef] == $Heap[p, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[p, $ownerFrame]);
    $Heap[this, PeerFields.p] := p;
    call $UpdateOwnersForPeer(this, p);
    assume IsHeap($Heap);
    // ----- branch
    goto block7803;

  block7803:
    // ----- copy  ----- PeerFields.ssc(98,5)
    stack0o := local0;
    // ----- load token  ----- PeerFields.ssc(98,5)
    havoc stack1s;
    assume $IsTokenForType(stack1s, PeerFields);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(98,5)
    stack1o := TypeObject(PeerFields);
    // ----- classic pack  ----- PeerFields.ssc(98,5)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == PeerFields ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := PeerFields;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block7769;

  block7769:
    // ----- return  ----- PeerFields.ssc(99,3)
    return;

}



procedure PeerFields.Assign3(this: ref);
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



implementation PeerFields.Assign3(this: ref)
{
  var stack0i: int, stack50000o: ref, stack0o: ref, p: ref where $Is(p, PeerFields), local1: ref where $Is(local1, PeerFields), stack1s: struct, stack1o: ref, temp0: exposeVersionType, temp1: exposeVersionType;

  entry:
    assume $IsNotNull(this, PeerFields);
    assume $Heap[this, $allocated] == true;
    goto block8245;

  block8245:
    goto block8313;

  block8313:
    // ----- load constant 5  ----- PeerFields.ssc(104,5)
    stack0i := 5;
    // ----- new object  ----- PeerFields.ssc(104,5)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == PeerFields;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- PeerFields.ssc(104,5)
    assert stack50000o != null;
    call PeerFields..ctor$System.Int32(stack50000o, stack0i);
    // ----- copy  ----- PeerFields.ssc(104,5)
    stack0o := stack50000o;
    // ----- copy  ----- PeerFields.ssc(104,5)
    p := stack0o;
    // ----- copy  ----- PeerFields.ssc(105,22)
    local1 := p;
    // ----- copy  ----- PeerFields.ssc(105,22)
    stack0o := local1;
    // ----- load token  ----- PeerFields.ssc(105,22)
    havoc stack1s;
    assume $IsTokenForType(stack1s, PeerFields);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(105,22)
    stack1o := TypeObject(PeerFields);
    // ----- classic unpack  ----- PeerFields.ssc(105,22)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == PeerFields && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block8330;

  block8330:
    // ----- store field  ----- PeerFields.ssc(106,7)
    assert p != null;
    havoc temp1;
    $Heap[p, $exposeVersion] := temp1;
    assert this == null || ($Heap[p, $ownerFrame] == $PeerGroupPlaceholder && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[p, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame]))) || ((!($Heap[$Heap[p, $ownerRef], $inv] <: $Heap[p, $ownerFrame]) || $Heap[$Heap[p, $ownerRef], $localinv] == $BaseClass($Heap[p, $ownerFrame])) && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[p, $ownerRef] == $Heap[this, $ownerRef] && $Heap[p, $ownerFrame] == $Heap[this, $ownerFrame]);
    $Heap[p, PeerFields.p] := this;
    call $UpdateOwnersForPeer(p, this);
    assume IsHeap($Heap);
    // ----- branch
    goto block8381;

  block8381:
    // ----- copy  ----- PeerFields.ssc(107,5)
    stack0o := local1;
    // ----- load token  ----- PeerFields.ssc(107,5)
    havoc stack1s;
    assume $IsTokenForType(stack1s, PeerFields);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(107,5)
    stack1o := TypeObject(PeerFields);
    // ----- classic pack  ----- PeerFields.ssc(107,5)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == PeerFields ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := PeerFields;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block8347;

  block8347:
    // ----- return  ----- PeerFields.ssc(108,3)
    return;

}



procedure PeerFields.Assign4(this: ref);
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



implementation PeerFields.Assign4(this: ref)
{
  var stack0i: int, stack50000o: ref, stack0o: ref, temp0: exposeVersionType;

  entry:
    assume $IsNotNull(this, PeerFields);
    assume $Heap[this, $allocated] == true;
    goto block8840;

  block8840:
    goto block8857;

  block8857:
    // ----- load constant 2  ----- PeerFields.ssc(113,5)
    stack0i := 2;
    // ----- new object  ----- PeerFields.ssc(113,5)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == PeerFields;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- PeerFields.ssc(113,5)
    assert stack50000o != null;
    call PeerFields..ctor$System.Int32(stack50000o, stack0i);
    // ----- copy  ----- PeerFields.ssc(113,5)
    stack0o := stack50000o;
    // ----- store field  ----- PeerFields.ssc(113,5)
    assert this != null;
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    assert stack0o == null || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) || ((!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerRef] == $Heap[stack0o, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[stack0o, $ownerFrame]);
    $Heap[this, PeerFields.p] := stack0o;
    call $UpdateOwnersForPeer(this, stack0o);
    assume IsHeap($Heap);
    // ----- return  ----- PeerFields.ssc(114,3)
    return;

}



procedure PeerFields.Assign5(this: ref);
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



implementation PeerFields.Assign5(this: ref)
{
  var stack0o: ref, temp0: exposeVersionType;

  entry:
    assume $IsNotNull(this, PeerFields);
    assume $Heap[this, $allocated] == true;
    goto block9095;

  block9095:
    goto block9112;

  block9112:
    stack0o := null;
    // ----- store field  ----- PeerFields.ssc(122,5)
    assert this != null;
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    assert stack0o == null || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) || ((!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerRef] == $Heap[stack0o, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[stack0o, $ownerFrame]);
    $Heap[this, PeerFields.p] := stack0o;
    call $UpdateOwnersForPeer(this, stack0o);
    assume IsHeap($Heap);
    // ----- return  ----- PeerFields.ssc(123,3)
    return;

}



axiom Parent <: Parent;

axiom $BaseClass(Parent) == System.Object;

axiom Parent <: $BaseClass(Parent) && AsDirectSubClass(Parent, $BaseClass(Parent)) == Parent;

axiom !$IsImmutable(Parent) && $AsMutable(Parent) == Parent;

procedure Parent.M(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Parent && $Heap[this, $localinv] == $typeof(this);
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



implementation Parent.M(this: ref)
{
  var stack0i: int, stack50000o: ref, stack0o: ref, c: ref where $Is(c, Child), local1: ref where $Is(local1, Parent), stack1s: struct, stack1o: ref, temp0: exposeVersionType;

  entry:
    assume $IsNotNull(this, Parent);
    assume $Heap[this, $allocated] == true;
    goto block9367;

  block9367:
    goto block9435;

  block9435:
    // ----- load constant 3  ----- PeerFields.ssc(130,5)
    stack0i := 3;
    // ----- new object  ----- PeerFields.ssc(130,5)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Child;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- PeerFields.ssc(130,5)
    assert stack50000o != null;
    call Child..ctor$System.Int32(stack50000o, stack0i);
    // ----- copy  ----- PeerFields.ssc(130,5)
    stack0o := stack50000o;
    // ----- copy  ----- PeerFields.ssc(130,5)
    c := stack0o;
    // ----- copy  ----- PeerFields.ssc(131,22)
    local1 := this;
    // ----- copy  ----- PeerFields.ssc(131,22)
    stack0o := local1;
    // ----- load token  ----- PeerFields.ssc(131,22)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Parent);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(131,22)
    stack1o := TypeObject(Parent);
    // ----- classic unpack  ----- PeerFields.ssc(131,22)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == Parent && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block9452;

  block9452:
    // ----- store field  ----- PeerFields.ssc(132,7)
    assert this != null;
    assert !($Heap[this, $inv] <: Parent) || $Heap[this, $localinv] == System.Object;
    assert c == null || $Heap[c, $ownerFrame] == $PeerGroupPlaceholder || ($Heap[c, $ownerRef] == this && $Heap[c, $ownerFrame] == Parent);
    $Heap[this, Parent.ch] := c;
    call $UpdateOwnersForRep(this, Parent, c);
    assume IsHeap($Heap);
    // ----- branch
    goto block9503;

  block9503:
    // ----- copy  ----- PeerFields.ssc(133,5)
    stack0o := local1;
    // ----- load token  ----- PeerFields.ssc(133,5)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Parent);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(133,5)
    stack1o := TypeObject(Parent);
    // ----- classic pack  ----- PeerFields.ssc(133,5)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == Parent ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := Parent;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block9469;

  block9469:
    // ----- return  ----- PeerFields.ssc(134,3)
    return;

}



axiom Child <: Child;

axiom $BaseClass(Child) == System.Object;

axiom Child <: $BaseClass(Child) && AsDirectSubClass(Child, $BaseClass(Child)) == Child;

axiom !$IsImmutable(Child) && $AsMutable(Child) == Child;

procedure Child..ctor$System.Int32(this: ref, youngerSiblings$in: int where InRange(youngerSiblings$in, System.Int32));
  free requires true;
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Child && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Child <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



procedure Parent.N(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Parent && $Heap[this, $localinv] == $typeof(this);
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



implementation Parent.N(this: ref)
{
  var stack0o: ref, stack1o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, Parent);
    assume $Heap[this, $allocated] == true;
    goto block9996;

  block9996:
    goto block10013;

  block10013:
    // ----- load field  ----- PeerFields.ssc(138,5)
    assert this != null;
    stack0o := $Heap[this, Parent.ch];
    stack1o := null;
    // ----- binary operator  ----- PeerFields.ssc(138,5)
    // ----- branch  ----- PeerFields.ssc(138,5)
    goto true10013to10047, false10013to10030;

  true10013to10047:
    assume stack0o == stack1o;
    goto block10047;

  false10013to10030:
    assume stack0o != stack1o;
    goto block10030;

  block10047:
    // ----- return  ----- PeerFields.ssc(141,3)
    return;

  block10030:
    // ----- load field  ----- PeerFields.ssc(139,7)
    assert this != null;
    stack0o := $Heap[this, Parent.ch];
    // ----- call  ----- PeerFields.ssc(139,7)
    assert stack0o != null;
    call Child.M(stack0o);
    goto block10047;

}



procedure Child.M(this: ref);
  // user-declared preconditions
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



procedure Parent.P(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Parent && $Heap[this, $localinv] == $typeof(this);
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



implementation Parent.P(this: ref)
{
  var local0: ref where $Is(local0, Parent), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType, stack0b: bool;

  entry:
    assume $IsNotNull(this, Parent);
    assume $Heap[this, $allocated] == true;
    goto block10421;

  block10421:
    goto block10489;

  block10489:
    // ----- copy  ----- PeerFields.ssc(145,22)
    local0 := this;
    // ----- copy  ----- PeerFields.ssc(145,22)
    stack0o := local0;
    // ----- load token  ----- PeerFields.ssc(145,22)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Parent);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(145,22)
    stack1o := TypeObject(Parent);
    // ----- classic unpack  ----- PeerFields.ssc(145,22)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == Parent && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block10506;

  block10506:
    // ----- load field  ----- PeerFields.ssc(146,7)
    assert this != null;
    stack0o := $Heap[this, Parent.ch];
    stack1o := null;
    // ----- binary operator  ----- PeerFields.ssc(146,7)
    // ----- branch  ----- PeerFields.ssc(146,7)
    goto true10506to10557, false10506to10523;

  true10506to10557:
    assume stack0o == stack1o;
    goto block10557;

  false10506to10523:
    assume stack0o != stack1o;
    goto block10523;

  block10557:
    // ----- branch
    goto block10608;

  block10523:
    // ----- load field  ----- PeerFields.ssc(147,9)
    assert this != null;
    stack0o := $Heap[this, Parent.ch];
    // ----- call  ----- PeerFields.ssc(147,9)
    assert stack0o != null;
    call Child.M(stack0o);
    // ----- load field  ----- PeerFields.ssc(148,9)
    assert this != null;
    stack0o := $Heap[this, Parent.ch];
    // ----- load field  ----- PeerFields.ssc(148,9)
    assert stack0o != null;
    stack0o := $Heap[stack0o, Child.sibling];
    stack1o := null;
    // ----- binary operator  ----- PeerFields.ssc(148,9)
    // ----- branch  ----- PeerFields.ssc(148,9)
    goto true10523to10557, false10523to10540;

  true10523to10557:
    assume stack0o == stack1o;
    goto block10557;

  false10523to10540:
    assume stack0o != stack1o;
    goto block10540;

  block10540:
    // ----- load field  ----- PeerFields.ssc(149,11)
    assert this != null;
    stack0o := $Heap[this, Parent.ch];
    // ----- load field  ----- PeerFields.ssc(149,11)
    assert stack0o != null;
    stack0o := $Heap[stack0o, Child.sibling];
    // ----- call  ----- PeerFields.ssc(149,11)
    assert stack0o != null;
    call Child.M(stack0o);
    goto block10557;

  block10608:
    // ----- copy  ----- PeerFields.ssc(152,5)
    stack0o := local0;
    // ----- load token  ----- PeerFields.ssc(152,5)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Parent);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(152,5)
    stack1o := TypeObject(Parent);
    // ----- classic pack  ----- PeerFields.ssc(152,5)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == Parent ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := Parent;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block10574;

  block10574:
    // ----- return  ----- PeerFields.ssc(153,3)
    return;

}



procedure Parent.Q(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Parent && $Heap[this, $localinv] == $typeof(this);
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



implementation Parent.Q(this: ref)
{
  var stack0o: ref, stack1o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, Parent);
    assume $Heap[this, $allocated] == true;
    goto block11237;

  block11237:
    goto block11254;

  block11254:
    // ----- load field  ----- PeerFields.ssc(157,5)
    assert this != null;
    stack0o := $Heap[this, Parent.ch];
    stack1o := null;
    // ----- binary operator  ----- PeerFields.ssc(157,5)
    // ----- branch  ----- PeerFields.ssc(157,5)
    goto true11254to11288, false11254to11271;

  true11254to11288:
    assume stack0o == stack1o;
    goto block11288;

  false11254to11271:
    assume stack0o != stack1o;
    goto block11271;

  block11288:
    // ----- return  ----- PeerFields.ssc(160,3)
    return;

  block11271:
    // ----- load field  ----- PeerFields.ssc(158,7)
    assert this != null;
    stack0o := $Heap[this, Parent.ch];
    // ----- call  ----- PeerFields.ssc(158,7)
    assert stack0o != null;
    call Child.M(stack0o);
    goto block11288;

}



procedure Parent.Assign0(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Parent && $Heap[this, $localinv] == $typeof(this);
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



implementation Parent.Assign0(this: ref)
{
  var stack0i: int, stack50000o: ref, stack0o: ref, c: ref where $Is(c, Child), local1: ref where $Is(local1, Child), stack1s: struct, stack1o: ref, temp0: exposeVersionType, temp1: exposeVersionType;

  entry:
    assume $IsNotNull(this, Parent);
    assume $Heap[this, $allocated] == true;
    goto block11611;

  block11611:
    goto block11679;

  block11679:
    // ----- load constant 10  ----- PeerFields.ssc(163,5)
    stack0i := 10;
    // ----- new object  ----- PeerFields.ssc(163,5)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Child;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- PeerFields.ssc(163,5)
    assert stack50000o != null;
    call Child..ctor$System.Int32(stack50000o, stack0i);
    // ----- copy  ----- PeerFields.ssc(163,5)
    stack0o := stack50000o;
    // ----- copy  ----- PeerFields.ssc(163,5)
    c := stack0o;
    // ----- copy  ----- PeerFields.ssc(164,22)
    local1 := c;
    // ----- copy  ----- PeerFields.ssc(164,22)
    stack0o := local1;
    // ----- load token  ----- PeerFields.ssc(164,22)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Child);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(164,22)
    stack1o := TypeObject(Child);
    // ----- classic unpack  ----- PeerFields.ssc(164,22)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == Child && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block11696;

  block11696:
    // ----- load field  ----- PeerFields.ssc(165,7)
    assert this != null;
    stack0o := $Heap[this, Parent.ch];
    // ----- store field  ----- PeerFields.ssc(165,7)
    assert c != null;
    havoc temp1;
    $Heap[c, $exposeVersion] := temp1;
    assert stack0o == null || ($Heap[c, $ownerFrame] == $PeerGroupPlaceholder && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[c, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) || ((!($Heap[$Heap[c, $ownerRef], $inv] <: $Heap[c, $ownerFrame]) || $Heap[$Heap[c, $ownerRef], $localinv] == $BaseClass($Heap[c, $ownerFrame])) && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[c, $ownerRef] == $Heap[stack0o, $ownerRef] && $Heap[c, $ownerFrame] == $Heap[stack0o, $ownerFrame]);
    $Heap[c, Child.sibling] := stack0o;
    call $UpdateOwnersForPeer(c, stack0o);
    assume IsHeap($Heap);
    // ----- branch
    goto block11747;

  block11747:
    // ----- copy  ----- PeerFields.ssc(166,5)
    stack0o := local1;
    // ----- load token  ----- PeerFields.ssc(166,5)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Child);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(166,5)
    stack1o := TypeObject(Child);
    // ----- classic pack  ----- PeerFields.ssc(166,5)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == Child ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := Child;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block11713;

  block11713:
    // ----- return  ----- PeerFields.ssc(167,3)
    return;

}



procedure Parent.Assign1(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Parent && $Heap[this, $localinv] == $typeof(this);
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



implementation Parent.Assign1(this: ref)
{
  var local0: ref where $Is(local0, Parent), stack0o: ref, stack1s: struct, stack1o: ref, temp0: exposeVersionType, stack0i: int, stack50000o: ref, c: ref where $Is(c, Child), local2: ref where $Is(local2, Child), temp1: exposeVersionType, temp2: exposeVersionType;

  entry:
    assume $IsNotNull(this, Parent);
    assume $Heap[this, $allocated] == true;
    goto block12359;

  block12359:
    goto block12427;

  block12427:
    // ----- copy  ----- PeerFields.ssc(170,22)
    local0 := this;
    // ----- copy  ----- PeerFields.ssc(170,22)
    stack0o := local0;
    // ----- load token  ----- PeerFields.ssc(170,22)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Parent);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(170,22)
    stack1o := TypeObject(Parent);
    // ----- classic unpack  ----- PeerFields.ssc(170,22)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == Parent && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block12444;

  block12444:
    // ----- load constant 10  ----- PeerFields.ssc(171,7)
    stack0i := 10;
    // ----- new object  ----- PeerFields.ssc(171,7)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Child;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- PeerFields.ssc(171,7)
    assert stack50000o != null;
    call Child..ctor$System.Int32(stack50000o, stack0i);
    // ----- copy  ----- PeerFields.ssc(171,7)
    stack0o := stack50000o;
    // ----- copy  ----- PeerFields.ssc(171,7)
    c := stack0o;
    // ----- copy  ----- PeerFields.ssc(172,24)
    local2 := c;
    // ----- copy  ----- PeerFields.ssc(172,24)
    stack0o := local2;
    // ----- load token  ----- PeerFields.ssc(172,24)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Child);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(172,24)
    stack1o := TypeObject(Child);
    // ----- classic unpack  ----- PeerFields.ssc(172,24)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] == Child && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $inv] := System.Object;
    havoc temp1;
    $Heap[stack0o, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    goto block12461;

  block12461:
    // ----- load field  ----- PeerFields.ssc(173,9)
    assert this != null;
    stack0o := $Heap[this, Parent.ch];
    // ----- store field  ----- PeerFields.ssc(173,9)
    assert c != null;
    havoc temp2;
    $Heap[c, $exposeVersion] := temp2;
    assert stack0o == null || ($Heap[c, $ownerFrame] == $PeerGroupPlaceholder && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[c, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) || ((!($Heap[$Heap[c, $ownerRef], $inv] <: $Heap[c, $ownerFrame]) || $Heap[$Heap[c, $ownerRef], $localinv] == $BaseClass($Heap[c, $ownerFrame])) && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[c, $ownerRef] == $Heap[stack0o, $ownerRef] && $Heap[c, $ownerFrame] == $Heap[stack0o, $ownerFrame]);
    $Heap[c, Child.sibling] := stack0o;
    call $UpdateOwnersForPeer(c, stack0o);
    assume IsHeap($Heap);
    // ----- branch
    goto block12529;

  block12529:
    // ----- copy  ----- PeerFields.ssc(174,7)
    stack0o := local2;
    // ----- load token  ----- PeerFields.ssc(174,7)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Child);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(174,7)
    stack1o := TypeObject(Child);
    // ----- classic pack  ----- PeerFields.ssc(174,7)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == Child ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := Child;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block12478;

  block12478:
    // ----- branch
    goto block12546;

  block12546:
    // ----- copy  ----- PeerFields.ssc(175,5)
    stack0o := local0;
    // ----- load token  ----- PeerFields.ssc(175,5)
    havoc stack1s;
    assume $IsTokenForType(stack1s, Parent);
    // ----- statically resolved GetTypeFromHandle call  ----- PeerFields.ssc(175,5)
    stack1o := TypeObject(Parent);
    // ----- classic pack  ----- PeerFields.ssc(175,5)
    assert stack0o != null;
    assert $Heap[stack0o, $inv] == System.Object && $Heap[stack0o, $localinv] == $typeof(stack0o);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == Parent ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $inv] := Parent;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block12495;

  block12495:
    // ----- return  ----- PeerFields.ssc(176,3)
    return;

}



procedure Parent..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Parent && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(Parent <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation Parent..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, Parent);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, Parent.ch] == null;
    goto block13294;

  block13294:
    goto block13311;

  block13311:
    // ----- call  ----- PeerFields.ssc(126,14)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == Parent ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := Parent;
    assume IsHeap($Heap);
    return;

}



implementation Child..ctor$System.Int32(this: ref, youngerSiblings$in: int)
{
  var youngerSiblings: int where InRange(youngerSiblings, System.Int32), stack0i: int, stack0b: bool, stack50000o: ref, stack0o: ref, temp0: exposeVersionType;

  entry:
    assume $IsNotNull(this, Child);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    youngerSiblings := youngerSiblings$in;
    assume $Heap[this, Child.sibling] == null;
    goto block13515;

  block13515:
    goto block13532;

  block13532:
    // ----- call  ----- PeerFields.ssc(182,37)
    assert this != null;
    call System.Object..ctor(this);
    // ----- load constant 0  ----- PeerFields.ssc(183,5)
    stack0i := 0;
    // ----- binary operator  ----- PeerFields.ssc(183,5)
    // ----- branch  ----- PeerFields.ssc(183,5)
    goto true13532to13566, false13532to13549;

  true13532to13566:
    assume stack0i >= youngerSiblings;
    goto block13566;

  false13532to13549:
    assume stack0i < youngerSiblings;
    goto block13549;

  block13566:
    // ----- return  ----- PeerFields.ssc(186,3)
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == Child ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := Child;
    assume IsHeap($Heap);
    return;

  block13549:
    // ----- load constant 1  ----- PeerFields.ssc(184,7)
    stack0i := 1;
    // ----- binary operator  ----- PeerFields.ssc(184,7)
    stack0i := youngerSiblings - stack0i;
    // ----- new object  ----- PeerFields.ssc(184,7)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Child;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- PeerFields.ssc(184,7)
    assert stack50000o != null;
    call Child..ctor$System.Int32(stack50000o, stack0i);
    // ----- copy  ----- PeerFields.ssc(184,7)
    stack0o := stack50000o;
    // ----- store field  ----- PeerFields.ssc(184,7)
    assert this != null;
    havoc temp0;
    $Heap[this, $exposeVersion] := temp0;
    assert stack0o == null || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder && (!($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame]))) || ((!($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder) || ($Heap[this, $ownerRef] == $Heap[stack0o, $ownerRef] && $Heap[this, $ownerFrame] == $Heap[stack0o, $ownerFrame]);
    $Heap[this, Child.sibling] := stack0o;
    call $UpdateOwnersForPeer(this, stack0o);
    assume IsHeap($Heap);
    goto block13566;

}



implementation Child.M(this: ref)
{
  var stack0o: ref, stack1o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, Child);
    assume $Heap[this, $allocated] == true;
    goto block14008;

  block14008:
    goto block14110;

  block14110:
    // ----- nop
    // ----- load field  ----- PeerFields.ssc(191,5)
    assert this != null;
    stack0o := $Heap[this, Child.sibling];
    stack1o := null;
    // ----- binary operator  ----- PeerFields.ssc(191,5)
    // ----- branch  ----- PeerFields.ssc(191,5)
    goto true14110to14144, false14110to14127;

  true14110to14144:
    assume stack0o == stack1o;
    goto block14144;

  false14110to14127:
    assume stack0o != stack1o;
    goto block14127;

  block14144:
    // ----- return
    return;

  block14127:
    // ----- load field  ----- PeerFields.ssc(192,7)
    assert this != null;
    stack0o := $Heap[this, Child.sibling];
    // ----- call  ----- PeerFields.ssc(192,7)
    assert stack0o != null;
    call Child.M(stack0o);
    goto block14144;

}



const $stringLiteral0: ref;

axiom (forall heap: [ref,<x>name]x :: { heap[$stringLiteral0, $allocated] } IsHeap(heap) ==> heap[$stringLiteral0, $allocated]) && $IsNotNull($stringLiteral0, System.String) && $StringLength($stringLiteral0) == 5;

axiom (forall heap: [ref,<x>name]x :: { heap[$stringLiteral0, $allocated] } IsHeap(heap) ==> heap[$stringLiteral0, $allocated]) && $IsNotNull($stringLiteral0, System.String) && #System.String.IsInterned$System.String$notnull($stringLiteral0) == $stringLiteral0;
