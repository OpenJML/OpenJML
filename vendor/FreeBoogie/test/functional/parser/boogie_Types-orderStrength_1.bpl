// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: -nologo /prover:blank /print:boogie_tmp.@TIME@.bpl /proverLog:boogie_tmp.@TIME@.simplify /orderStrength:1 Types.dll

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

const T.x: <ref>name;

const T.g: <ref>name;

const T.y: <ref>name;

const T.next: <ref>name;

const System.Collections.ICollection: name;

const System.ICloneable: name;

const System.Boolean: name;

const L: name;

const J: name;

const System.IEquatable`1...System.String: name;

const F: name;

const System.Runtime.InteropServices._Type: name;

const System.Reflection.IReflect: name;

const T: name;

const System.IComparable: name;

const K: name;

const System.Runtime.InteropServices._MemberInfo: name;

const System.Reflection.MemberInfo: name;

const A: name;

const MoreTypes: name;

const System.Collections.IList: name;

const Types: name;

const System.Collections.IEnumerable: name;

const System.IConvertible: name;

const System.Reflection.ICustomAttributeProvider: name;

const System.Collections.Generic.IEnumerable`1...System.Char: name;

const D: name;

const B: name;

const System.IComparable`1...System.String: name;

const C: name;

axiom !IsStaticField(T.x);

axiom IsDirectlyModifiableField(T.x);

axiom DeclType(T.x) == T;

axiom AsRefField(T.x, D) == T.x;

axiom !IsStaticField(T.y);

axiom IsDirectlyModifiableField(T.y);

axiom DeclType(T.y) == T;

axiom AsNonNullRefField(T.y, D) == T.y;

axiom !IsStaticField(T.next);

axiom IsDirectlyModifiableField(T.next);

axiom DeclType(T.next) == T;

axiom AsRefField(T.next, T) == T.next;

axiom IsStaticField(T.g);

axiom IsDirectlyModifiableField(T.g);

axiom DeclType(T.g) == T;

axiom AsRefField(T.g, C) == T.g;

axiom Types <: Types;

axiom $BaseClass(Types) == System.Object;

axiom Types <: $BaseClass(Types) && AsDirectSubClass(Types, $BaseClass(Types)) == Types;

axiom !$IsImmutable(Types) && $AsMutable(Types) == Types;

axiom (forall $K: name :: { Types <: $K } Types <: $K <==> Types == $K || System.Object <: $K);

axiom (forall $U: name :: { $U <: Types } $U <: Types ==> $U == Types);

procedure Types.Main();
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



implementation Types.Main()
{

  entry:
    goto block1785;

  block1785:
    goto block1802;

  block1802:
    // ----- return  ----- Types.ssc(2,30)
    return;

}



axiom B <: B;

axiom A <: A;

axiom $BaseClass(A) == System.Object;

axiom A <: $BaseClass(A) && AsDirectSubClass(A, $BaseClass(A)) == A;

axiom !$IsImmutable(A) && $AsMutable(A) == A;

axiom (forall $K: name :: { A <: $K } A <: $K <==> A == $K || System.Object <: $K);

axiom $BaseClass(B) == A;

axiom B <: $BaseClass(B) && AsDirectSubClass(B, $BaseClass(B)) == B;

axiom !$IsImmutable(B) && $AsMutable(B) == B;

axiom J <: System.Object;

axiom (forall $K: name :: { J <: $K } J <: $K <==> J == $K || System.Object == $K);

axiom $IsMemberlessType(J);

axiom B <: J;

axiom (forall $K: name :: { B <: $K } B <: $K <==> B == $K || A <: $K || J <: $K);

axiom (forall $U: name :: { $U <: System.Boolean } $U <: System.Boolean ==> $U == System.Boolean);

procedure Types.M0$B$notnull$System.Boolean(this: ref, b$in: ref where $IsNotNull(b$in, B), maybe$in: bool where true);
  free requires $Heap[b$in, $allocated] == true;
  free requires true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[b$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[b$in, $ownerRef], $inv] <: $Heap[b$in, $ownerFrame]) || $Heap[$Heap[b$in, $ownerRef], $localinv] == $BaseClass($Heap[b$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[b$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[b$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation Types.M0$B$notnull$System.Boolean(this: ref, b$in: ref, maybe$in: bool)
{
  var b: ref where $IsNotNull(b, B), maybe: bool where true, stack0o: ref, o: ref where $Is(o, System.Object), stack0b: bool, stack1o: ref, isString: bool where true;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    b := b$in;
    maybe := maybe$in;
    goto block2873;

  block2873:
    goto block2975;

  block2975:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(5,5)
    assert $IsNotNull(b, B);
    goto block3060;

  block3060:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(6,5)
    assert $IsNotNull(b, A);
    goto block3145;

  block3145:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(7,5)
    assert $IsNotNull(b, System.Object);
    goto block3230;

  block3230:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(8,5)
    assert $IsNotNull(b, J);
    goto block3315;

  block3315:
    // ----- nop
    // ----- copy  ----- Types.ssc(9,5)
    o := b;
    // ----- serialized AssertStatement  ----- Types.ssc(10,5)
    assert o == b;
    goto block3400;

  block3400:
    // ----- nop
    // ----- copy  ----- Types.ssc(11,5)
    stack0b := maybe;
    // ----- unary operator  ----- Types.ssc(11,5)
    // ----- branch  ----- Types.ssc(11,5)
    goto true3400to3621, false3400to3417;

  true3400to3621:
    assume !stack0b;
    goto block3621;

  false3400to3417:
    assume stack0b;
    goto block3417;

  block3621:
    // ----- is instance  ----- Types.ssc(14,7)
    stack0o := $As(o, System.String);
    stack1o := null;
    // ----- binary operator  ----- Types.ssc(14,7)
    // ----- branch  ----- Types.ssc(14,7)
    goto true3621to3655, false3621to3638;

  block3417:
    // ----- serialized AssertStatement  ----- Types.ssc(12,7)
    assert !$IsNotNull(o, System.String);
    goto block3604;

  true3621to3655:
    assume stack0o != stack1o;
    goto block3655;

  false3621to3638:
    assume stack0o == stack1o;
    goto block3638;

  block3655:
    // ----- load constant 1
    stack0b := true;
    goto block3672;

  block3638:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block3672;

  block3604:
    // ----- nop
    // ----- branch  ----- Types.ssc(13,7)
    goto block3825;

  block3825:
    // ----- return
    return;

  block3672:
    // ----- copy
    isString := stack0b;
    // ----- serialized AssertStatement  ----- Types.ssc(15,7)
    assert !isString;
    goto block3808;

  block3808:
    // ----- nop
    // ----- nop  ----- Types.ssc(17,3)
    goto block3825;

}



axiom System.String <: System.String;

axiom $BaseClass(System.String) == System.Object;

axiom System.String <: $BaseClass(System.String) && AsDirectSubClass(System.String, $BaseClass(System.String)) == System.String;

axiom $IsImmutable(System.String) && $AsImmutable(System.String) == System.String;

axiom System.IComparable <: System.Object;

axiom (forall $K: name :: { System.IComparable <: $K } System.IComparable <: $K <==> System.IComparable == $K || System.Object == $K);

axiom $IsMemberlessType(System.IComparable);

axiom System.String <: System.IComparable;

axiom System.ICloneable <: System.Object;

axiom (forall $K: name :: { System.ICloneable <: $K } System.ICloneable <: $K <==> System.ICloneable == $K || System.Object == $K);

axiom $IsMemberlessType(System.ICloneable);

axiom System.String <: System.ICloneable;

axiom System.IConvertible <: System.Object;

axiom (forall $K: name :: { System.IConvertible <: $K } System.IConvertible <: $K <==> System.IConvertible == $K || System.Object == $K);

axiom $IsMemberlessType(System.IConvertible);

axiom System.String <: System.IConvertible;

axiom System.IComparable`1...System.String <: System.Object;

axiom (forall $K: name :: { System.IComparable`1...System.String <: $K } System.IComparable`1...System.String <: $K <==> System.IComparable`1...System.String == $K || System.Object == $K);

axiom $IsMemberlessType(System.IComparable`1...System.String);

axiom System.String <: System.IComparable`1...System.String;

axiom System.Collections.Generic.IEnumerable`1...System.Char <: System.Object;

axiom System.Collections.IEnumerable <: System.Object;

axiom (forall $K: name :: { System.Collections.IEnumerable <: $K } System.Collections.IEnumerable <: $K <==> System.Collections.IEnumerable == $K || System.Object == $K);

axiom $IsMemberlessType(System.Collections.IEnumerable);

axiom System.Collections.Generic.IEnumerable`1...System.Char <: System.Collections.IEnumerable;

axiom (forall $K: name :: { System.Collections.Generic.IEnumerable`1...System.Char <: $K } System.Collections.Generic.IEnumerable`1...System.Char <: $K <==> System.Collections.Generic.IEnumerable`1...System.Char == $K || System.Object == $K || System.Collections.IEnumerable <: $K);

axiom $IsMemberlessType(System.Collections.Generic.IEnumerable`1...System.Char);

axiom System.String <: System.Collections.Generic.IEnumerable`1...System.Char;

axiom System.String <: System.Collections.IEnumerable;

axiom System.IEquatable`1...System.String <: System.Object;

axiom (forall $K: name :: { System.IEquatable`1...System.String <: $K } System.IEquatable`1...System.String <: $K <==> System.IEquatable`1...System.String == $K || System.Object == $K);

axiom $IsMemberlessType(System.IEquatable`1...System.String);

axiom System.String <: System.IEquatable`1...System.String;

axiom (forall $K: name :: { System.String <: $K } System.String <: $K <==> System.String == $K || System.Object <: $K || System.IComparable <: $K || System.ICloneable <: $K || System.IConvertible <: $K || System.IComparable`1...System.String <: $K || System.Collections.Generic.IEnumerable`1...System.Char <: $K || System.Collections.IEnumerable <: $K || System.IEquatable`1...System.String <: $K);

axiom (forall $U: name :: { $U <: System.String } $U <: System.String ==> $U == System.String);

procedure Types.Px0$System.Object(this: ref, t$in: ref where $Is(t$in, System.Object));
  free requires $Heap[t$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires t$in == null || (($Heap[t$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[t$in, $ownerRef], $inv] <: $Heap[t$in, $ownerFrame]) || $Heap[$Heap[t$in, $ownerRef], $localinv] == $BaseClass($Heap[t$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[t$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[t$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
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



implementation Types.Px0$System.Object(this: ref, t$in: ref)
{
  var t: ref where $Is(t, System.Object), stack0o: ref;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    t := t$in;
    goto block5049;

  block5049:
    goto block5066;

  block5066:
    // ----- serialized AssumeStatement  ----- Types.ssc(20,5)
    assume $IsNotNull(t, Types);
    goto block5151;

  block5151:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(21,5)
    assert t != null;
    goto block5236;

  block5236:
    // ----- nop
    // ----- return  ----- Types.ssc(22,3)
    return;

}



procedure Types.Px1$System.Object(this: ref, t$in: ref where $Is(t$in, System.Object));
  free requires $Heap[t$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires t$in == null || (($Heap[t$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[t$in, $ownerRef], $inv] <: $Heap[t$in, $ownerFrame]) || $Heap[$Heap[t$in, $ownerRef], $localinv] == $BaseClass($Heap[t$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[t$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[t$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
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



implementation Types.Px1$System.Object(this: ref, t$in: ref)
{
  var t: ref where $Is(t, System.Object), stack0o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    t := t$in;
    goto block5678;

  block5678:
    goto block5695;

  block5695:
    // ----- is instance  ----- Types.ssc(25,5)
    stack0o := $As(t, Types);
    // ----- unary operator  ----- Types.ssc(25,5)
    // ----- branch  ----- Types.ssc(25,5)
    goto true5695to5814, false5695to5712;

  true5695to5814:
    assume stack0o == null;
    goto block5814;

  false5695to5712:
    assume stack0o != null;
    goto block5712;

  block5814:
    // ----- return  ----- Types.ssc(28,3)
    return;

  block5712:
    // ----- serialized AssertStatement  ----- Types.ssc(26,7)
    assert t != null;
    goto block5797;

  block5797:
    // ----- nop
    goto block5814;

}



procedure Types.Px2$System.Object(this: ref, t$in: ref where $Is(t$in, System.Object));
  free requires $Heap[t$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires t$in == null || (($Heap[t$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[t$in, $ownerRef], $inv] <: $Heap[t$in, $ownerFrame]) || $Heap[$Heap[t$in, $ownerRef], $localinv] == $BaseClass($Heap[t$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[t$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[t$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
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



implementation Types.Px2$System.Object(this: ref, t$in: ref)
{
  var t: ref where $Is(t, System.Object), stack0o: ref, stack1o: ref, stack0b: bool, b: bool where true;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    t := t$in;
    goto block6273;

  block6273:
    goto block6290;

  block6290:
    // ----- is instance  ----- Types.ssc(31,5)
    stack0o := $As(t, Types);
    stack1o := null;
    // ----- binary operator  ----- Types.ssc(31,5)
    // ----- branch  ----- Types.ssc(31,5)
    goto true6290to6324, false6290to6307;

  true6290to6324:
    assume stack0o != stack1o;
    goto block6324;

  false6290to6307:
    assume stack0o == stack1o;
    goto block6307;

  block6324:
    // ----- load constant 1
    stack0b := true;
    goto block6341;

  block6307:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block6341;

  block6341:
    // ----- copy
    b := stack0b;
    // ----- copy  ----- Types.ssc(32,5)
    stack0b := b;
    // ----- unary operator  ----- Types.ssc(32,5)
    // ----- branch  ----- Types.ssc(32,5)
    goto true6341to6460, false6341to6358;

  true6341to6460:
    assume !stack0b;
    goto block6460;

  false6341to6358:
    assume stack0b;
    goto block6358;

  block6460:
    // ----- return  ----- Types.ssc(35,3)
    return;

  block6358:
    // ----- serialized AssertStatement  ----- Types.ssc(33,7)
    assert t != null;
    goto block6443;

  block6443:
    // ----- nop
    goto block6460;

}



procedure Types.M1$B(this: ref, b$in: ref where $Is(b$in, B));
  free requires $Heap[b$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires b$in == null || (($Heap[b$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[b$in, $ownerRef], $inv] <: $Heap[b$in, $ownerFrame]) || $Heap[$Heap[b$in, $ownerRef], $localinv] == $BaseClass($Heap[b$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[b$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[b$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
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



implementation Types.M1$B(this: ref, b$in: ref)
{
  var b: ref where $Is(b, B), stack0o: ref, stack0b: bool, c: ref where $Is(c, C);

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    b := b$in;
    goto block7089;

  block7089:
    goto block7106;

  block7106:
    // ----- is instance  ----- Types.ssc(38,5)
    stack0o := $As(b, C);
    // ----- unary operator  ----- Types.ssc(38,5)
    // ----- branch  ----- Types.ssc(38,5)
    goto true7106to7310, false7106to7123;

  true7106to7310:
    assume stack0o == null;
    goto block7310;

  false7106to7123:
    assume stack0o != null;
    goto block7123;

  block7310:
    // ----- return  ----- Types.ssc(43,3)
    return;

  block7123:
    // ----- serialized AssertStatement  ----- Types.ssc(39,7)
    assert b != null;
    goto block7208;

  block7208:
    // ----- nop
    // ----- castclass  ----- Types.ssc(40,7)
    assert $Is(b, C);
    stack0o := b;
    // ----- copy  ----- Types.ssc(40,7)
    c := stack0o;
    // ----- serialized AssertStatement  ----- Types.ssc(41,7)
    assert b == c;
    goto block7293;

  block7293:
    // ----- nop
    goto block7310;

}



axiom C <: C;

axiom $BaseClass(C) == B;

axiom C <: $BaseClass(C) && AsDirectSubClass(C, $BaseClass(C)) == C;

axiom !$IsImmutable(C) && $AsMutable(C) == C;

axiom (forall $K: name :: { C <: $K } C <: $K <==> C == $K || B <: $K);

procedure Types.M2$B(this: ref, b$in: ref where $Is(b$in, B));
  free requires $Heap[b$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires b$in == null || (($Heap[b$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[b$in, $ownerRef], $inv] <: $Heap[b$in, $ownerFrame]) || $Heap[$Heap[b$in, $ownerRef], $localinv] == $BaseClass($Heap[b$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[b$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[b$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
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



implementation Types.M2$B(this: ref, b$in: ref)
{
  var b: ref where $Is(b, B), stack0o: ref, c: ref where $Is(c, C), stack0b: bool;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    b := b$in;
    goto block7922;

  block7922:
    goto block7939;

  block7939:
    // ----- is instance  ----- Types.ssc(46,5)
    stack0o := $As(b, C);
    // ----- copy  ----- Types.ssc(46,5)
    c := stack0o;
    stack0o := null;
    // ----- binary operator  ----- Types.ssc(47,5)
    // ----- branch  ----- Types.ssc(47,5)
    goto true7939to8143, false7939to7956;

  true7939to8143:
    assume c == stack0o;
    goto block8143;

  false7939to7956:
    assume c != stack0o;
    goto block7956;

  block8143:
    // ----- return  ----- Types.ssc(51,3)
    return;

  block7956:
    // ----- serialized AssertStatement  ----- Types.ssc(48,7)
    assert $IsNotNull(b, C);
    goto block8041;

  block8041:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(49,7)
    assert b == c;
    goto block8126;

  block8126:
    // ----- nop
    goto block8143;

}



procedure Types.M3$B(this: ref, b$in: ref where $Is(b$in, B));
  free requires $Heap[b$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires b$in == null || (($Heap[b$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[b$in, $ownerRef], $inv] <: $Heap[b$in, $ownerFrame]) || $Heap[$Heap[b$in, $ownerRef], $localinv] == $BaseClass($Heap[b$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[b$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[b$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
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



implementation Types.M3$B(this: ref, b$in: ref)
{
  var b: ref where $Is(b, B), stack0o: ref, bb: ref where $Is(bb, B);

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    b := b$in;
    goto block9061;

  block9061:
    goto block9078;

  block9078:
    // ----- is instance  ----- Types.ssc(54,5)
    // ----- branch  ----- Types.ssc(54,5)
    goto true9078to9197, false9078to9095;

  true9078to9197:
    assume $As(b, B) != null;
    goto block9197;

  false9078to9095:
    assume $As(b, B) == null;
    goto block9095;

  block9197:
    // ----- copy  ----- Types.ssc(57,7)
    stack0o := b;
    assert stack0o != null;
    bb := stack0o;
    // ----- serialized AssertStatement  ----- Types.ssc(58,7)
    assert bb == b;
    goto block9282;

  block9095:
    // ----- serialized AssertStatement  ----- Types.ssc(55,7)
    assert b == null;
    goto block9180;

  block9180:
    // ----- nop
    // ----- branch  ----- Types.ssc(56,7)
    goto block9299;

  block9282:
    // ----- nop
    // ----- nop  ----- Types.ssc(60,3)
    goto block9299;

  block9299:
    // ----- return  ----- Types.ssc(60,3)
    return;

}



procedure Types.M4$System.Object(this: ref, o$in: ref where $Is(o$in, System.Object));
  free requires $Heap[o$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires o$in == null || (($Heap[o$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[o$in, $ownerRef], $inv] <: $Heap[o$in, $ownerFrame]) || $Heap[$Heap[o$in, $ownerRef], $localinv] == $BaseClass($Heap[o$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[o$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[o$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
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



implementation Types.M4$System.Object(this: ref, o$in: ref)
{
  var o: ref where $Is(o, System.Object), stack0o: ref;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    o := o$in;
    goto block10047;

  block10047:
    goto block10064;

  block10064:
    // ----- serialized AssertStatement  ----- Types.ssc(63,5)
    assert $IsNotNull(o, D) == $IsNotNull(o, D);
    goto block10251;

  block10251:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(64,5)
    assert $As(o, A) == $As(o, A);
    goto block10336;

  block10336:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(65,5)
    assert $As(o, C) == $As(o, C);
    goto block10421;

  block10421:
    // ----- nop
    // ----- return  ----- Types.ssc(66,3)
    return;

}



axiom D <: D;

axiom $BaseClass(D) == A;

axiom D <: $BaseClass(D) && AsDirectSubClass(D, $BaseClass(D)) == D;

axiom !$IsImmutable(D) && $AsMutable(D) == D;

axiom (forall $K: name :: { D <: $K } D <: $K <==> D == $K || A <: $K);

procedure Types.N0$C$D(this: ref, c$in: ref where $Is(c$in, C), d$in: ref where $Is(d$in, D));
  free requires $Heap[c$in, $allocated] == true;
  free requires $Heap[d$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires c$in == null || (($Heap[c$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[c$in, $ownerRef], $inv] <: $Heap[c$in, $ownerFrame]) || $Heap[$Heap[c$in, $ownerRef], $localinv] == $BaseClass($Heap[c$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[c$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[c$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
  requires d$in == null || (($Heap[d$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[d$in, $ownerRef], $inv] <: $Heap[d$in, $ownerFrame]) || $Heap[$Heap[d$in, $ownerRef], $localinv] == $BaseClass($Heap[d$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[d$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[d$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
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



implementation Types.N0$C$D(this: ref, c$in: ref, d$in: ref)
{
  var c: ref where $Is(c, C), d: ref where $Is(d, D), cc: ref where $Is(cc, System.Object), dd: ref where $Is(dd, System.Object), stack0o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    c := c$in;
    d := d$in;
    goto block11237;

  block11237:
    goto block11254;

  block11254:
    // ----- copy  ----- Types.ssc(70,5)
    cc := c;
    // ----- copy  ----- Types.ssc(71,5)
    dd := d;
    // ----- serialized AssertStatement  ----- Types.ssc(72,5)
    assert cc == c && dd == d;
    goto block11373;

  block11373:
    // ----- nop
    stack0o := null;
    // ----- binary operator  ----- Types.ssc(73,5)
    // ----- branch  ----- Types.ssc(73,5)
    goto true11373to11492, false11373to11390;

  true11373to11492:
    assume c == stack0o;
    goto block11492;

  false11373to11390:
    assume c != stack0o;
    goto block11390;

  block11492:
    stack0o := null;
    // ----- binary operator  ----- Types.ssc(75,12)
    // ----- branch  ----- Types.ssc(75,12)
    goto true11492to11611, false11492to11509;

  block11390:
    // ----- serialized AssertStatement  ----- Types.ssc(74,7)
    assert cc != dd;
    goto block11475;

  true11492to11611:
    assume d == stack0o;
    goto block11611;

  false11492to11509:
    assume d != stack0o;
    goto block11509;

  block11611:
    // ----- nop  ----- Types.ssc(78,3)
    goto block11628;

  block11509:
    // ----- serialized AssertStatement  ----- Types.ssc(76,7)
    assert cc != dd;
    goto block11594;

  block11475:
    // ----- nop
    // ----- branch  ----- Types.ssc(75,7)
    goto block11628;

  block11628:
    // ----- return  ----- Types.ssc(78,3)
    return;

  block11594:
    // ----- nop
    goto block11611;

}



procedure Types.N1$C$D(this: ref, c$in: ref where $Is(c$in, C), d$in: ref where $Is(d$in, D));
  free requires $Heap[c$in, $allocated] == true;
  free requires $Heap[d$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires c$in == null || (($Heap[c$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[c$in, $ownerRef], $inv] <: $Heap[c$in, $ownerFrame]) || $Heap[$Heap[c$in, $ownerRef], $localinv] == $BaseClass($Heap[c$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[c$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[c$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
  requires d$in == null || (($Heap[d$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[d$in, $ownerRef], $inv] <: $Heap[d$in, $ownerFrame]) || $Heap[$Heap[d$in, $ownerRef], $localinv] == $BaseClass($Heap[d$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[d$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[d$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
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



implementation Types.N1$C$D(this: ref, c$in: ref, d$in: ref)
{
  var c: ref where $Is(c, C), d: ref where $Is(d, D), stack0o: ref;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    c := c$in;
    d := d$in;
    goto block12257;

  block12257:
    goto block12274;

  block12274:
    // ----- serialized AssertStatement  ----- Types.ssc(81,5)
    assert c != d;
    goto block12359;

  block12359:
    // ----- nop
    // ----- return  ----- Types.ssc(82,3)
    return;

}



axiom K <: System.Object;

axiom K <: J;

axiom (forall $K: name :: { K <: $K } K <: $K <==> K == $K || System.Object == $K || J <: $K);

axiom $IsMemberlessType(K);

procedure Types.P0$K$notnull(this: ref, k$in: ref where $IsNotNull(k$in, K));
  free requires $Heap[k$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[k$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[k$in, $ownerRef], $inv] <: $Heap[k$in, $ownerFrame]) || $Heap[$Heap[k$in, $ownerRef], $localinv] == $BaseClass($Heap[k$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[k$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[k$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation Types.P0$K$notnull(this: ref, k$in: ref)
{
  var k: ref where $IsNotNull(k, K), stack0o: ref, ok: ref where $Is(ok, System.Object);

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    k := k$in;
    goto block13226;

  block13226:
    goto block13328;

  block13328:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(85,5)
    assert $IsNotNull(k, J);
    goto block13413;

  block13413:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(86,5)
    assert $IsNotNull(k, System.Object);
    goto block13498;

  block13498:
    // ----- nop
    // ----- copy  ----- Types.ssc(87,5)
    ok := k;
    // ----- serialized AssertStatement  ----- Types.ssc(88,5)
    assert !$IsNotNull(ok, F);
    goto block13685;

  block13685:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(89,5)
    assert !$IsNotNull(ok, ValueArray(System.Int32, 1));
    goto block13872;

  block13872:
    // ----- nop
    // ----- return
    return;

}



axiom F <: F;

axiom $BaseClass(F) == A;

axiom F <: $BaseClass(F) && AsDirectSubClass(F, $BaseClass(F)) == F;

axiom !$IsImmutable(F) && $AsMutable(F) == F;

axiom (forall $K: name :: { F <: $K } F <: $K <==> F == $K || A <: $K);

axiom (forall $U: name :: { $U <: F } $U <: F ==> $U == F);

procedure Types.P1$K$notnull(this: ref, k$in: ref where $IsNotNull(k$in, K));
  free requires $Heap[k$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[k$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[k$in, $ownerRef], $inv] <: $Heap[k$in, $ownerFrame]) || $Heap[$Heap[k$in, $ownerRef], $localinv] == $BaseClass($Heap[k$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[k$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[k$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation Types.P1$K$notnull(this: ref, k$in: ref)
{
  var k: ref where $IsNotNull(k, K), ok: ref where $Is(ok, System.Object), stack0o: ref;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    k := k$in;
    goto block14773;

  block14773:
    goto block14875;

  block14875:
    // ----- nop
    // ----- copy  ----- Types.ssc(93,5)
    ok := k;
    // ----- serialized AssertStatement  ----- Types.ssc(94,5)
    assert !$IsNotNull(ok, A);
    goto block15062;

  block15062:
    // ----- nop
    // ----- return
    return;

}



procedure Types.P2$K$notnull(this: ref, k$in: ref where $IsNotNull(k$in, K));
  free requires $Heap[k$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[k$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[k$in, $ownerRef], $inv] <: $Heap[k$in, $ownerFrame]) || $Heap[$Heap[k$in, $ownerRef], $localinv] == $BaseClass($Heap[k$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[k$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[k$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation Types.P2$K$notnull(this: ref, k$in: ref)
{
  var k: ref where $IsNotNull(k, K), stack0o: ref;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    k := k$in;
    goto block15674;

  block15674:
    goto block15776;

  block15776:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(98,5)
    assert !$IsNotNull(k, L);
    goto block15963;

  block15963:
    // ----- nop
    // ----- return
    return;

}



axiom L <: System.Object;

axiom (forall $K: name :: { L <: $K } L <: $K <==> L == $K || System.Object == $K);

axiom $IsMemberlessType(L);

procedure Types.P3$K$notnull(this: ref, k$in: ref where $IsNotNull(k$in, K));
  free requires $Heap[k$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[k$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[k$in, $ownerRef], $inv] <: $Heap[k$in, $ownerFrame]) || $Heap[$Heap[k$in, $ownerRef], $localinv] == $BaseClass($Heap[k$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[k$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[k$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation Types.P3$K$notnull(this: ref, k$in: ref)
{
  var k: ref where $IsNotNull(k, K), ok: ref where $Is(ok, System.Object), stack0o: ref;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    k := k$in;
    goto block16558;

  block16558:
    goto block16660;

  block16660:
    // ----- nop
    // ----- copy  ----- Types.ssc(102,5)
    ok := k;
    // ----- serialized AssertStatement  ----- Types.ssc(103,5)
    assert !$IsNotNull(ok, System.Array);
    goto block16847;

  block16847:
    // ----- nop
    // ----- return
    return;

}



axiom System.Array <: System.Array;

axiom $BaseClass(System.Array) == System.Object;

axiom System.Array <: $BaseClass(System.Array) && AsDirectSubClass(System.Array, $BaseClass(System.Array)) == System.Array;

axiom !$IsImmutable(System.Array) && $AsMutable(System.Array) == System.Array;

axiom System.Array <: System.ICloneable;

axiom System.Collections.IList <: System.Object;

axiom System.Collections.ICollection <: System.Object;

axiom System.Collections.ICollection <: System.Collections.IEnumerable;

axiom (forall $K: name :: { System.Collections.ICollection <: $K } System.Collections.ICollection <: $K <==> System.Collections.ICollection == $K || System.Object == $K || System.Collections.IEnumerable <: $K);

axiom $IsMemberlessType(System.Collections.ICollection);

axiom System.Collections.IList <: System.Collections.ICollection;

axiom System.Collections.IList <: System.Collections.IEnumerable;

axiom (forall $K: name :: { System.Collections.IList <: $K } System.Collections.IList <: $K <==> System.Collections.IList == $K || System.Object == $K || System.Collections.ICollection <: $K || System.Collections.IEnumerable <: $K);

axiom $IsMemberlessType(System.Collections.IList);

axiom System.Array <: System.Collections.IList;

axiom System.Array <: System.Collections.ICollection;

axiom System.Array <: System.Collections.IEnumerable;

axiom (forall $K: name :: { System.Array <: $K } System.Array <: $K <==> System.Array == $K || System.Object <: $K || System.ICloneable <: $K || System.Collections.IList <: $K || System.Collections.ICollection <: $K || System.Collections.IEnumerable <: $K);

axiom $IsMemberlessType(System.Array);

procedure Types.P4$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this: ref, aObject$in: ref where $IsNotNull(aObject$in, RefArray(System.Object, 1)), aInt$in: ref where $IsNotNull(aInt$in, ValueArray(System.Int32, 1)), aA$in: ref where $IsNotNull(aA$in, RefArray(A, 1)), aJ$in: ref where $IsNotNull(aJ$in, RefArray(J, 1)), aB$in: ref where $IsNotNull(aB$in, RefArray(B, 1)));
  free requires $Heap[aObject$in, $allocated] == true;
  free requires $Heap[aInt$in, $allocated] == true;
  free requires $Heap[aA$in, $allocated] == true;
  free requires $Heap[aJ$in, $allocated] == true;
  free requires $Heap[aB$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aObject$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aObject$in, $ownerRef], $inv] <: $Heap[aObject$in, $ownerFrame]) || $Heap[$Heap[aObject$in, $ownerRef], $localinv] == $BaseClass($Heap[aObject$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aObject$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aObject$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aInt$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aInt$in, $ownerRef], $inv] <: $Heap[aInt$in, $ownerFrame]) || $Heap[$Heap[aInt$in, $ownerRef], $localinv] == $BaseClass($Heap[aInt$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aInt$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aInt$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aA$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aA$in, $ownerRef], $inv] <: $Heap[aA$in, $ownerFrame]) || $Heap[$Heap[aA$in, $ownerRef], $localinv] == $BaseClass($Heap[aA$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aA$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aA$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aJ$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aJ$in, $ownerRef], $inv] <: $Heap[aJ$in, $ownerFrame]) || $Heap[$Heap[aJ$in, $ownerRef], $localinv] == $BaseClass($Heap[aJ$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aJ$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aJ$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aB$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aB$in, $ownerRef], $inv] <: $Heap[aB$in, $ownerFrame]) || $Heap[$Heap[aB$in, $ownerRef], $localinv] == $BaseClass($Heap[aB$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aB$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aB$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation Types.P4$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this: ref, aObject$in: ref, aInt$in: ref, aA$in: ref, aJ$in: ref, aB$in: ref)
{
  var aObject: ref where $IsNotNull(aObject, RefArray(System.Object, 1)), aInt: ref where $IsNotNull(aInt, ValueArray(System.Int32, 1)), aA: ref where $IsNotNull(aA, RefArray(A, 1)), aJ: ref where $IsNotNull(aJ, RefArray(J, 1)), aB: ref where $IsNotNull(aB, RefArray(B, 1)), o: ref where $Is(o, System.Object), p: ref where $Is(p, System.Object), stack0o: ref;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    aObject := aObject$in;
    aInt := aInt$in;
    aA := aA$in;
    aJ := aJ$in;
    aB := aB$in;
    goto block18496;

  block18496:
    goto block18802;

  block18802:
    // ----- nop
    // ----- copy  ----- Types.ssc(108,5)
    o := aInt;
    // ----- copy  ----- Types.ssc(108,16)
    p := aObject;
    // ----- serialized AssertStatement  ----- Types.ssc(109,5)
    assert o != p;
    goto block18887;

  block18887:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(110,5)
    assert aInt != aObject;
    goto block18972;

  block18972:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(111,5)
    assert aInt != aObject;
    goto block19057;

  block19057:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(112,5)
    assert aInt != aObject;
    goto block19142;

  block19142:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(113,5)
    assert aInt == aInt;
    goto block19227;

  block19227:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(115,5)
    assert aInt != aJ;
    goto block19312;

  block19312:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(116,5)
    assert aInt != aA;
    goto block19397;

  block19397:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(117,5)
    assert aInt != aB;
    goto block19482;

  block19482:
    // ----- nop
    // ----- copy  ----- Types.ssc(119,5)
    o := aB;
    // ----- serialized AssertStatement  ----- Types.ssc(120,5)
    assert $IsNotNull(o, RefArray(A, 1));
    goto block19567;

  block19567:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(121,5)
    assert $IsNotNull(o, RefArray(J, 1));
    goto block19652;

  block19652:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(122,5)
    assert $IsNotNull(o, RefArray(System.Object, 1));
    goto block19737;

  block19737:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(123,5)
    assert $IsNotNull(o, RefArray(System.Object, 1));
    goto block19822;

  block19822:
    // ----- nop
    // ----- return
    return;

}



procedure Types.P5$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this: ref, aObject$in: ref where $IsNotNull(aObject$in, RefArray(System.Object, 1)), aInt$in: ref where $IsNotNull(aInt$in, ValueArray(System.Int32, 1)), aA$in: ref where $IsNotNull(aA$in, RefArray(A, 1)), aJ$in: ref where $IsNotNull(aJ$in, RefArray(J, 1)), aB$in: ref where $IsNotNull(aB$in, RefArray(B, 1)));
  free requires $Heap[aObject$in, $allocated] == true;
  free requires $Heap[aInt$in, $allocated] == true;
  free requires $Heap[aA$in, $allocated] == true;
  free requires $Heap[aJ$in, $allocated] == true;
  free requires $Heap[aB$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aObject$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aObject$in, $ownerRef], $inv] <: $Heap[aObject$in, $ownerFrame]) || $Heap[$Heap[aObject$in, $ownerRef], $localinv] == $BaseClass($Heap[aObject$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aObject$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aObject$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aInt$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aInt$in, $ownerRef], $inv] <: $Heap[aInt$in, $ownerFrame]) || $Heap[$Heap[aInt$in, $ownerRef], $localinv] == $BaseClass($Heap[aInt$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aInt$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aInt$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aA$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aA$in, $ownerRef], $inv] <: $Heap[aA$in, $ownerFrame]) || $Heap[$Heap[aA$in, $ownerRef], $localinv] == $BaseClass($Heap[aA$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aA$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aA$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aJ$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aJ$in, $ownerRef], $inv] <: $Heap[aJ$in, $ownerFrame]) || $Heap[$Heap[aJ$in, $ownerRef], $localinv] == $BaseClass($Heap[aJ$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aJ$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aJ$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aB$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aB$in, $ownerRef], $inv] <: $Heap[aB$in, $ownerFrame]) || $Heap[$Heap[aB$in, $ownerRef], $localinv] == $BaseClass($Heap[aB$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aB$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aB$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation Types.P5$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this: ref, aObject$in: ref, aInt$in: ref, aA$in: ref, aJ$in: ref, aB$in: ref)
{
  var aObject: ref where $IsNotNull(aObject, RefArray(System.Object, 1)), aInt: ref where $IsNotNull(aInt, ValueArray(System.Int32, 1)), aA: ref where $IsNotNull(aA, RefArray(A, 1)), aJ: ref where $IsNotNull(aJ, RefArray(J, 1)), aB: ref where $IsNotNull(aB, RefArray(B, 1)), stack0o: ref;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    aObject := aObject$in;
    aInt := aInt$in;
    aA := aA$in;
    aJ := aJ$in;
    aB := aB$in;
    goto block21471;

  block21471:
    goto block21777;

  block21777:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(127,5)
    assert aA != aJ;
    goto block21862;

  block21862:
    // ----- nop
    // ----- return
    return;

}



procedure Types.P6$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this: ref, aObject$in: ref where $IsNotNull(aObject$in, RefArray(System.Object, 1)), aInt$in: ref where $IsNotNull(aInt$in, ValueArray(System.Int32, 1)), aA$in: ref where $IsNotNull(aA$in, RefArray(A, 1)), aJ$in: ref where $IsNotNull(aJ$in, RefArray(J, 1)), aB$in: ref where $IsNotNull(aB$in, RefArray(B, 1)));
  free requires $Heap[aObject$in, $allocated] == true;
  free requires $Heap[aInt$in, $allocated] == true;
  free requires $Heap[aA$in, $allocated] == true;
  free requires $Heap[aJ$in, $allocated] == true;
  free requires $Heap[aB$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aObject$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aObject$in, $ownerRef], $inv] <: $Heap[aObject$in, $ownerFrame]) || $Heap[$Heap[aObject$in, $ownerRef], $localinv] == $BaseClass($Heap[aObject$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aObject$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aObject$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aInt$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aInt$in, $ownerRef], $inv] <: $Heap[aInt$in, $ownerFrame]) || $Heap[$Heap[aInt$in, $ownerRef], $localinv] == $BaseClass($Heap[aInt$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aInt$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aInt$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aA$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aA$in, $ownerRef], $inv] <: $Heap[aA$in, $ownerFrame]) || $Heap[$Heap[aA$in, $ownerRef], $localinv] == $BaseClass($Heap[aA$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aA$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aA$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aJ$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aJ$in, $ownerRef], $inv] <: $Heap[aJ$in, $ownerFrame]) || $Heap[$Heap[aJ$in, $ownerRef], $localinv] == $BaseClass($Heap[aJ$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aJ$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aJ$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aB$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aB$in, $ownerRef], $inv] <: $Heap[aB$in, $ownerFrame]) || $Heap[$Heap[aB$in, $ownerRef], $localinv] == $BaseClass($Heap[aB$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aB$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aB$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation Types.P6$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this: ref, aObject$in: ref, aInt$in: ref, aA$in: ref, aJ$in: ref, aB$in: ref)
{
  var aObject: ref where $IsNotNull(aObject, RefArray(System.Object, 1)), aInt: ref where $IsNotNull(aInt, ValueArray(System.Int32, 1)), aA: ref where $IsNotNull(aA, RefArray(A, 1)), aJ: ref where $IsNotNull(aJ, RefArray(J, 1)), aB: ref where $IsNotNull(aB, RefArray(B, 1)), stack0o: ref;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    aObject := aObject$in;
    aInt := aInt$in;
    aA := aA$in;
    aJ := aJ$in;
    aB := aB$in;
    goto block22525;

  block22525:
    goto block22831;

  block22831:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(131,5)
    assert aB != aJ;
    goto block22916;

  block22916:
    // ----- nop
    // ----- return
    return;

}



procedure Types.P7$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this: ref, aObject$in: ref where $IsNotNull(aObject$in, RefArray(System.Object, 1)), aInt$in: ref where $IsNotNull(aInt$in, ValueArray(System.Int32, 1)), aA$in: ref where $IsNotNull(aA$in, RefArray(A, 1)), aJ$in: ref where $IsNotNull(aJ$in, RefArray(J, 1)), aB$in: ref where $IsNotNull(aB$in, RefArray(B, 1)));
  free requires $Heap[aObject$in, $allocated] == true;
  free requires $Heap[aInt$in, $allocated] == true;
  free requires $Heap[aA$in, $allocated] == true;
  free requires $Heap[aJ$in, $allocated] == true;
  free requires $Heap[aB$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aObject$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aObject$in, $ownerRef], $inv] <: $Heap[aObject$in, $ownerFrame]) || $Heap[$Heap[aObject$in, $ownerRef], $localinv] == $BaseClass($Heap[aObject$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aObject$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aObject$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aInt$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aInt$in, $ownerRef], $inv] <: $Heap[aInt$in, $ownerFrame]) || $Heap[$Heap[aInt$in, $ownerRef], $localinv] == $BaseClass($Heap[aInt$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aInt$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aInt$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aA$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aA$in, $ownerRef], $inv] <: $Heap[aA$in, $ownerFrame]) || $Heap[$Heap[aA$in, $ownerRef], $localinv] == $BaseClass($Heap[aA$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aA$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aA$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aJ$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aJ$in, $ownerRef], $inv] <: $Heap[aJ$in, $ownerFrame]) || $Heap[$Heap[aJ$in, $ownerRef], $localinv] == $BaseClass($Heap[aJ$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aJ$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aJ$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aB$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aB$in, $ownerRef], $inv] <: $Heap[aB$in, $ownerFrame]) || $Heap[$Heap[aB$in, $ownerRef], $localinv] == $BaseClass($Heap[aB$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aB$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aB$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation Types.P7$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this: ref, aObject$in: ref, aInt$in: ref, aA$in: ref, aJ$in: ref, aB$in: ref)
{
  var aObject: ref where $IsNotNull(aObject, RefArray(System.Object, 1)), aInt: ref where $IsNotNull(aInt, ValueArray(System.Int32, 1)), aA: ref where $IsNotNull(aA, RefArray(A, 1)), aJ: ref where $IsNotNull(aJ, RefArray(J, 1)), aB: ref where $IsNotNull(aB, RefArray(B, 1)), stack0o: ref;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    aObject := aObject$in;
    aInt := aInt$in;
    aA := aA$in;
    aJ := aJ$in;
    aB := aB$in;
    goto block23579;

  block23579:
    goto block23885;

  block23885:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(135,5)
    assert aB != aA;
    goto block23970;

  block23970:
    // ----- nop
    // ----- return
    return;

}



procedure Types.P8$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this: ref, aObject$in: ref where $IsNotNull(aObject$in, RefArray(System.Object, 1)), aInt$in: ref where $IsNotNull(aInt$in, ValueArray(System.Int32, 1)), aA$in: ref where $IsNotNull(aA$in, RefArray(A, 1)), aJ$in: ref where $IsNotNull(aJ$in, RefArray(J, 1)), aB$in: ref where $IsNotNull(aB$in, RefArray(B, 1)));
  free requires $Heap[aObject$in, $allocated] == true;
  free requires $Heap[aInt$in, $allocated] == true;
  free requires $Heap[aA$in, $allocated] == true;
  free requires $Heap[aJ$in, $allocated] == true;
  free requires $Heap[aB$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aObject$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aObject$in, $ownerRef], $inv] <: $Heap[aObject$in, $ownerFrame]) || $Heap[$Heap[aObject$in, $ownerRef], $localinv] == $BaseClass($Heap[aObject$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aObject$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aObject$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aInt$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aInt$in, $ownerRef], $inv] <: $Heap[aInt$in, $ownerFrame]) || $Heap[$Heap[aInt$in, $ownerRef], $localinv] == $BaseClass($Heap[aInt$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aInt$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aInt$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aA$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aA$in, $ownerRef], $inv] <: $Heap[aA$in, $ownerFrame]) || $Heap[$Heap[aA$in, $ownerRef], $localinv] == $BaseClass($Heap[aA$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aA$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aA$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aJ$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aJ$in, $ownerRef], $inv] <: $Heap[aJ$in, $ownerFrame]) || $Heap[$Heap[aJ$in, $ownerRef], $localinv] == $BaseClass($Heap[aJ$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aJ$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aJ$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aB$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aB$in, $ownerRef], $inv] <: $Heap[aB$in, $ownerFrame]) || $Heap[$Heap[aB$in, $ownerRef], $localinv] == $BaseClass($Heap[aB$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aB$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aB$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation Types.P8$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this: ref, aObject$in: ref, aInt$in: ref, aA$in: ref, aJ$in: ref, aB$in: ref)
{
  var aObject: ref where $IsNotNull(aObject, RefArray(System.Object, 1)), aInt: ref where $IsNotNull(aInt, ValueArray(System.Int32, 1)), aA: ref where $IsNotNull(aA, RefArray(A, 1)), aJ: ref where $IsNotNull(aJ, RefArray(J, 1)), aB: ref where $IsNotNull(aB, RefArray(B, 1)), stack0o: ref;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    aObject := aObject$in;
    aInt := aInt$in;
    aA := aA$in;
    aJ := aJ$in;
    aB := aB$in;
    goto block24633;

  block24633:
    goto block24939;

  block24939:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(139,5)
    assert aObject != aJ;
    goto block25024;

  block25024:
    // ----- nop
    // ----- return
    return;

}



procedure Types.P9$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this: ref, aObject$in: ref where $IsNotNull(aObject$in, RefArray(System.Object, 1)), aInt$in: ref where $IsNotNull(aInt$in, ValueArray(System.Int32, 1)), aA$in: ref where $IsNotNull(aA$in, RefArray(A, 1)), aJ$in: ref where $IsNotNull(aJ$in, RefArray(J, 1)), aB$in: ref where $IsNotNull(aB$in, RefArray(B, 1)));
  free requires $Heap[aObject$in, $allocated] == true;
  free requires $Heap[aInt$in, $allocated] == true;
  free requires $Heap[aA$in, $allocated] == true;
  free requires $Heap[aJ$in, $allocated] == true;
  free requires $Heap[aB$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aObject$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aObject$in, $ownerRef], $inv] <: $Heap[aObject$in, $ownerFrame]) || $Heap[$Heap[aObject$in, $ownerRef], $localinv] == $BaseClass($Heap[aObject$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aObject$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aObject$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aInt$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aInt$in, $ownerRef], $inv] <: $Heap[aInt$in, $ownerFrame]) || $Heap[$Heap[aInt$in, $ownerRef], $localinv] == $BaseClass($Heap[aInt$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aInt$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aInt$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aA$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aA$in, $ownerRef], $inv] <: $Heap[aA$in, $ownerFrame]) || $Heap[$Heap[aA$in, $ownerRef], $localinv] == $BaseClass($Heap[aA$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aA$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aA$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aJ$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aJ$in, $ownerRef], $inv] <: $Heap[aJ$in, $ownerFrame]) || $Heap[$Heap[aJ$in, $ownerRef], $localinv] == $BaseClass($Heap[aJ$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aJ$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aJ$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[aB$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[aB$in, $ownerRef], $inv] <: $Heap[aB$in, $ownerFrame]) || $Heap[$Heap[aB$in, $ownerRef], $localinv] == $BaseClass($Heap[aB$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[aB$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[aB$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation Types.P9$System.Object.array$notnull$System.Int32.array$notnull$A.array$notnull$J.array$notnull$B.array$notnull(this: ref, aObject$in: ref, aInt$in: ref, aA$in: ref, aJ$in: ref, aB$in: ref)
{
  var aObject: ref where $IsNotNull(aObject, RefArray(System.Object, 1)), aInt: ref where $IsNotNull(aInt, ValueArray(System.Int32, 1)), aA: ref where $IsNotNull(aA, RefArray(A, 1)), aJ: ref where $IsNotNull(aJ, RefArray(J, 1)), aB: ref where $IsNotNull(aB, RefArray(B, 1)), stack0o: ref;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    aObject := aObject$in;
    aInt := aInt$in;
    aA := aA$in;
    aJ := aJ$in;
    aB := aB$in;
    goto block25687;

  block25687:
    goto block25993;

  block25993:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(143,5)
    assert aObject != aB;
    goto block26078;

  block26078:
    // ----- nop
    // ----- return
    return;

}



procedure Types.P10$J.array$notnull$B.array$notnull$F.array$notnull(this: ref, a$in: ref where $IsNotNull(a$in, RefArray(J, 1)), b$in: ref where $IsNotNull(b$in, RefArray(B, 1)), f$in: ref where $IsNotNull(f$in, RefArray(F, 1)));
  free requires $Heap[a$in, $allocated] == true;
  free requires $Heap[b$in, $allocated] == true;
  free requires $Heap[f$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[a$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[a$in, $ownerRef], $inv] <: $Heap[a$in, $ownerFrame]) || $Heap[$Heap[a$in, $ownerRef], $localinv] == $BaseClass($Heap[a$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[a$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[a$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[b$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[b$in, $ownerRef], $inv] <: $Heap[b$in, $ownerFrame]) || $Heap[$Heap[b$in, $ownerRef], $localinv] == $BaseClass($Heap[b$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[b$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[b$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires ($Heap[f$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[f$in, $ownerRef], $inv] <: $Heap[f$in, $ownerFrame]) || $Heap[$Heap[f$in, $ownerRef], $localinv] == $BaseClass($Heap[f$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[f$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[f$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
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



implementation Types.P10$J.array$notnull$B.array$notnull$F.array$notnull(this: ref, a$in: ref, b$in: ref, f$in: ref)
{
  var a: ref where $IsNotNull(a, RefArray(J, 1)), b: ref where $IsNotNull(b, RefArray(B, 1)), f: ref where $IsNotNull(f, RefArray(F, 1)), o: ref where $Is(o, System.Object), stack0o: ref;

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    a := a$in;
    b := b$in;
    f := f$in;
    goto block27098;

  block27098:
    goto block27302;

  block27302:
    // ----- nop
    // ----- copy  ----- Types.ssc(147,5)
    o := a;
    // ----- serialized AssertStatement  ----- Types.ssc(148,5)
    assert !$IsNotNull(o, RefArray(F, 1));
    goto block27489;

  block27489:
    // ----- nop
    // ----- copy  ----- Types.ssc(149,5)
    o := b;
    // ----- serialized AssertStatement  ----- Types.ssc(150,5)
    assert !$IsNotNull(o, RefArray(F, 1));
    goto block27676;

  block27676:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(151,5)
    assert a != f;
    goto block27761;

  block27761:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(152,5)
    assert b != f;
    goto block27846;

  block27846:
    // ----- nop
    // ----- return
    return;

}



axiom T <: T;

axiom $BaseClass(T) == System.Object;

axiom T <: $BaseClass(T) && AsDirectSubClass(T, $BaseClass(T)) == T;

axiom !$IsImmutable(T) && $AsMutable(T) == T;

axiom (forall $K: name :: { T <: $K } T <: $K <==> T == $K || System.Object <: $K);

procedure Types.Q$T$T(this: ref, t$in: ref where $Is(t$in, T), tn$in: ref where $Is(tn$in, T));
  free requires $Heap[t$in, $allocated] == true;
  free requires $Heap[tn$in, $allocated] == true;
  // user-declared preconditions
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == Types && $Heap[this, $localinv] == $typeof(this);
  requires t$in == null || (($Heap[t$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[t$in, $ownerRef], $inv] <: $Heap[t$in, $ownerFrame]) || $Heap[$Heap[t$in, $ownerRef], $localinv] == $BaseClass($Heap[t$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[t$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[t$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
  requires tn$in == null || (($Heap[tn$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[tn$in, $ownerRef], $inv] <: $Heap[tn$in, $ownerFrame]) || $Heap[$Heap[tn$in, $ownerRef], $localinv] == $BaseClass($Heap[tn$in, $ownerFrame])) && $Heap[tn$in, $inv] == $typeof(tn$in) && $Heap[tn$in, $localinv] == $typeof(tn$in));
  requires tn$in != t$in;
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



implementation Types.Q$T$T(this: ref, t$in: ref, tn$in: ref)
{
  var t: ref where $Is(t, T), tn: ref where $Is(tn, T), stack0o: ref, stack0b: bool, local11: ref where $Is(local11, T), stack1s: struct, stack1o: ref, temp0: exposeVersionType, n: ref where $Is(n, T);

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    t := t$in;
    tn := tn$in;
    goto block31773;

  block31773:
    goto block32147;

  block32147:
    // ----- nop
    stack0o := null;
    // ----- binary operator  ----- Types.ssc(162,5)
    // ----- branch  ----- Types.ssc(162,5)
    goto true32147to32946, false32147to32164;

  true32147to32946:
    assume t == stack0o;
    goto block32946;

  false32147to32164:
    assume t != stack0o;
    goto block32164;

  block32946:
    stack0o := null;
    // ----- binary operator  ----- Types.ssc(177,5)
    // ----- branch  ----- Types.ssc(177,5)
    goto true32946to33082, false32946to32963;

  block32164:
    // ----- serialized AssertStatement  ----- Types.ssc(163,7)
    assert $Heap[t, T.x] == $Heap[t, T.x];
    goto block32249;

  true32946to33082:
    assume t == stack0o;
    goto block33082;

  false32946to32963:
    assume t != stack0o;
    goto block32963;

  block33082:
    stack0o := null;
    // ----- binary operator  ----- Types.ssc(183,5)
    // ----- branch  ----- Types.ssc(183,5)
    goto true33082to33881, false33082to33099;

  block32963:
    // ----- serialized AssumeStatement  ----- Types.ssc(178,7)
    assume ($Heap[t, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[t, $ownerRef], $inv] <: $Heap[t, $ownerFrame]) || $Heap[$Heap[t, $ownerRef], $localinv] == $BaseClass($Heap[t, $ownerFrame])) && $Heap[t, $inv] == T && $Heap[t, $localinv] == $typeof(t);
    goto block33048;

  block32249:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(164,7)
    assert $IsNotNull($Heap[t, T.y], D);
    goto block32334;

  true33082to33881:
    assume t == stack0o;
    goto block33881;

  false33082to33099:
    assume t != stack0o;
    goto block33099;

  block33881:
    stack0o := null;
    // ----- binary operator  ----- Types.ssc(198,5)
    // ----- branch  ----- Types.ssc(198,5)
    goto true33881to33915, false33881to33898;

  block33099:
    // ----- serialized AssertStatement  ----- Types.ssc(184,7)
    assert $Heap[t, T.x] == $Heap[t, T.x];
    goto block33184;

  block32334:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(165,7)
    assert $IsNotNull($Heap[t, T.y], D);
    goto block32419;

  block33048:
    // ----- nop
    // ----- copy  ----- Types.ssc(179,15)
    local11 := t;
    // ----- copy  ----- Types.ssc(179,15)
    stack0o := local11;
    // ----- load token  ----- Types.ssc(179,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, T);
    // ----- statically resolved GetTypeFromHandle call  ----- Types.ssc(179,15)
    stack1o := TypeObject(T);
    // ----- local unpack  ----- Types.ssc(179,15)
    assert stack0o != null;
    assert ($Heap[stack0o, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[stack0o, $ownerRef], $inv] <: $Heap[stack0o, $ownerFrame]) || $Heap[$Heap[stack0o, $ownerRef], $localinv] == $BaseClass($Heap[stack0o, $ownerFrame])) && $Heap[stack0o, $inv] <: T && $Heap[stack0o, $localinv] == $typeof(stack0o);
    $Heap[stack0o, $localinv] := System.Object;
    havoc temp0;
    $Heap[stack0o, $exposeVersion] := temp0;
    assume IsHeap($Heap);
    goto block33065;

  true33881to33915:
    assume t == stack0o;
    goto block33915;

  false33881to33898:
    assume t != stack0o;
    goto block33898;

  block33915:
    stack0o := null;
    // ----- binary operator  ----- Types.ssc(203,5)
    // ----- branch  ----- Types.ssc(203,5)
    goto true33915to34714, false33915to33932;

  block33898:
    // ----- call  ----- Types.ssc(199,7)
    assert t != null;
    call T.M(t);
    goto block33915;

  block32419:
    // ----- nop
    // ----- load field  ----- Types.ssc(166,7)
    assert t != null;
    stack0o := $Heap[t, T.next];
    // ----- is instance  ----- Types.ssc(166,7)
    stack0o := $As(stack0o, T);
    // ----- unary operator  ----- Types.ssc(166,7)
    // ----- branch  ----- Types.ssc(166,7)
    goto true32419to32827, false32419to32436;

  true32419to32827:
    assume stack0o == null;
    goto block32827;

  false32419to32436:
    assume stack0o != null;
    goto block32436;

  block32827:
    // ----- serialized AssertStatement  ----- Types.ssc(173,7)
    assert $Heap[ClassRepr(T), T.g] == null || $IsNotNull($Heap[ClassRepr(T), T.g], C);
    goto block32929;

  block32436:
    // ----- serialized AssertStatement  ----- Types.ssc(167,9)
    assert $Heap[t, T.next] != null;
    goto block32521;

  block33065:
    // ----- store field  ----- Types.ssc(179,20)
    assert t != null;
    assert !($Heap[t, $inv] <: T) || $Heap[t, $localinv] == System.Object;
    $Heap[t, T.next] := tn;
    assume IsHeap($Heap);
    // ----- branch
    goto block34748;

  true33915to34714:
    assume t == stack0o;
    goto block34714;

  false33915to33932:
    assume t != stack0o;
    goto block33932;

  block34714:
    // ----- return
    return;

  block33932:
    // ----- serialized AssertStatement  ----- Types.ssc(204,7)
    assert $Heap[t, T.x] == $Heap[t, T.x];
    goto block34017;

  block33184:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(185,7)
    assert $IsNotNull($Heap[t, T.y], D);
    goto block33269;

  block34748:
    // ----- copy  ----- Types.ssc(179,33)
    stack0o := local11;
    // ----- load token  ----- Types.ssc(179,33)
    havoc stack1s;
    assume $IsTokenForType(stack1s, T);
    // ----- statically resolved GetTypeFromHandle call  ----- Types.ssc(179,33)
    stack1o := TypeObject(T);
    // ----- local pack  ----- Types.ssc(179,33)
    assert stack0o != null;
    assert $Heap[stack0o, $localinv] == System.Object;
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == stack0o && $Heap[$p, $ownerFrame] == T ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[stack0o, $localinv] := $typeof(stack0o);
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block33082;

  block33269:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(186,7)
    assert $IsNotNull($Heap[t, T.y], D);
    goto block33354;

  block32521:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(168,9)
    assert $IsNotNull($Heap[t, T.next], System.Object);
    goto block32606;

  block32929:
    // ----- nop
    goto block32946;

  block34017:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(205,7)
    assert $IsNotNull($Heap[t, T.y], D);
    goto block34102;

  block33354:
    // ----- nop
    // ----- load field  ----- Types.ssc(187,7)
    assert t != null;
    stack0o := $Heap[t, T.next];
    // ----- is instance  ----- Types.ssc(187,7)
    stack0o := $As(stack0o, T);
    // ----- unary operator  ----- Types.ssc(187,7)
    // ----- branch  ----- Types.ssc(187,7)
    goto true33354to33762, false33354to33371;

  true33354to33762:
    assume stack0o == null;
    goto block33762;

  false33354to33371:
    assume stack0o != null;
    goto block33371;

  block33762:
    // ----- serialized AssertStatement  ----- Types.ssc(194,7)
    assert $Heap[ClassRepr(T), T.g] == null || $IsNotNull($Heap[ClassRepr(T), T.g], C);
    goto block33864;

  block33371:
    // ----- serialized AssertStatement  ----- Types.ssc(188,9)
    assert $Heap[t, T.next] != null;
    goto block33456;

  block32606:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(169,9)
    assert $IsNotNull($Heap[$Heap[t, T.next], T.y], D);
    goto block32691;

  block34102:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(206,7)
    assert $IsNotNull($Heap[t, T.y], D);
    goto block34187;

  block32691:
    // ----- nop
    // ----- load field  ----- Types.ssc(170,9)
    assert t != null;
    stack0o := $Heap[t, T.next];
    // ----- load field  ----- Types.ssc(170,9)
    assert stack0o != null;
    n := $Heap[stack0o, T.next];
    // ----- serialized AssertStatement  ----- Types.ssc(171,9)
    assert n == null || $IsNotNull($Heap[n, T.x], D) || $Heap[n, T.x] == null;
    goto block32810;

  block34187:
    // ----- nop
    // ----- load field  ----- Types.ssc(207,7)
    assert t != null;
    stack0o := $Heap[t, T.next];
    // ----- is instance  ----- Types.ssc(207,7)
    stack0o := $As(stack0o, T);
    // ----- unary operator  ----- Types.ssc(207,7)
    // ----- branch  ----- Types.ssc(207,7)
    goto true34187to34595, false34187to34204;

  true34187to34595:
    assume stack0o == null;
    goto block34595;

  false34187to34204:
    assume stack0o != null;
    goto block34204;

  block34595:
    // ----- serialized AssertStatement  ----- Types.ssc(214,7)
    assert $Heap[ClassRepr(T), T.g] == null || $IsNotNull($Heap[ClassRepr(T), T.g], C);
    goto block34697;

  block34204:
    // ----- serialized AssertStatement  ----- Types.ssc(208,9)
    assert $Heap[t, T.next] != null;
    goto block34289;

  block33456:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(189,9)
    assert $IsNotNull($Heap[t, T.next], System.Object);
    goto block33541;

  block33864:
    // ----- nop
    goto block33881;

  block32810:
    // ----- nop
    goto block32827;

  block33541:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(190,9)
    assert $IsNotNull($Heap[$Heap[t, T.next], T.y], D);
    goto block33626;

  block34697:
    // ----- nop
    goto block34714;

  block34289:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(209,9)
    assert $IsNotNull($Heap[t, T.next], System.Object);
    goto block34374;

  block33626:
    // ----- nop
    // ----- load field  ----- Types.ssc(191,9)
    assert t != null;
    stack0o := $Heap[t, T.next];
    // ----- load field  ----- Types.ssc(191,9)
    assert stack0o != null;
    n := $Heap[stack0o, T.next];
    // ----- serialized AssertStatement  ----- Types.ssc(192,9)
    assert n == null || $IsNotNull($Heap[n, T.x], D) || $Heap[n, T.x] == null;
    goto block33745;

  block34374:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(210,9)
    assert $IsNotNull($Heap[$Heap[t, T.next], T.y], D);
    goto block34459;

  block33745:
    // ----- nop
    goto block33762;

  block34459:
    // ----- nop
    // ----- load field  ----- Types.ssc(211,9)
    assert t != null;
    stack0o := $Heap[t, T.next];
    // ----- load field  ----- Types.ssc(211,9)
    assert stack0o != null;
    n := $Heap[stack0o, T.next];
    // ----- serialized AssertStatement  ----- Types.ssc(212,9)
    assert n == null || $IsNotNull($Heap[n, T.x], D) || $Heap[n, T.x] == null;
    goto block34578;

  block34578:
    // ----- nop
    goto block34595;

}



axiom System.Type <: System.Type;

axiom System.Reflection.MemberInfo <: System.Reflection.MemberInfo;

axiom $BaseClass(System.Reflection.MemberInfo) == System.Object;

axiom System.Reflection.MemberInfo <: $BaseClass(System.Reflection.MemberInfo) && AsDirectSubClass(System.Reflection.MemberInfo, $BaseClass(System.Reflection.MemberInfo)) == System.Reflection.MemberInfo;

axiom $IsImmutable(System.Reflection.MemberInfo) && $AsImmutable(System.Reflection.MemberInfo) == System.Reflection.MemberInfo;

axiom System.Reflection.ICustomAttributeProvider <: System.Object;

axiom (forall $K: name :: { System.Reflection.ICustomAttributeProvider <: $K } System.Reflection.ICustomAttributeProvider <: $K <==> System.Reflection.ICustomAttributeProvider == $K || System.Object == $K);

axiom $IsMemberlessType(System.Reflection.ICustomAttributeProvider);

axiom System.Reflection.MemberInfo <: System.Reflection.ICustomAttributeProvider;

axiom System.Runtime.InteropServices._MemberInfo <: System.Object;

axiom (forall $K: name :: { System.Runtime.InteropServices._MemberInfo <: $K } System.Runtime.InteropServices._MemberInfo <: $K <==> System.Runtime.InteropServices._MemberInfo == $K || System.Object == $K);

axiom $IsMemberlessType(System.Runtime.InteropServices._MemberInfo);

axiom System.Reflection.MemberInfo <: System.Runtime.InteropServices._MemberInfo;

axiom (forall $K: name :: { System.Reflection.MemberInfo <: $K } System.Reflection.MemberInfo <: $K <==> System.Reflection.MemberInfo == $K || System.Object <: $K || System.Reflection.ICustomAttributeProvider <: $K || System.Runtime.InteropServices._MemberInfo <: $K);

axiom $IsMemberlessType(System.Reflection.MemberInfo);

axiom $BaseClass(System.Type) == System.Reflection.MemberInfo;

axiom System.Type <: $BaseClass(System.Type) && AsDirectSubClass(System.Type, $BaseClass(System.Type)) == System.Type;

axiom $IsImmutable(System.Type) && $AsImmutable(System.Type) == System.Type;

axiom System.Runtime.InteropServices._Type <: System.Object;

axiom (forall $K: name :: { System.Runtime.InteropServices._Type <: $K } System.Runtime.InteropServices._Type <: $K <==> System.Runtime.InteropServices._Type == $K || System.Object == $K);

axiom $IsMemberlessType(System.Runtime.InteropServices._Type);

axiom System.Type <: System.Runtime.InteropServices._Type;

axiom System.Reflection.IReflect <: System.Object;

axiom (forall $K: name :: { System.Reflection.IReflect <: $K } System.Reflection.IReflect <: $K <==> System.Reflection.IReflect == $K || System.Object == $K);

axiom $IsMemberlessType(System.Reflection.IReflect);

axiom System.Type <: System.Reflection.IReflect;

axiom (forall $K: name :: { System.Type <: $K } System.Type <: $K <==> System.Type == $K || System.Reflection.MemberInfo <: $K || System.Runtime.InteropServices._Type <: $K || System.Reflection.IReflect <: $K);

axiom $IsMemberlessType(System.Type);

procedure T.M(this: ref);
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



implementation Types..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, Types);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block37876;

  block37876:
    goto block37893;

  block37893:
    // ----- call  ----- Types.ssc(1,21)
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



procedure A..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == A && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(A <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation A..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, A);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block38063;

  block38063:
    goto block38080;

  block38080:
    // ----- call  ----- Types.ssc(219,14)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == A ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := A;
    assume IsHeap($Heap);
    return;

}



procedure B..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == B && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(B <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation B..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, B);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block38250;

  block38250:
    goto block38267;

  block38267:
    // ----- call  ----- Types.ssc(221,14)
    assert this != null;
    call A..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == A && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == B ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := B;
    assume IsHeap($Heap);
    return;

}



procedure C..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == C && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(C <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation C..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, C);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block38437;

  block38437:
    goto block38454;

  block38454:
    // ----- call  ----- Types.ssc(222,14)
    assert this != null;
    call B..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == B && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == C ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := C;
    assume IsHeap($Heap);
    return;

}



procedure D..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == D && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(D <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation D..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, D);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block38624;

  block38624:
    goto block38641;

  block38641:
    // ----- call  ----- Types.ssc(223,14)
    assert this != null;
    call A..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == A && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == D ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := D;
    assume IsHeap($Heap);
    return;

}



procedure F..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == F && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(F <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation F..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, F);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block38811;

  block38811:
    goto block38828;

  block38828:
    // ----- call  ----- Types.ssc(224,21)
    assert this != null;
    call A..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == A && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == F ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := F;
    assume IsHeap($Heap);
    return;

}



procedure T..ctor$D$notnull(this: ref, d$in: ref where $IsNotNull(d$in, D));
  free requires $Heap[d$in, $allocated] == true;
  requires ($Heap[d$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[d$in, $ownerRef], $inv] <: $Heap[d$in, $ownerFrame]) || $Heap[$Heap[d$in, $ownerRef], $localinv] == $BaseClass($Heap[d$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[d$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[d$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == T && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(T <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation T..ctor$D$notnull(this: ref, d$in: ref)
{
  var d: ref where $IsNotNull(d, D);

  entry:
    assume $IsNotNull(this, T);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    d := d$in;
    assume $Heap[this, T.x] == null;
    assume $Heap[this, T.next] == null;
    goto block39083;

  block39083:
    goto block39185;

  block39185:
    // ----- nop
    // ----- store field  ----- Types.ssc(238,5)
    assert this != null;
    assert !($Heap[this, $inv] <: T) || $Heap[this, $localinv] == System.Object;
    $Heap[this, T.y] := d;
    assume IsHeap($Heap);
    // ----- call  ----- Types.ssc(239,5)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == T ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := T;
    assume IsHeap($Heap);
    return;

}



implementation T.M(this: ref)
{

  entry:
    assume $IsNotNull(this, T);
    assume $Heap[this, $allocated] == true;
    goto block39423;

  block39423:
    goto block39440;

  block39440:
    // ----- return  ----- Types.ssc(242,20)
    return;

}



axiom MoreTypes <: MoreTypes;

axiom $BaseClass(MoreTypes) == System.Object;

axiom MoreTypes <: $BaseClass(MoreTypes) && AsDirectSubClass(MoreTypes, $BaseClass(MoreTypes)) == MoreTypes;

axiom !$IsImmutable(MoreTypes) && $AsMutable(MoreTypes) == MoreTypes;

axiom (forall $K: name :: { MoreTypes <: $K } MoreTypes <: $K <==> MoreTypes == $K || System.Object <: $K);

procedure MoreTypes.M$System.Object(this: ref, t$in: ref where $Is(t$in, System.Object));
  free requires $Heap[t$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires t$in == null || (($Heap[t$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[t$in, $ownerRef], $inv] <: $Heap[t$in, $ownerFrame]) || $Heap[$Heap[t$in, $ownerRef], $localinv] == $BaseClass($Heap[t$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[t$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[t$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
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



implementation MoreTypes.M$System.Object(this: ref, t$in: ref)
{
  var t: ref where $Is(t, System.Object), stack0o: ref;

  entry:
    assume $IsNotNull(this, MoreTypes);
    assume $Heap[this, $allocated] == true;
    t := t$in;
    goto block39763;

  block39763:
    goto block39780;

  block39780:
    // ----- serialized AssumeStatement  ----- Types.ssc(247,5)
    assume $IsNotNull(t, MoreTypes);
    goto block39865;

  block39865:
    // ----- nop
    // ----- serialized AssertStatement  ----- Types.ssc(248,5)
    assert t != null;
    goto block39950;

  block39950:
    // ----- nop
    // ----- return  ----- Types.ssc(249,3)
    return;

}



procedure MoreTypes.N$System.Object(this: ref, t$in: ref where $Is(t$in, System.Object));
  free requires $Heap[t$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires t$in == null || (($Heap[t$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[t$in, $ownerRef], $inv] <: $Heap[t$in, $ownerFrame]) || $Heap[$Heap[t$in, $ownerRef], $localinv] == $BaseClass($Heap[t$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[t$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[t$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
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



implementation MoreTypes.N$System.Object(this: ref, t$in: ref)
{
  var t: ref where $Is(t, System.Object), stack0o: ref, stack0b: bool;

  entry:
    assume $IsNotNull(this, MoreTypes);
    assume $Heap[this, $allocated] == true;
    t := t$in;
    goto block40392;

  block40392:
    goto block40409;

  block40409:
    // ----- is instance  ----- Types.ssc(252,5)
    stack0o := $As(t, MoreTypes);
    // ----- unary operator  ----- Types.ssc(252,5)
    // ----- branch  ----- Types.ssc(252,5)
    goto true40409to40528, false40409to40426;

  true40409to40528:
    assume stack0o == null;
    goto block40528;

  false40409to40426:
    assume stack0o != null;
    goto block40426;

  block40528:
    // ----- return  ----- Types.ssc(255,3)
    return;

  block40426:
    // ----- serialized AssertStatement  ----- Types.ssc(253,7)
    assert t != null;
    goto block40511;

  block40511:
    // ----- nop
    goto block40528;

}



procedure MoreTypes.P$System.Object(this: ref, t$in: ref where $Is(t$in, System.Object));
  free requires $Heap[t$in, $allocated] == true;
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  requires t$in == null || (($Heap[t$in, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[t$in, $ownerRef], $inv] <: $Heap[t$in, $ownerFrame]) || $Heap[$Heap[t$in, $ownerRef], $localinv] == $BaseClass($Heap[t$in, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[t$in, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[t$in, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc)));
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



implementation MoreTypes.P$System.Object(this: ref, t$in: ref)
{
  var t: ref where $Is(t, System.Object), stack0o: ref, stack1o: ref, stack0b: bool, b: bool where true;

  entry:
    assume $IsNotNull(this, MoreTypes);
    assume $Heap[this, $allocated] == true;
    t := t$in;
    goto block40987;

  block40987:
    goto block41004;

  block41004:
    // ----- is instance  ----- Types.ssc(258,5)
    stack0o := $As(t, MoreTypes);
    stack1o := null;
    // ----- binary operator  ----- Types.ssc(258,5)
    // ----- branch  ----- Types.ssc(258,5)
    goto true41004to41038, false41004to41021;

  true41004to41038:
    assume stack0o != stack1o;
    goto block41038;

  false41004to41021:
    assume stack0o == stack1o;
    goto block41021;

  block41038:
    // ----- load constant 1
    stack0b := true;
    goto block41055;

  block41021:
    // ----- load constant 0
    stack0b := false;
    // ----- branch
    goto block41055;

  block41055:
    // ----- copy
    b := stack0b;
    // ----- copy  ----- Types.ssc(259,5)
    stack0b := b;
    // ----- unary operator  ----- Types.ssc(259,5)
    // ----- branch  ----- Types.ssc(259,5)
    goto true41055to41174, false41055to41072;

  true41055to41174:
    assume !stack0b;
    goto block41174;

  false41055to41072:
    assume stack0b;
    goto block41072;

  block41174:
    // ----- return  ----- Types.ssc(262,3)
    return;

  block41072:
    // ----- serialized AssertStatement  ----- Types.ssc(260,7)
    assert t != null;
    goto block41157;

  block41157:
    // ----- nop
    goto block41174;

}



procedure MoreTypes..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == MoreTypes && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(MoreTypes <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation MoreTypes..ctor(this: ref)
{

  entry:
    assume $IsNotNull(this, MoreTypes);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    goto block41599;

  block41599:
    goto block41616;

  block41616:
    // ----- call  ----- Types.ssc(245,14)
    assert this != null;
    call System.Object..ctor(this);
    // ----- return
    assert this != null;
    assert $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == this && $Heap[$p, $ownerFrame] == MoreTypes ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[this, $inv] := MoreTypes;
    assume IsHeap($Heap);
    return;

}


