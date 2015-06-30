// Spec# Program Verifier Version 0.80, Copyright (c) 2003-2006, Microsoft.
// Command Line Options: /nologo -nologo /nologo /prover:blank /nologo /print:boogie_tmp.@TIME@.bpl /nologo /proverLog:boogie_tmp.@TIME@.simplify /nologo /nologo /nologo /nologo /nologo /modifiesOnLoop Finally

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

const ReturnFinally.x: <int>name;

const ReturnFinally.y: <int>name;

const System.Collections.IEnumerable: name;

const System.IEquatable`1...System.String: name;

const Microsoft.Contracts.ICheckedException: name;

const ReturnFinally: name;

const System.Runtime.Serialization.ISerializable: name;

const System.Runtime.InteropServices._Type: name;

const System.Exception: name;

const System.IComparable: name;

const System.Reflection.MemberInfo: name;

const System.Runtime.InteropServices._MemberInfo: name;

const System.Collections.Generic.IEnumerable`1...System.Char: name;

const System.Runtime.InteropServices._Exception: name;

const Microsoft.Contracts.ObjectInvariantException: name;

const System.Boolean: name;

const System.IComparable`1...System.String: name;

const System.Reflection.ICustomAttributeProvider: name;

const Microsoft.Contracts.GuardException: name;

const System.ICloneable: name;

const System.IConvertible: name;

const System.Reflection.IReflect: name;

axiom !IsStaticField(ReturnFinally.y);

axiom IsDirectlyModifiableField(ReturnFinally.y);

axiom DeclType(ReturnFinally.y) == ReturnFinally;

axiom AsRangeField(ReturnFinally.y, System.Int32) == ReturnFinally.y;

axiom IsStaticField(ReturnFinally.x);

axiom IsDirectlyModifiableField(ReturnFinally.x);

axiom DeclType(ReturnFinally.x) == ReturnFinally;

axiom AsRangeField(ReturnFinally.x, System.Int32) == ReturnFinally.x;

axiom ReturnFinally <: ReturnFinally;

axiom $BaseClass(ReturnFinally) == System.Object;

axiom ReturnFinally <: $BaseClass(ReturnFinally) && AsDirectSubClass(ReturnFinally, $BaseClass(ReturnFinally)) == ReturnFinally;

axiom !$IsImmutable(ReturnFinally) && $AsMutable(ReturnFinally) == ReturnFinally;

axiom (forall $oi: ref, $h: [ref,<x>name]x :: { $h[$oi, $inv] <: ReturnFinally } IsHeap($h) && $h[$oi, $inv] <: ReturnFinally && $h[$oi, $localinv] != System.Object ==> 0 <= $h[$oi, ReturnFinally.y]);

axiom (forall $U: name :: { $U <: System.Boolean } $U <: System.Boolean ==> $U == System.Boolean);

procedure ReturnFinally.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool where true) returns ($result: bool where true);
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



implementation ReturnFinally.SpecSharp.CheckInvariant$System.Boolean(this: ref, throwException$in: bool) returns ($result: bool)
{
  var throwException: bool where true, stack0i: int, stack1i: int, stack0b: bool, return.value: bool where true, stack50000o: ref, stack0o: ref, SS$Display.Return.Local: bool where true;

  entry:
    assume $IsNotNull(this, ReturnFinally);
    assume $Heap[this, $allocated] == true;
    throwException := throwException$in;
    goto block4386;

  block4386:
    goto block4403;

  block4403:
    // ----- load constant 0  ----- Finally.ssc(5,13)
    stack0i := 0;
    // ----- load field  ----- Finally.ssc(5,18)
    assert this != null;
    stack1i := $Heap[this, ReturnFinally.y];
    // ----- binary operator  ----- Finally.ssc(5,13)
    // ----- branch
    goto true4403to4522, false4403to4420;

  true4403to4522:
    assume stack0i <= stack1i;
    goto block4522;

  false4403to4420:
    assume stack0i > stack1i;
    goto block4420;

  block4522:
    goto block4539;

  block4420:
    // ----- copy
    stack0b := throwException;
    // ----- unary operator
    // ----- branch
    goto true4420to4471, false4420to4437;

  true4420to4471:
    assume !stack0b;
    goto block4471;

  false4420to4437:
    assume stack0b;
    goto block4437;

  block4471:
    // ----- load constant False
    return.value := false;
    // ----- branch
    goto block4573;

  block4437:
    assume false;
    // ----- new object  ----- Finally.ssc(5,3)
    havoc stack50000o;
    assume $Heap[stack50000o, $allocated] == false && stack50000o != null && $typeof(stack50000o) == Microsoft.Contracts.ObjectInvariantException;
    assume $Heap[stack50000o, $ownerRef] == stack50000o && $Heap[stack50000o, $ownerFrame] == $PeerGroupPlaceholder;
    $Heap[stack50000o, $allocated] := true;
    // ----- call  ----- Finally.ssc(5,3)
    assert stack50000o != null;
    call Microsoft.Contracts.ObjectInvariantException..ctor(stack50000o);
    // ----- copy  ----- Finally.ssc(5,3)
    stack0o := stack50000o;
    // ----- throw  ----- Finally.ssc(5,3)
    assert stack0o != null;
    assume false;
    return;

  block4539:
    goto block4556;

  block4573:
    goto block4590;

  block4556:
    // ----- load constant True
    return.value := true;
    // ----- branch
    goto block4573;

  block4590:
    // ----- copy
    SS$Display.Return.Local := return.value;
    // ----- copy
    stack0b := return.value;
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



procedure ReturnFinally.TryFinally0(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // user-declared postconditions
  ensures $Heap[ClassRepr(ReturnFinally), ReturnFinally.x] == 6;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != ClassRepr(ReturnFinally) || $f != ReturnFinally.x) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation ReturnFinally.TryFinally0(this: ref)
{
  var stack0i: int;

  entry:
    assume $IsNotNull(this, ReturnFinally);
    assume $Heap[this, $allocated] == true;
    goto block5389;

  block5389:
    goto block5644;

  block5644:
    // ----- nop
    goto block5661;

  block5661:
    // ----- branch
    goto block5967;

  block5967:
    // ----- load constant 10  ----- Finally.ssc(13,11)
    stack0i := 10;
    // ----- store field  ----- Finally.ssc(13,7)
    $Heap[ClassRepr(ReturnFinally), ReturnFinally.x] := stack0i;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block5712;

  block5712:
    goto block5729;

  block5729:
    goto block5933;

  block5933:
    // ----- nop
    goto block5950;

  block5950:
    // ----- return
    return;

}



procedure ReturnFinally.TryFinally1(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // user-declared postconditions
  ensures $Heap[ClassRepr(ReturnFinally), ReturnFinally.x] == 6;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != ClassRepr(ReturnFinally) || $f != ReturnFinally.x) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation ReturnFinally.TryFinally1(this: ref)
{
  var stack0i: int;

  entry:
    assume $IsNotNull(this, ReturnFinally);
    assume $Heap[this, $allocated] == true;
    goto block6749;

  block6749:
    goto block7004;

  block7004:
    // ----- nop
    goto block7021;

  block7021:
    // ----- load constant 6  ----- Finally.ssc(22,11)
    stack0i := 6;
    // ----- store field  ----- Finally.ssc(22,7)
    $Heap[ClassRepr(ReturnFinally), ReturnFinally.x] := stack0i;
    assume IsHeap($Heap);
    // ----- branch
    goto block7327;

  block7327:
    // ----- load constant 10  ----- Finally.ssc(24,11)
    stack0i := 10;
    // ----- store field  ----- Finally.ssc(24,7)
    $Heap[ClassRepr(ReturnFinally), ReturnFinally.x] := stack0i;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block7072;

  block7072:
    goto block7089;

  block7089:
    goto block7293;

  block7293:
    // ----- nop
    goto block7310;

  block7310:
    // ----- return
    return;

}



procedure ReturnFinally.TryFinally2(this: ref);
  requires ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && (forall $pc: ref :: $pc != null && $Heap[$pc, $allocated] == true && $Heap[$pc, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$pc, $ownerFrame] == $Heap[this, $ownerFrame] ==> $Heap[$pc, $inv] == $typeof($pc) && $Heap[$pc, $localinv] == $typeof($pc));
  free requires $BeingConstructed == null;
  modifies $Heap;
  // user-declared postconditions
  ensures $Heap[ClassRepr(ReturnFinally), ReturnFinally.x] == 6;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != ClassRepr(ReturnFinally) || $f != ReturnFinally.x) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation ReturnFinally.TryFinally2(this: ref)
{
  var stack0i: int;

  entry:
    assume $IsNotNull(this, ReturnFinally);
    assume $Heap[this, $allocated] == true;
    goto block8075;

  block8075:
    goto block8330;

  block8330:
    // ----- nop
    goto block8347;

  block8347:
    // ----- load constant 10  ----- Finally.ssc(33,11)
    stack0i := 10;
    // ----- store field  ----- Finally.ssc(33,7)
    $Heap[ClassRepr(ReturnFinally), ReturnFinally.x] := stack0i;
    assume IsHeap($Heap);
    // ----- branch
    goto block8653;

  block8653:
    // ----- load constant 6  ----- Finally.ssc(35,11)
    stack0i := 6;
    // ----- store field  ----- Finally.ssc(35,7)
    $Heap[ClassRepr(ReturnFinally), ReturnFinally.x] := stack0i;
    assume IsHeap($Heap);
    // ----- nop
    // ----- branch
    goto block8398;

  block8398:
    goto block8415;

  block8415:
    goto block8619;

  block8619:
    // ----- nop
    goto block8636;

  block8636:
    // ----- return
    return;

}



procedure ReturnFinally.TryFinally3(this: ref);
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



implementation ReturnFinally.TryFinally3(this: ref)
{
  var stack0o: ref;

  entry:
    assume $IsNotNull(this, ReturnFinally);
    assume $Heap[this, $allocated] == true;
    goto block9503;

  block9503:
    goto block9758;

  block9758:
    // ----- nop
    goto block9775;

  block9775:
    // ----- branch
    goto block9877;

  block9877:
    // ----- serialized AssertStatement  ----- Finally.ssc(43,7)
    assert true;
    goto block9945;

  block9945:
    // ----- nop
    goto block9962;

  block9962:
    // ----- nop
    // ----- branch
    goto block9826;

  block9826:
    goto block9843;

  block9843:
    goto block9860;

  block9860:
    // ----- return
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

procedure ReturnFinally.Expose0$System.Boolean(this: ref, b$in: bool where true);
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || $f != ReturnFinally.y) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation ReturnFinally.Expose0$System.Boolean(this: ref, b$in: bool)
{
  var b: bool where true, temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local11900: ref where $Is(local11900, System.Exception), stack0i: int, stack0b: bool, stack0o: ref, stack0s: struct;

  entry:
    assume $IsNotNull(this, ReturnFinally);
    assume $Heap[this, $allocated] == true;
    b := b$in;
    goto block10829;

  block10829:
    goto block11084;

  block11084:
    // ----- nop
    goto block11101;

  block11101:
    // ----- FrameGuard processing  ----- Finally.ssc(50,13)
    temp0 := this;
    // ----- load token  ----- Finally.ssc(50,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, ReturnFinally);
    // ----- statically resolved GetTypeFromHandle call  ----- Finally.ssc(50,13)
    stack1o := TypeObject(ReturnFinally);
    // ----- local unpack  ----- Finally.ssc(50,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: ReturnFinally && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local11900 := null;
    goto block11118;

  block11118:
    // ----- load constant -4  ----- Finally.ssc(51,16)
    stack0i := -4;
    // ----- store field  ----- Finally.ssc(51,7)
    assert this != null;
    assert !($Heap[this, $inv] <: ReturnFinally) || $Heap[this, $localinv] == System.Object;
    $Heap[this, ReturnFinally.y] := stack0i;
    assume IsHeap($Heap);
    goto block11135;

  block11135:
    // ----- copy  ----- Finally.ssc(52,11)
    stack0b := b;
    // ----- unary operator  ----- Finally.ssc(52,11)
    // ----- branch  ----- Finally.ssc(52,7)
    goto true11135to11169, false11135to11152;

  true11135to11169:
    assume !stack0b;
    goto block11169;

  false11135to11152:
    assume stack0b;
    goto block11152;

  block11169:
    goto block11186;

  block11152:
    // ----- branch  ----- Finally.ssc(52,16)
    goto block11373;

  block11186:
    goto block11203;

  block11373:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true11373to11475, false11373to11390;

  true11373to11475:
    assume local11900 == stack0o;
    goto block11475;

  false11373to11390:
    assume local11900 != stack0o;
    goto block11390;

  block11475:
    goto block11492;

  block11390:
    // ----- is instance
    // ----- branch
    goto true11390to11475, false11390to11407;

  block11203:
    // ----- load constant 2  ----- Finally.ssc(53,16)
    stack0i := 2;
    // ----- store field  ----- Finally.ssc(53,7)
    assert this != null;
    assert !($Heap[this, $inv] <: ReturnFinally) || $Heap[this, $localinv] == System.Object;
    $Heap[this, ReturnFinally.y] := stack0i;
    assume IsHeap($Heap);
    // ----- branch
    goto block11509;

  true11390to11475:
    assume $As(local11900, Microsoft.Contracts.ICheckedException) != null;
    goto block11475;

  false11390to11407:
    assume $As(local11900, Microsoft.Contracts.ICheckedException) == null;
    goto block11407;

  block11407:
    // ----- branch
    goto block11424;

  block11509:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true11509to11611, false11509to11526;

  true11509to11611:
    assume local11900 == stack0o;
    goto block11611;

  false11509to11526:
    assume local11900 != stack0o;
    goto block11526;

  block11611:
    goto block11628;

  block11526:
    // ----- is instance
    // ----- branch
    goto true11526to11611, false11526to11543;

  block11492:
    // ----- load token  ----- Finally.ssc(54,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, ReturnFinally);
    // ----- statically resolved GetTypeFromHandle call  ----- Finally.ssc(54,5)
    stack0o := TypeObject(ReturnFinally);
    // ----- local pack  ----- Finally.ssc(54,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, ReturnFinally.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == ReturnFinally ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block11424;

  true11526to11611:
    assume $As(local11900, Microsoft.Contracts.ICheckedException) != null;
    goto block11611;

  false11526to11543:
    assume $As(local11900, Microsoft.Contracts.ICheckedException) == null;
    goto block11543;

  block11543:
    // ----- branch
    goto block11560;

  block11424:
    goto block11441;

  block11628:
    // ----- load token  ----- Finally.ssc(54,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, ReturnFinally);
    // ----- statically resolved GetTypeFromHandle call  ----- Finally.ssc(54,5)
    stack0o := TypeObject(ReturnFinally);
    // ----- local pack  ----- Finally.ssc(54,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, ReturnFinally.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == ReturnFinally ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block11560;

  block11441:
    goto block11458;

  block11560:
    goto block11577;

  block11458:
    // ----- nop
    // ----- branch
    goto block11339;

  block11577:
    goto block11594;

  block11339:
    goto block11356;

  block11594:
    // ----- nop
    // ----- branch
    goto block11322;

  block11356:
    // ----- return
    return;

  block11322:
    goto block11339;

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

axiom Microsoft.Contracts.ICheckedException <: System.Object;

axiom $IsMemberlessType(Microsoft.Contracts.ICheckedException);

procedure ReturnFinally.Expose1$System.Boolean(this: ref, b$in: bool where true);
  free requires true;
  // user-declared preconditions
  requires !b$in;
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || $f != ReturnFinally.y) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation ReturnFinally.Expose1$System.Boolean(this: ref, b$in: bool)
{
  var b: bool where true, temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local13906: ref where $Is(local13906, System.Exception), stack0i: int, stack0b: bool, stack0o: ref, stack0s: struct;

  entry:
    assume $IsNotNull(this, ReturnFinally);
    assume $Heap[this, $allocated] == true;
    b := b$in;
    goto block12733;

  block12733:
    goto block13090;

  block13090:
    // ----- nop
    goto block13107;

  block13107:
    // ----- FrameGuard processing  ----- Finally.ssc(61,13)
    temp0 := this;
    // ----- load token  ----- Finally.ssc(61,13)
    havoc stack1s;
    assume $IsTokenForType(stack1s, ReturnFinally);
    // ----- statically resolved GetTypeFromHandle call  ----- Finally.ssc(61,13)
    stack1o := TypeObject(ReturnFinally);
    // ----- local unpack  ----- Finally.ssc(61,13)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: ReturnFinally && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local13906 := null;
    goto block13124;

  block13124:
    // ----- load constant -4  ----- Finally.ssc(62,16)
    stack0i := -4;
    // ----- store field  ----- Finally.ssc(62,7)
    assert this != null;
    assert !($Heap[this, $inv] <: ReturnFinally) || $Heap[this, $localinv] == System.Object;
    $Heap[this, ReturnFinally.y] := stack0i;
    assume IsHeap($Heap);
    goto block13141;

  block13141:
    // ----- copy  ----- Finally.ssc(63,11)
    stack0b := b;
    // ----- unary operator  ----- Finally.ssc(63,11)
    // ----- branch  ----- Finally.ssc(63,7)
    goto true13141to13175, false13141to13158;

  true13141to13175:
    assume !stack0b;
    goto block13175;

  false13141to13158:
    assume stack0b;
    goto block13158;

  block13175:
    goto block13192;

  block13158:
    // ----- branch  ----- Finally.ssc(63,16)
    goto block13379;

  block13379:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true13379to13481, false13379to13396;

  true13379to13481:
    assume local13906 == stack0o;
    goto block13481;

  false13379to13396:
    assume local13906 != stack0o;
    goto block13396;

  block13481:
    goto block13498;

  block13396:
    // ----- is instance
    // ----- branch
    goto true13396to13481, false13396to13413;

  block13192:
    goto block13209;

  true13396to13481:
    assume $As(local13906, Microsoft.Contracts.ICheckedException) != null;
    goto block13481;

  false13396to13413:
    assume $As(local13906, Microsoft.Contracts.ICheckedException) == null;
    goto block13413;

  block13413:
    // ----- branch
    goto block13430;

  block13209:
    // ----- load constant 2  ----- Finally.ssc(64,16)
    stack0i := 2;
    // ----- store field  ----- Finally.ssc(64,7)
    assert this != null;
    assert !($Heap[this, $inv] <: ReturnFinally) || $Heap[this, $localinv] == System.Object;
    $Heap[this, ReturnFinally.y] := stack0i;
    assume IsHeap($Heap);
    // ----- branch
    goto block13515;

  block13498:
    // ----- load token  ----- Finally.ssc(65,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, ReturnFinally);
    // ----- statically resolved GetTypeFromHandle call  ----- Finally.ssc(65,5)
    stack0o := TypeObject(ReturnFinally);
    // ----- local pack  ----- Finally.ssc(65,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, ReturnFinally.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == ReturnFinally ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block13430;

  block13515:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true13515to13617, false13515to13532;

  true13515to13617:
    assume local13906 == stack0o;
    goto block13617;

  false13515to13532:
    assume local13906 != stack0o;
    goto block13532;

  block13617:
    goto block13634;

  block13532:
    // ----- is instance
    // ----- branch
    goto true13532to13617, false13532to13549;

  block13430:
    goto block13447;

  true13532to13617:
    assume $As(local13906, Microsoft.Contracts.ICheckedException) != null;
    goto block13617;

  false13532to13549:
    assume $As(local13906, Microsoft.Contracts.ICheckedException) == null;
    goto block13549;

  block13549:
    // ----- branch
    goto block13566;

  block13447:
    goto block13464;

  block13634:
    // ----- load token  ----- Finally.ssc(65,5)
    havoc stack0s;
    assume $IsTokenForType(stack0s, ReturnFinally);
    // ----- statically resolved GetTypeFromHandle call  ----- Finally.ssc(65,5)
    stack0o := TypeObject(ReturnFinally);
    // ----- local pack  ----- Finally.ssc(65,5)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, ReturnFinally.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == ReturnFinally ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block13566;

  block13464:
    // ----- nop
    // ----- branch
    goto block13345;

  block13566:
    goto block13583;

  block13345:
    goto block13362;

  block13583:
    goto block13600;

  block13362:
    // ----- return
    return;

  block13600:
    // ----- nop
    // ----- branch
    goto block13328;

  block13328:
    goto block13345;

}



procedure ReturnFinally.Expose2$System.Boolean$System.Int32(this: ref, b$in: bool where true, x$in: int where InRange(x$in, System.Int32));
  free requires true;
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || $f != ReturnFinally.y) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation ReturnFinally.Expose2$System.Boolean$System.Int32(this: ref, b$in: bool, x$in: int)
{
  var b: bool where true, x: int where InRange(x, System.Int32), i: int where InRange(i, System.Int32), stack0b: bool, temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local15997: ref where $Is(local15997, System.Exception), stack0i: int, stack0o: ref, stack0s: struct, local16014: int where InRange(local16014, System.Int32), $Heap$block15079$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, ReturnFinally);
    assume $Heap[this, $allocated] == true;
    b := b$in;
    x := x$in;
    goto block14790;

  block14790:
    goto block15045;

  block15045:
    // ----- nop
    goto block15062;

  block15062:
    // ----- load constant 0  ----- Finally.ssc(71,10)
    i := 0;
    goto block15079$LoopPreheader;

  block15079:
    // ----- default loop invariant: allocation and ownership are stable  ----- Finally.ssc(71,21)
    assume (forall $o: ref :: $Heap$block15079$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block15079$LoopPreheader[$ot, $allocated] == true && $Heap$block15079$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block15079$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block15079$LoopPreheader[$ot, $ownerFrame]) && $Heap$block15079$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- Finally.ssc(71,21)
    assume (forall $o: ref :: ($Heap$block15079$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block15079$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block15079$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block15079$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- Finally.ssc(71,21)
    assert (forall $o: ref :: $o != null && $Heap$block15079$LoopPreheader[$o, $allocated] == true ==> $Heap$block15079$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block15079$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- default loop invariant: modifies  ----- Finally.ssc(71,21)
    assert (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || $f != ReturnFinally.y) && old($o != this || $f != $exposeVersion) ==> $Heap$block15079$LoopPreheader[$o, $f] == $Heap[$o, $f]);
    // ----- binary operator  ----- Finally.ssc(71,21)
    // ----- branch  ----- Finally.ssc(71,21)
    goto true15079to15385, false15079to15096;

  true15079to15385:
    assume i >= x;
    goto block15385;

  false15079to15096:
    assume i < x;
    goto block15096;

  block15385:
    goto block15402;

  block15096:
    // ----- FrameGuard processing  ----- Finally.ssc(72,15)
    temp0 := this;
    // ----- load token  ----- Finally.ssc(72,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, ReturnFinally);
    // ----- statically resolved GetTypeFromHandle call  ----- Finally.ssc(72,15)
    stack1o := TypeObject(ReturnFinally);
    // ----- local unpack  ----- Finally.ssc(72,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: ReturnFinally && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local15997 := null;
    goto block15113;

  block15113:
    // ----- load constant -4  ----- Finally.ssc(73,18)
    stack0i := -4;
    // ----- store field  ----- Finally.ssc(73,9)
    assert this != null;
    assert !($Heap[this, $inv] <: ReturnFinally) || $Heap[this, $localinv] == System.Object;
    $Heap[this, ReturnFinally.y] := stack0i;
    assume IsHeap($Heap);
    goto block15130;

  block15402:
    goto block15419;

  block15130:
    // ----- copy  ----- Finally.ssc(74,13)
    stack0b := b;
    // ----- unary operator  ----- Finally.ssc(74,13)
    // ----- branch  ----- Finally.ssc(74,9)
    goto true15130to15164, false15130to15147;

  true15130to15164:
    assume !stack0b;
    goto block15164;

  false15130to15147:
    assume stack0b;
    goto block15147;

  block15164:
    goto block15181;

  block15147:
    // ----- branch  ----- Finally.ssc(74,18)
    goto block15436;

  block15419:
    // ----- return
    return;

  block15181:
    goto block15198;

  block15436:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true15436to15538, false15436to15453;

  true15436to15538:
    assume local15997 == stack0o;
    goto block15538;

  false15436to15453:
    assume local15997 != stack0o;
    goto block15453;

  block15538:
    goto block15555;

  block15453:
    // ----- is instance
    // ----- branch
    goto true15453to15538, false15453to15470;

  block15198:
    // ----- load constant 2  ----- Finally.ssc(75,18)
    stack0i := 2;
    // ----- store field  ----- Finally.ssc(75,9)
    assert this != null;
    assert !($Heap[this, $inv] <: ReturnFinally) || $Heap[this, $localinv] == System.Object;
    $Heap[this, ReturnFinally.y] := stack0i;
    assume IsHeap($Heap);
    // ----- branch
    goto block15572;

  true15453to15538:
    assume $As(local15997, Microsoft.Contracts.ICheckedException) != null;
    goto block15538;

  false15453to15470:
    assume $As(local15997, Microsoft.Contracts.ICheckedException) == null;
    goto block15470;

  block15470:
    // ----- branch
    goto block15487;

  block15572:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true15572to15674, false15572to15589;

  true15572to15674:
    assume local15997 == stack0o;
    goto block15674;

  false15572to15589:
    assume local15997 != stack0o;
    goto block15589;

  block15674:
    goto block15691;

  block15589:
    // ----- is instance
    // ----- branch
    goto true15589to15674, false15589to15606;

  block15555:
    // ----- load token  ----- Finally.ssc(76,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, ReturnFinally);
    // ----- statically resolved GetTypeFromHandle call  ----- Finally.ssc(76,7)
    stack0o := TypeObject(ReturnFinally);
    // ----- local pack  ----- Finally.ssc(76,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, ReturnFinally.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == ReturnFinally ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block15487;

  true15589to15674:
    assume $As(local15997, Microsoft.Contracts.ICheckedException) != null;
    goto block15674;

  false15589to15606:
    assume $As(local15997, Microsoft.Contracts.ICheckedException) == null;
    goto block15606;

  block15606:
    // ----- branch
    goto block15623;

  block15487:
    goto block15504;

  block15691:
    // ----- load token  ----- Finally.ssc(76,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, ReturnFinally);
    // ----- statically resolved GetTypeFromHandle call  ----- Finally.ssc(76,7)
    stack0o := TypeObject(ReturnFinally);
    // ----- local pack  ----- Finally.ssc(76,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, ReturnFinally.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == ReturnFinally ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block15623;

  block15504:
    goto block15521;

  block15623:
    goto block15640;

  block15521:
    // ----- nop
    // ----- branch
    goto block15385;

  block15640:
    goto block15657;

  block15657:
    // ----- nop
    // ----- branch
    goto block15317;

  block15317:
    goto block15334;

  block15334:
    // ----- copy  ----- Finally.ssc(71,28)
    local16014 := i;
    // ----- load constant 1  ----- Finally.ssc(71,28)
    stack0i := 1;
    // ----- binary operator  ----- Finally.ssc(71,28)
    stack0i := local16014 + stack0i;
    // ----- copy  ----- Finally.ssc(71,28)
    i := stack0i;
    // ----- copy  ----- Finally.ssc(71,28)
    stack0i := local16014;
    goto block15351;

  block15351:
    // ----- nop  ----- Finally.ssc(71,28)
    goto block15368;

  block15368:
    // ----- branch
    goto block15079;

  block15079$LoopPreheader:
    $Heap$block15079$LoopPreheader := $Heap;
    goto block15079;

}



procedure ReturnFinally.Expose3$System.Boolean$System.Int32(this: ref, b$in: bool where true, x$in: int where InRange(x$in, System.Int32));
  free requires true;
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || $f != ReturnFinally.y) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation ReturnFinally.Expose3$System.Boolean$System.Int32(this: ref, b$in: bool, x$in: int)
{
  var b: bool where true, x: int where InRange(x, System.Int32), i: int where InRange(i, System.Int32), stack0b: bool, temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local18105: ref where $Is(local18105, System.Exception), stack0i: int, stack0o: ref, stack0s: struct, local18156: int where InRange(local18156, System.Int32), $Heap$block17187$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, ReturnFinally);
    assume $Heap[this, $allocated] == true;
    b := b$in;
    x := x$in;
    goto block16898;

  block16898:
    goto block17153;

  block17153:
    // ----- nop
    goto block17170;

  block17170:
    // ----- load constant 0  ----- Finally.ssc(83,10)
    i := 0;
    goto block17187$LoopPreheader;

  block17187:
    // ----- default loop invariant: allocation and ownership are stable  ----- Finally.ssc(83,21)
    assume (forall $o: ref :: $Heap$block17187$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block17187$LoopPreheader[$ot, $allocated] == true && $Heap$block17187$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block17187$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block17187$LoopPreheader[$ot, $ownerFrame]) && $Heap$block17187$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- Finally.ssc(83,21)
    assume (forall $o: ref :: ($Heap$block17187$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block17187$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block17187$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block17187$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- Finally.ssc(83,21)
    assert (forall $o: ref :: $o != null && $Heap$block17187$LoopPreheader[$o, $allocated] == true ==> $Heap$block17187$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block17187$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- default loop invariant: modifies  ----- Finally.ssc(83,21)
    assert (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || $f != ReturnFinally.y) && old($o != this || $f != $exposeVersion) ==> $Heap$block17187$LoopPreheader[$o, $f] == $Heap[$o, $f]);
    // ----- binary operator  ----- Finally.ssc(83,21)
    // ----- branch  ----- Finally.ssc(83,21)
    goto true17187to17493, false17187to17204;

  true17187to17493:
    assume i >= x;
    goto block17493;

  false17187to17204:
    assume i < x;
    goto block17204;

  block17493:
    goto block17510;

  block17204:
    // ----- FrameGuard processing  ----- Finally.ssc(84,15)
    temp0 := this;
    // ----- load token  ----- Finally.ssc(84,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, ReturnFinally);
    // ----- statically resolved GetTypeFromHandle call  ----- Finally.ssc(84,15)
    stack1o := TypeObject(ReturnFinally);
    // ----- local unpack  ----- Finally.ssc(84,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: ReturnFinally && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local18105 := null;
    goto block17221;

  block17510:
    goto block17527;

  block17221:
    // ----- load constant -4  ----- Finally.ssc(85,18)
    stack0i := -4;
    // ----- store field  ----- Finally.ssc(85,9)
    assert this != null;
    assert !($Heap[this, $inv] <: ReturnFinally) || $Heap[this, $localinv] == System.Object;
    $Heap[this, ReturnFinally.y] := stack0i;
    assume IsHeap($Heap);
    goto block17238;

  block17527:
    // ----- return
    return;

  block17238:
    // ----- copy  ----- Finally.ssc(86,13)
    stack0b := b;
    // ----- unary operator  ----- Finally.ssc(86,13)
    // ----- branch  ----- Finally.ssc(86,9)
    goto true17238to17272, false17238to17255;

  true17238to17272:
    assume !stack0b;
    goto block17272;

  false17238to17255:
    assume stack0b;
    goto block17255;

  block17272:
    goto block17289;

  block17255:
    // ----- branch  ----- Finally.ssc(86,18)
    goto block17544;

  block17289:
    goto block17306;

  block17544:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true17544to17646, false17544to17561;

  true17544to17646:
    assume local18105 == stack0o;
    goto block17646;

  false17544to17561:
    assume local18105 != stack0o;
    goto block17561;

  block17646:
    goto block17663;

  block17561:
    // ----- is instance
    // ----- branch
    goto true17561to17646, false17561to17578;

  block17306:
    // ----- load constant 2  ----- Finally.ssc(87,18)
    stack0i := 2;
    // ----- store field  ----- Finally.ssc(87,9)
    assert this != null;
    assert !($Heap[this, $inv] <: ReturnFinally) || $Heap[this, $localinv] == System.Object;
    $Heap[this, ReturnFinally.y] := stack0i;
    assume IsHeap($Heap);
    // ----- branch
    goto block17680;

  true17561to17646:
    assume $As(local18105, Microsoft.Contracts.ICheckedException) != null;
    goto block17646;

  false17561to17578:
    assume $As(local18105, Microsoft.Contracts.ICheckedException) == null;
    goto block17578;

  block17578:
    // ----- branch
    goto block17595;

  block17680:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true17680to17782, false17680to17697;

  true17680to17782:
    assume local18105 == stack0o;
    goto block17782;

  false17680to17697:
    assume local18105 != stack0o;
    goto block17697;

  block17782:
    goto block17799;

  block17697:
    // ----- is instance
    // ----- branch
    goto true17697to17782, false17697to17714;

  block17663:
    // ----- load token  ----- Finally.ssc(88,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, ReturnFinally);
    // ----- statically resolved GetTypeFromHandle call  ----- Finally.ssc(88,7)
    stack0o := TypeObject(ReturnFinally);
    // ----- local pack  ----- Finally.ssc(88,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, ReturnFinally.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == ReturnFinally ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block17595;

  true17697to17782:
    assume $As(local18105, Microsoft.Contracts.ICheckedException) != null;
    goto block17782;

  false17697to17714:
    assume $As(local18105, Microsoft.Contracts.ICheckedException) == null;
    goto block17714;

  block17714:
    // ----- branch
    goto block17731;

  block17595:
    goto block17612;

  block17799:
    // ----- load token  ----- Finally.ssc(88,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, ReturnFinally);
    // ----- statically resolved GetTypeFromHandle call  ----- Finally.ssc(88,7)
    stack0o := TypeObject(ReturnFinally);
    // ----- local pack  ----- Finally.ssc(88,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, ReturnFinally.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == ReturnFinally ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block17731;

  block17612:
    goto block17629;

  block17731:
    goto block17748;

  block17629:
    // ----- nop
    // ----- branch
    goto block17442;

  block17748:
    goto block17765;

  block17442:
    // ----- copy  ----- Finally.ssc(83,28)
    local18156 := i;
    // ----- load constant 1  ----- Finally.ssc(83,28)
    stack0i := 1;
    // ----- binary operator  ----- Finally.ssc(83,28)
    stack0i := local18156 + stack0i;
    // ----- copy  ----- Finally.ssc(83,28)
    i := stack0i;
    // ----- copy  ----- Finally.ssc(83,28)
    stack0i := local18156;
    goto block17459;

  block17765:
    // ----- nop
    // ----- branch
    goto block17425;

  block17459:
    // ----- nop  ----- Finally.ssc(83,28)
    goto block17476;

  block17425:
    goto block17442;

  block17476:
    // ----- branch
    goto block17187;

  block17187$LoopPreheader:
    $Heap$block17187$LoopPreheader := $Heap;
    goto block17187;

}



procedure ReturnFinally.Expose4$System.Boolean$System.Int32(this: ref, b$in: bool where true, x$in: int where InRange(x$in, System.Int32));
  free requires true;
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
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || $f != ReturnFinally.y) && old($o != this || $f != $exposeVersion) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation ReturnFinally.Expose4$System.Boolean$System.Int32(this: ref, b$in: bool, x$in: int)
{
  var b: bool where true, x: int where InRange(x, System.Int32), i: int where InRange(i, System.Int32), stack0b: bool, temp0: ref, stack1s: struct, stack1o: ref, temp1: exposeVersionType, local20247: ref where $Is(local20247, System.Exception), stack0i: int, stack0o: ref, stack0s: struct, local20264: int where InRange(local20264, System.Int32), $Heap$block19312$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, ReturnFinally);
    assume $Heap[this, $allocated] == true;
    b := b$in;
    x := x$in;
    goto block19023;

  block19023:
    goto block19278;

  block19278:
    // ----- nop
    goto block19295;

  block19295:
    // ----- load constant 0  ----- Finally.ssc(95,10)
    i := 0;
    goto block19312$LoopPreheader;

  block19312:
    // ----- default loop invariant: allocation and ownership are stable  ----- Finally.ssc(95,21)
    assume (forall $o: ref :: $Heap$block19312$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block19312$LoopPreheader[$ot, $allocated] == true && $Heap$block19312$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block19312$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block19312$LoopPreheader[$ot, $ownerFrame]) && $Heap$block19312$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- Finally.ssc(95,21)
    assume (forall $o: ref :: ($Heap$block19312$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block19312$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block19312$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block19312$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- Finally.ssc(95,21)
    assert (forall $o: ref :: $o != null && $Heap$block19312$LoopPreheader[$o, $allocated] == true ==> $Heap$block19312$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block19312$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- default loop invariant: modifies  ----- Finally.ssc(95,21)
    assert (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old($o != this || $f != ReturnFinally.y) && old($o != this || $f != $exposeVersion) ==> $Heap$block19312$LoopPreheader[$o, $f] == $Heap[$o, $f]);
    // ----- binary operator  ----- Finally.ssc(95,21)
    // ----- branch  ----- Finally.ssc(95,21)
    goto true19312to19618, false19312to19329;

  true19312to19618:
    assume i >= x;
    goto block19618;

  false19312to19329:
    assume i < x;
    goto block19329;

  block19618:
    goto block19635;

  block19329:
    // ----- FrameGuard processing  ----- Finally.ssc(96,15)
    temp0 := this;
    // ----- load token  ----- Finally.ssc(96,15)
    havoc stack1s;
    assume $IsTokenForType(stack1s, ReturnFinally);
    // ----- statically resolved GetTypeFromHandle call  ----- Finally.ssc(96,15)
    stack1o := TypeObject(ReturnFinally);
    // ----- local unpack  ----- Finally.ssc(96,15)
    assert temp0 != null;
    assert ($Heap[temp0, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[temp0, $ownerRef], $inv] <: $Heap[temp0, $ownerFrame]) || $Heap[$Heap[temp0, $ownerRef], $localinv] == $BaseClass($Heap[temp0, $ownerFrame])) && $Heap[temp0, $inv] <: ReturnFinally && $Heap[temp0, $localinv] == $typeof(temp0);
    $Heap[temp0, $localinv] := System.Object;
    havoc temp1;
    $Heap[temp0, $exposeVersion] := temp1;
    assume IsHeap($Heap);
    local20247 := null;
    goto block19346;

  block19635:
    goto block19652;

  block19346:
    // ----- load constant -4  ----- Finally.ssc(97,18)
    stack0i := -4;
    // ----- store field  ----- Finally.ssc(97,9)
    assert this != null;
    assert !($Heap[this, $inv] <: ReturnFinally) || $Heap[this, $localinv] == System.Object;
    $Heap[this, ReturnFinally.y] := stack0i;
    assume IsHeap($Heap);
    goto block19363;

  block19652:
    goto block19669;

  block19363:
    // ----- copy  ----- Finally.ssc(98,13)
    stack0b := b;
    // ----- unary operator  ----- Finally.ssc(98,13)
    // ----- branch  ----- Finally.ssc(98,9)
    goto true19363to19397, false19363to19380;

  true19363to19397:
    assume !stack0b;
    goto block19397;

  false19363to19380:
    assume stack0b;
    goto block19380;

  block19397:
    goto block19414;

  block19380:
    // ----- branch  ----- Finally.ssc(98,18)
    goto block19686;

  block19669:
    // ----- return
    return;

  block19414:
    goto block19431;

  block19686:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true19686to19788, false19686to19703;

  true19686to19788:
    assume local20247 == stack0o;
    goto block19788;

  false19686to19703:
    assume local20247 != stack0o;
    goto block19703;

  block19788:
    goto block19805;

  block19703:
    // ----- is instance
    // ----- branch
    goto true19703to19788, false19703to19720;

  block19431:
    // ----- load constant 2  ----- Finally.ssc(99,18)
    stack0i := 2;
    // ----- store field  ----- Finally.ssc(99,9)
    assert this != null;
    assert !($Heap[this, $inv] <: ReturnFinally) || $Heap[this, $localinv] == System.Object;
    $Heap[this, ReturnFinally.y] := stack0i;
    assume IsHeap($Heap);
    // ----- branch
    goto block19822;

  true19703to19788:
    assume $As(local20247, Microsoft.Contracts.ICheckedException) != null;
    goto block19788;

  false19703to19720:
    assume $As(local20247, Microsoft.Contracts.ICheckedException) == null;
    goto block19720;

  block19720:
    // ----- branch
    goto block19737;

  block19822:
    stack0o := null;
    // ----- binary operator
    // ----- branch
    goto true19822to19924, false19822to19839;

  true19822to19924:
    assume local20247 == stack0o;
    goto block19924;

  false19822to19839:
    assume local20247 != stack0o;
    goto block19839;

  block19924:
    goto block19941;

  block19839:
    // ----- is instance
    // ----- branch
    goto true19839to19924, false19839to19856;

  block19805:
    // ----- load token  ----- Finally.ssc(100,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, ReturnFinally);
    // ----- statically resolved GetTypeFromHandle call  ----- Finally.ssc(100,7)
    stack0o := TypeObject(ReturnFinally);
    // ----- local pack  ----- Finally.ssc(100,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, ReturnFinally.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == ReturnFinally ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block19737;

  true19839to19924:
    assume $As(local20247, Microsoft.Contracts.ICheckedException) != null;
    goto block19924;

  false19839to19856:
    assume $As(local20247, Microsoft.Contracts.ICheckedException) == null;
    goto block19856;

  block19856:
    // ----- branch
    goto block19873;

  block19737:
    goto block19754;

  block19941:
    // ----- load token  ----- Finally.ssc(100,7)
    havoc stack0s;
    assume $IsTokenForType(stack0s, ReturnFinally);
    // ----- statically resolved GetTypeFromHandle call  ----- Finally.ssc(100,7)
    stack0o := TypeObject(ReturnFinally);
    // ----- local pack  ----- Finally.ssc(100,7)
    assert temp0 != null;
    assert $Heap[temp0, $localinv] == System.Object;
    assert 0 <= $Heap[temp0, ReturnFinally.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == ReturnFinally ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $localinv] := $typeof(temp0);
    assume IsHeap($Heap);
    goto block19873;

  block19754:
    goto block19771;

  block19873:
    goto block19890;

  block19771:
    // ----- nop
    // ----- branch
    goto block19635;

  block19890:
    goto block19907;

  block19907:
    // ----- nop
    // ----- branch
    goto block19550;

  block19550:
    goto block19567;

  block19567:
    // ----- copy  ----- Finally.ssc(95,28)
    local20264 := i;
    // ----- load constant 1  ----- Finally.ssc(95,28)
    stack0i := 1;
    // ----- binary operator  ----- Finally.ssc(95,28)
    stack0i := local20264 + stack0i;
    // ----- copy  ----- Finally.ssc(95,28)
    i := stack0i;
    // ----- copy  ----- Finally.ssc(95,28)
    stack0i := local20264;
    goto block19584;

  block19584:
    // ----- nop  ----- Finally.ssc(95,28)
    goto block19601;

  block19601:
    // ----- branch
    goto block19312;

  block19312$LoopPreheader:
    $Heap$block19312$LoopPreheader := $Heap;
    goto block19312;

}



procedure ReturnFinally.M(this: ref);
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



implementation ReturnFinally.M(this: ref)
{
  var stack0o: ref;

  entry:
    assume $IsNotNull(this, ReturnFinally);
    assume $Heap[this, $allocated] == true;
    goto block21029;

  block21029:
    goto block21284;

  block21284:
    // ----- nop
    goto block21301;

  block21301:
    // ----- branch
    goto block21403;

  block21403:
    // ----- serialized AssertStatement  ----- Finally.ssc(109,7)
    assert false;
    return;

}



procedure ReturnFinally.N(this: ref);
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



implementation ReturnFinally.N(this: ref)
{
  var stack0o: ref;

  entry:
    assume $IsNotNull(this, ReturnFinally);
    assume $Heap[this, $allocated] == true;
    goto block22355;

  block22355:
    goto block22610;

  block22610:
    // ----- nop
    goto block22627;

  block22627:
    // ----- branch  ----- Finally.ssc(115,7)
    goto block22746;

  block22746:
    // ----- serialized AssertStatement  ----- Finally.ssc(117,7)
    assert false;
    return;

}



procedure ReturnFinally.P0$System.Int32(this: ref, x$in: int where InRange(x$in, System.Int32));
  free requires true;
  // user-declared preconditions
  requires 0 <= x$in;
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



implementation ReturnFinally.P0$System.Int32(this: ref, x$in: int)
{
  var x: int where InRange(x, System.Int32), stack0o: ref, stack0i: int, stack0b: bool, local24922: int where InRange(local24922, System.Int32), $Heap$block24531$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, ReturnFinally);
    assume $Heap[this, $allocated] == true;
    x := x$in;
    goto block24055;

  block24055:
    goto block24412;

  block24412:
    // ----- nop
    goto block24429;

  block24429:
    // ----- branch
    goto block24531$LoopPreheader;

  block24531:
    // ----- default loop invariant: allocation and ownership are stable  ----- Finally.ssc(127,19)
    assume (forall $o: ref :: $Heap$block24531$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block24531$LoopPreheader[$ot, $allocated] == true && $Heap$block24531$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block24531$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block24531$LoopPreheader[$ot, $ownerFrame]) && $Heap$block24531$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- Finally.ssc(127,19)
    assume (forall $o: ref :: ($Heap$block24531$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block24531$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block24531$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block24531$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- Finally.ssc(127,19)
    assert (forall $o: ref :: $o != null && $Heap$block24531$LoopPreheader[$o, $allocated] == true ==> $Heap$block24531$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block24531$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- default loop invariant: modifies  ----- Finally.ssc(127,19)
    assert (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> $Heap$block24531$LoopPreheader[$o, $f] == $Heap[$o, $f]);
    // ----- serialized LoopInvariant  ----- Finally.ssc(127,19)
    assert 0 <= x;
    goto block24616;

  block24616:
    // ----- nop
    goto block24633;

  block24633:
    // ----- load constant 0  ----- Finally.ssc(126,14)
    stack0i := 0;
    // ----- binary operator  ----- Finally.ssc(126,14)
    // ----- branch  ----- Finally.ssc(126,7)
    goto true24633to24701, false24633to24650;

  true24633to24701:
    assume stack0i >= x;
    goto block24701;

  false24633to24650:
    assume stack0i < x;
    goto block24650;

  block24701:
    goto block24718;

  block24650:
    // ----- copy  ----- Finally.ssc(129,9)
    local24922 := x;
    // ----- load constant 1  ----- Finally.ssc(129,9)
    stack0i := 1;
    // ----- binary operator  ----- Finally.ssc(129,9)
    stack0i := local24922 - stack0i;
    // ----- copy  ----- Finally.ssc(129,9)
    x := stack0i;
    // ----- copy  ----- Finally.ssc(129,9)
    stack0i := local24922;
    goto block24667;

  block24718:
    // ----- nop
    // ----- branch
    goto block24480;

  block24667:
    // ----- nop  ----- Finally.ssc(129,9)
    goto block24684;

  block24480:
    goto block24497;

  block24684:
    // ----- branch  ----- Finally.ssc(130,8)
    goto block24531;

  block24497:
    goto block24514;

  block24514:
    // ----- return
    return;

  block24531$LoopPreheader:
    $Heap$block24531$LoopPreheader := $Heap;
    goto block24531;

}



procedure ReturnFinally.P1$System.Int32(this: ref, x$in: int where InRange(x$in, System.Int32));
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



implementation ReturnFinally.P1$System.Int32(this: ref, x$in: int)
{
  var x: int where InRange(x, System.Int32), stack0o: ref, stack0i: int, stack0b: bool, local26571: int where InRange(local26571, System.Int32), $Heap$block26180$LoopPreheader: [ref,<x>name]x;

  entry:
    assume $IsNotNull(this, ReturnFinally);
    assume $Heap[this, $allocated] == true;
    x := x$in;
    goto block25806;

  block25806:
    goto block26061;

  block26061:
    // ----- nop
    goto block26078;

  block26078:
    // ----- branch
    goto block26180$LoopPreheader;

  block26180:
    // ----- default loop invariant: allocation and ownership are stable  ----- Finally.ssc(139,19)
    assume (forall $o: ref :: $Heap$block26180$LoopPreheader[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: $Heap$block26180$LoopPreheader[$ot, $allocated] == true && $Heap$block26180$LoopPreheader[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == $Heap$block26180$LoopPreheader[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == $Heap$block26180$LoopPreheader[$ot, $ownerFrame]) && $Heap$block26180$LoopPreheader[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
    // ----- default loop invariant: $inv field  ----- Finally.ssc(139,19)
    assume (forall $o: ref :: ($Heap$block26180$LoopPreheader[$o, $inv] == $Heap[$o, $inv] && $Heap$block26180$LoopPreheader[$o, $localinv] == $Heap[$o, $localinv]) || $Heap$block26180$LoopPreheader[$o, $allocated] != true);
    assume (forall $o: ref :: $Heap$block26180$LoopPreheader[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
    // ----- default loop invariant: $ownerRef and $ownerFrame fields  ----- Finally.ssc(139,19)
    assert (forall $o: ref :: $o != null && $Heap$block26180$LoopPreheader[$o, $allocated] == true ==> $Heap$block26180$LoopPreheader[$o, $ownerRef] == $Heap[$o, $ownerRef] && $Heap$block26180$LoopPreheader[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
    // ----- default loop invariant: modifies  ----- Finally.ssc(139,19)
    assert (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && old(true) && old($o != this || $f != $exposeVersion) ==> $Heap$block26180$LoopPreheader[$o, $f] == $Heap[$o, $f]);
    // ----- serialized LoopInvariant  ----- Finally.ssc(139,19)
    assert 0 <= x;
    goto block26265;

  block26265:
    // ----- nop
    goto block26282;

  block26282:
    // ----- load constant 0  ----- Finally.ssc(138,14)
    stack0i := 0;
    // ----- binary operator  ----- Finally.ssc(138,14)
    // ----- branch  ----- Finally.ssc(138,7)
    goto true26282to26350, false26282to26299;

  true26282to26350:
    assume stack0i >= x;
    goto block26350;

  false26282to26299:
    assume stack0i < x;
    goto block26299;

  block26350:
    goto block26367;

  block26299:
    // ----- copy  ----- Finally.ssc(141,9)
    local26571 := x;
    // ----- load constant 1  ----- Finally.ssc(141,9)
    stack0i := 1;
    // ----- binary operator  ----- Finally.ssc(141,9)
    stack0i := local26571 - stack0i;
    // ----- copy  ----- Finally.ssc(141,9)
    x := stack0i;
    // ----- copy  ----- Finally.ssc(141,9)
    stack0i := local26571;
    goto block26316;

  block26367:
    // ----- nop
    // ----- branch
    goto block26129;

  block26316:
    // ----- nop  ----- Finally.ssc(141,9)
    goto block26333;

  block26129:
    goto block26146;

  block26333:
    // ----- branch  ----- Finally.ssc(142,8)
    goto block26180;

  block26146:
    goto block26163;

  block26163:
    // ----- return
    return;

  block26180$LoopPreheader:
    $Heap$block26180$LoopPreheader := $Heap;
    goto block26180;

}



procedure ReturnFinally..ctor(this: ref);
  // nothing is owned by [this,*]
  free requires (forall $o: ref :: $o != this ==> $Heap[$o, $ownerRef] != this);
  // 'this' is alone in its own peer group
  free requires $Heap[this, $ownerRef] == this && $Heap[this, $ownerFrame] == $PeerGroupPlaceholder;
  free requires (forall $o: ref :: $Heap[$o, $ownerRef] == $Heap[this, $ownerRef] && $Heap[$o, $ownerFrame] == $Heap[this, $ownerFrame] ==> $o == this);
  free requires $BeingConstructed == this;
  modifies $Heap;
  ensures ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == ReturnFinally && $Heap[this, $localinv] == $typeof(this);
  ensures $Heap[this, $ownerRef] == old($Heap)[this, $ownerRef] && $Heap[this, $ownerFrame] == old($Heap)[this, $ownerFrame];
  ensures $Heap[this, $sharingMode] == $SharingMode_Unshared;
  // newly allocated objects are fully valid
  free ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] != true && $Heap[$o, $allocated] == true ==> $Heap[$o, $inv] == $typeof($o) && $Heap[$o, $localinv] == $typeof($o));
  // first consistent owner unchanged if its exposeVersion is
  free ensures (forall $o: ref :: { $Heap[$o, $FirstConsistentOwner] } old($Heap)[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] == $Heap[old($Heap)[$o, $FirstConsistentOwner], $exposeVersion] ==> old($Heap)[$o, $FirstConsistentOwner] == $Heap[$o, $FirstConsistentOwner]);
  // only captured parameters may change their owners
  ensures (forall $o: ref :: $o != null && old($Heap)[$o, $allocated] == true ==> old($Heap)[$o, $ownerRef] == $Heap[$o, $ownerRef] && old($Heap)[$o, $ownerFrame] == $Heap[$o, $ownerFrame]);
  // frame condition
  free ensures (forall $o: ref, $f: name :: { $Heap[$o, $f] } $f != $inv && $f != $localinv && $f != $FirstConsistentOwner && (!IsStaticField($f) || !IsDirectlyModifiableField($f)) && $o != null && old($Heap)[$o, $allocated] == true && (old($Heap)[$o, $ownerFrame] == $PeerGroupPlaceholder || !(old($Heap)[old($Heap)[$o, $ownerRef], $inv] <: old($Heap)[$o, $ownerFrame]) || old($Heap)[old($Heap)[$o, $ownerRef], $localinv] == $BaseClass(old($Heap)[$o, $ownerFrame])) && ($o != this || !(ReturnFinally <: DeclType($f))) && old(true) ==> old($Heap)[$o, $f] == $Heap[$o, $f]);
  free ensures (forall $o: ref :: $o == this || (old($Heap)[$o, $inv] == $Heap[$o, $inv] && old($Heap)[$o, $localinv] == $Heap[$o, $localinv]) || old($Heap)[$o, $allocated] != true);
  free ensures (forall $o: ref :: old($Heap)[$o, $allocated] == true ==> $Heap[$o, $allocated] == true) && (forall $ot: ref :: old($Heap)[$ot, $allocated] == true && old($Heap)[$ot, $ownerFrame] != $PeerGroupPlaceholder ==> $Heap[$ot, $ownerRef] == old($Heap)[$ot, $ownerRef] && $Heap[$ot, $ownerFrame] == old($Heap)[$ot, $ownerFrame]) && old($Heap)[$BeingConstructed, $NonNullFieldsAreInitialized] == $Heap[$BeingConstructed, $NonNullFieldsAreInitialized];
  free ensures (forall $o: ref :: $o == this || old($Heap[$o, $sharingMode]) == $Heap[$o, $sharingMode]);



implementation ReturnFinally..ctor(this: ref)
{
  var temp0: ref;

  entry:
    assume $IsNotNull(this, ReturnFinally);
    assume $Heap[this, $allocated] == true;
    assume ($Heap[this, $ownerFrame] == $PeerGroupPlaceholder || !($Heap[$Heap[this, $ownerRef], $inv] <: $Heap[this, $ownerFrame]) || $Heap[$Heap[this, $ownerRef], $localinv] == $BaseClass($Heap[this, $ownerFrame])) && $Heap[this, $inv] == System.Object && $Heap[this, $localinv] == $typeof(this);
    assume $Heap[this, ReturnFinally.y] == 0;
    goto block27030;

  block27030:
    goto block27047;

  block27047:
    goto block27064;

  block27064:
    // ----- call  ----- Finally.ssc(1,14)
    assert this != null;
    call System.Object..ctor(this);
    goto block27183;

  block27183:
    goto block27200;

  block27200:
    // ----- nop
    goto block27217;

  block27217:
    goto block27234;

  block27234:
    // ----- FrameGuard processing  ----- Finally.ssc(1,26)
    temp0 := this;
    // ----- classic pack  ----- Finally.ssc(1,26)
    assert temp0 != null;
    assert $Heap[temp0, $inv] == System.Object && $Heap[temp0, $localinv] == $typeof(temp0);
    assert 0 <= $Heap[temp0, ReturnFinally.y];
    assert (forall $p: ref :: $p != null && $Heap[$p, $allocated] == true && $Heap[$p, $ownerRef] == temp0 && $Heap[$p, $ownerFrame] == ReturnFinally ==> $Heap[$p, $inv] == $typeof($p) && $Heap[$p, $localinv] == $typeof($p));
    $Heap[temp0, $inv] := ReturnFinally;
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



procedure ReturnFinally..cctor();
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



implementation ReturnFinally..cctor()
{

  entry:
    goto block27574;

  block27574:
    goto block27693;

  block27693:
    // ----- nop
    goto block27710;

  block27710:
    goto block27727;

  block27727:
    // ----- return
    return;

}


