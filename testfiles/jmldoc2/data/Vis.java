public class Vis extends SVis {

public int i_public;
protected int i_protected;
int i_package;
private int i_private;

//@ ghost public int g_public;
//@ ghost protected int g_protected;
//@ ghost int g_package;
//@ ghost private int g_private;

public int m_public() {};
protected int m_protected() {}
int m_package() {}
private int m_private() {}

//@ model public int q_public() {};
//@ model protected int q_protected() {}
//@ model int q_package() {}
//@ model private int q_private() {}

public Vis() {}
protected Vis(int i) {}
Vis(int i, int j) {}
private Vis(int i, int j, int k) {}

//@ model public Vis(Object o) {}
//@ model protected Vis(float i) {}
//@ model Vis(float i, float j) {}
//@ model private Vis(float i, float j, float k) {}


public static class C_public {}
protected static class C_protected {}
static class C_package {}
private static class C_private {}

//@ model public static class D_public {}
//@ model protected static class D_protected {}
//@ model static class D_package {}
//@ model private static class D_private {}

}

class SVis extends tp.PVis {

public int is_public;
protected int is_protected;
int is_package;
private int is_private;

//@ ghost public int gs_public;
//@ ghost protected int gs_protected;
//@ ghost int gs_package;
//@ ghost private int gs_private;

public int ms_public() {};
protected int ms_protected() {}
int ms_package() {}
private int ms_private() {}

//@ model public int qs_public() {};
//@ model protected int qs_protected() {}
//@ model int qs_package() {}
//@ model private int qs_private() {}

public static class Cs_public {}
protected static class Cs_protected {}
static class Cs_package {}
private static class Cs_private {}

//@ model public static class Ds_public {}
//@ model protected static class Ds_protected {}
//@ model static class Ds_package {}
//@ model private static class Ds_private {}


}
