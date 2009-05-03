package tp;

public class PVis {

public int ip_public;
protected int ip_protected;
int ip_package;
private int ip_private;

//@ ghost public int gp_public;
//@ ghost protected int gp_protected;
//@ ghost int gp_package;
//@ ghost private int gp_private;

public int mp_public() {};
protected int mp_protected() {}
int mp_package() {}
private int mp_private() {}

//@ model public int qp_public() {};
//@ model protected int qp_protected() {}
//@ model int qp_package() {}
//@ model private int qp_private() {}


public static class Cp_public {}
protected static class Cp_protected {}
static class Cp_package {}
private static class Cp_private {}

//@ model public static class Dp_public {}
//@ model protected static class Dp_protected {}
//@ model static class Dp_package {}
//@ model private static class Dp_private {}

}

