public class HelloWorld {
    
    public static void main(String[] args) {
        boolean test1Result = test1();
        boolean test2Result = test2();
        boolean test3Result = test3();
        boolean test4Result = test4();
    }

    //@ requires true;
    //@ ensures \result == false;
    //@ assignable \everything;
    public static boolean test1() {
        Date date = new Date("5", "21", "31", "14:00:00");
        String result = getFormat(date);
        //@ print "TEST1", result, date.year.length();
        if (!result.startsWith("y-")) {
            return false;
        }
        return true;
    }

    //@ requires true;
    //@ ensures \result == true;
    //@ assignable \everything;
    public static boolean test2() {
        Date date = new Date("25", "21", "31", "14:00:00");
        //@ assert date.year == "25";
        //@ assert date.year.length() == 2;
        String result = getFormat(date);
        if (!result.startsWith("yy-")) {
            return false;
        }
        return true;
    }

    //@ requires true;
    //@ ensures \result == false; // FAILS
    //@ pure
    public static boolean test3() {
        Date date = new Date("025", "21", "31", "14:00:00");
        String result = getFormat(date);
        if (!result.startsWith("yy-")) {
            return false;
        }
        return true;
    }

    //@ requires true;
    //@ ensures \result == true;
    //@ pure
    public static boolean test4() {
        Date date = new Date();
        date.year = "2025";
        date.month = "21";
        date.day = "31";
        date.time = "14:00:00";
        String result = getFormat(date);
        if (!result.startsWith("yyyy-")) {
            return false;
        }
        return true;
    }

    //@ requires date != null && date.year != null && date.month != null && date.day != null && date.time != null;
    //@ ensures \result != null;
    //@ ensures date.year.length() >= 4 ==> \result.startsWith("yyyy-");
    //@ ensures date.year.length() < 4 ==> \result.startsWith("yy-");
    //@ assignable \nothing;
    //@ pure
    public static String getFormat(Date date) {
        String year, result;
        if (date.year.length() >= 4) {
            year = "yyyy-";
        } else {
            year = "yy-";
        }
        int tokenLen = date.month.length(); 
        result = year + getMonthFormat(tokenLen); 
        tokenLen = date.day.length();
        result = result + getDayFormat(tokenLen); 
        tokenLen = date.time.length();
        result = result + getTimeFormat(tokenLen); 
        return result;
    }

    //@ requires true;
    //@ ensures length == 1 ==> \result.equals("M");
    //@ ensures length == 2 ==> \result.equals("MM");
    //@ ensures length != 1 && length != 2 ==> \result.equals("MMM");
    //@ ensures \result != null;
    //@ assignable \nothing;
    //@ pure
    private static String getMonthFormat(int length) {
        switch (length) {
            case 1:
                return "M";
            case 2:
                return "MM";
            default:
                return "MMM";
        }
    }

    //@ requires true;
    //@ assignable \nothing;
    //@ ensures \result != null;
    //@ ensures length == 1 ==> \result.equals("-d");
    //@ ensures length == 2 ==> \result.equals("-dd");
    //@ ensures length != 1 && length != 2 ==> \result.equals("-ddd");
    //@ pure
    private static String getDayFormat(int length) {
        switch (length) {
            case 1:
                return "-d";
            case 2:
                return "-dd";
            default:
                return "-ddd";
        }
    } // Dead exit

    //@ requires true;
    //@ ensures length == 5 ==> \result.equals(" HH:mm");
    //@ ensures length == 8 ==> \result.equals(" HH:mm:ss");
    //@ ensures length != 5 && length != 8 ==> \result.equals(" HH:mm:ss.SSS");
    //@ ensures \result != null;
    //@ assignable \nothing;
    //@ pure
    private static String getTimeFormat(int length) {
        switch (length) {
            case 5: // HH:mm
                return " HH:mm";
            case 8: // HH:mm:ss
                return " HH:mm:ss";
            default:
                return " HH:mm:ss.SSS";
        }
    }
}

// Date class definition
class Date {
    public String year;
    public String month;
    public String day;
    public String time;

    // Default constructor
    //@ ensures this.year == year;
    //@ ensures this.month == month;
    //@ ensures this.day == day;
    //@ ensures this.time == time;
    //@ pure
    public Date() {
        year = "";
        month = "";
        day = "";
        time = "";
    }

    // Constructor with parameters
    //@ ensures this.year == year;
    //@ ensures this.month == month;
    //@ ensures this.day == day;
    //@ ensures this.time == time;
    //@ pure
    public Date(String year, String month, String day, String time) {
        this.year = year;
        this.month = month;
        this.day = day;
        this.time = time;
    }
} 
