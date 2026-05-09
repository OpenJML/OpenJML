public class PrimeCheckerTest {
    public static void main(String[] args) {
        assert PrimeChecker.isNonPrime(2) == false : "Test failed for input 2";
        assert PrimeChecker.isNonPrime(10) == true : "Test failed for input 10";
        assert PrimeChecker.isNonPrime(35) == true : "Test failed for input 35";
        System.out.println("All tests passed.");
    }
}
