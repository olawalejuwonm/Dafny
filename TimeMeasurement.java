import java.math.BigInteger;

//TIP To <b>Run</b> code, press <shortcut actionId="Run"/> or
// click the <icon src="AllIcons.Actions.Execute"/> icon in the gutter.
public class TimeMeasurement{

    public static java.math.BigInteger SquareRootAscendingSearch(java.math.BigInteger y)
    {}
    public static java.math.BigInteger SquareRootDescendingSearch(java.math.BigInteger y)
    {}
    public static java.math.BigInteger SquareRootAscendingUsingAddition(java.math.BigInteger y)
    {}

    public static void main(String[] args) {
        java.math.BigInteger z;
        BigInteger A = new BigInteger("23");
        long x = System.currentTimeMillis();
        z = SquareRootAscendingSearch(A);
        long y = System.currentTimeMillis();
        long diff = y - x;
        System.out.println(diff / 1000.0 + " sec -- Ascending");

        x = System.currentTimeMillis();
        z = SquareRootDescendingSearch(A);
        y = System.currentTimeMillis();
        diff = y - x;
        System.out.println(diff / 1000.0 + " sec -- Descending " );

        x = System.currentTimeMillis();
        z = SquareRootAscendingUsingAddition(A);
        y = System.currentTimeMillis();
        diff = y - x;
        System.out.println(diff / 1000.0 + " sec -- Ascending Using Addition");
    }
}
