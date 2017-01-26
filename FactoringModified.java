import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.math.BigInteger;
import java.util.Random;

public class FactoringModified {

    private static final Random RAND = new Random(System.currentTimeMillis());
    private static final String NEW_LINE = System.getProperty("line.separator");

    private static final BigInteger ZERO = BigInteger.ZERO;
    private static final BigInteger ONE = BigInteger.ONE;
    private static final BigInteger TWO = BigInteger.valueOf(2);
	private static final BigInteger THREE = BigInteger.valueOf(3);
    private static final BigInteger FOUR = BigInteger.valueOf(4);
    private static final BigInteger THOUSAND = BigInteger.valueOf(1000);
    private static final BigInteger INTEGER_MAX_VALUE = BigInteger.valueOf(Integer.MAX_VALUE);
    
    private static final int PRIME_CERTAINTY = 15;
    private static final int FAIL_BIT_SIZE = 79;
    private static final int POLLARD_RHO_TRIES = 2;
    private static final int POLLARD_RHO_LIMIT = 65;
    private static final int POLLARD_P_MINUS_1_FACTORIAL_LIMIT = 27000;
    
    private static final int COMPOSITE_SIZE = 175000;
//    private static final int COMPOSITE_SIZE = 500;
    private static final BigInteger COMPOSITE_SIZE_BIG_INTEGER = BigInteger.valueOf(COMPOSITE_SIZE);
    private static final boolean[] composite = new boolean[COMPOSITE_SIZE];
    private static final int TRIAL_LIMIT = 500;
    
    private static final BigInteger[] PRIMES = new BigInteger[TRIAL_LIMIT];
    private static final BigInteger[] PRIMES_BIG = new BigInteger[55000 - POLLARD_P_MINUS_1_FACTORIAL_LIMIT];
    private static final int[] PRIMES_INT = new int[TRIAL_LIMIT];
    private static int primesSize = 0;
    private static int primesBigSize = 0;
    private static final BigInteger DIV_TABLE_LIMIT = BigInteger.valueOf(COMPOSITE_SIZE);
    private static final BigInteger[] DIV_TABLE = new BigInteger[DIV_TABLE_LIMIT.intValue()];
    
    private static BufferedReader in;
    private static BufferedWriter out;

    private static long startTime = System.currentTimeMillis();
    
    static boolean aborted = false;
    private static StringBuilder stringBuilder;
    private static int IDX = 0;

    public static void main(String[] args) throws Exception {
    	in = new BufferedReader(new InputStreamReader(System.in));
//        in = new BufferedReader(new InputStreamReader(new FileInputStream("fact"), "UTF-8"));
        out = new BufferedWriter(new OutputStreamWriter(System.out));
        
        // build a sieve of eratosthenes
        for (int i = 2; i < COMPOSITE_SIZE; i++)
            if (!composite[i])
                for (int j = 2*i; j < COMPOSITE_SIZE; j += i)
                    composite[j] = true;

        PRIMES[primesSize++] = TWO;
        for (int i = 3; i < COMPOSITE_SIZE; i += 2)
            if (!composite[i]) {
            	if (i < TRIAL_LIMIT) {
                    PRIMES[primesSize++] = BigInteger.valueOf(i);
            	}
            	if (i > POLLARD_P_MINUS_1_FACTORIAL_LIMIT) {
                    PRIMES_BIG[primesBigSize++] = BigInteger.valueOf(i);
                }
                
            }
        
        String line;
        while ((line = in.readLine()) != null) {
            
            BigInteger n = new BigInteger(line);
            aborted = false; // aborted is used to signal that we failed in factoring a number

            // is n prime?
            if (isPrime(n)) {
            	 out.write(n + NEW_LINE + NEW_LINE);
                 continue;
            }
            
            IDX = 0;
            // now we assume n is composite and factor it recursively
            stringBuilder = new StringBuilder();
            factor(n);
            out.write(stringBuilder.toString());
            out.write(NEW_LINE);
        }

        out.flush();
    }
    
    private static void factor(BigInteger n) throws IOException {
        if (aborted)
            return;
        
        BigInteger gcd = null;
        
        // trial division
        if (gcd == null && IDX < primesSize) {
        	if (n.mod(PRIMES[IDX]).equals(ZERO)) {
        		gcd = PRIMES[IDX];
        	} else {
        		IDX++;
        	}
        }
        
        // pollard p-1
        if (gcd == null && n.bitLength() < 200) {
        	BigInteger k = TWO;
        	BigInteger tmp = null;
    		BigInteger a = BigInteger.valueOf(RAND.nextInt()).mod(n.subtract(TWO)).add(ONE);
    		int flag = (1 << 8) - 1;
    		
    		tmp = n.gcd(a);
    		if (!tmp.equals(ONE) && !tmp.equals(n)) // did we get lucky?
    			gcd = tmp;
    		else { // otherwise continue with pollard p-1
    			int limit = POLLARD_P_MINUS_1_FACTORIAL_LIMIT + primesBigSize;
    			for (int i = 0; i < limit; i++) {
    				if (i < POLLARD_P_MINUS_1_FACTORIAL_LIMIT)
    					a = a.modPow(k, n);
    				else
    					a = a.modPow(PRIMES_BIG[i-POLLARD_P_MINUS_1_FACTORIAL_LIMIT], n);
        			if (i < 100 || i % 100 == 0) { // brent optimisation
						tmp = a.subtract(ONE).gcd(n);
            			if (tmp.compareTo(ONE) > 0 && tmp.compareTo(n) < 0) {
            				gcd = tmp;
            				break;
            			}
            			else if (tmp.equals(n)) {
            				a = BigInteger.valueOf(RAND.nextInt()).mod(n.subtract(TWO)).add(ONE);
            				k = TWO;
            				i = 0;
            			}
					}
            		k = k.add(ONE);
        		}
    		}
        }
        
        // 79 old
        if (gcd == null && n.bitLength() < 83) {
			//int limit = n.bitLength() >= 83 ? 1 << 17 : 1 << (n.bitLength() / 4 + 1); // expected number of necessary steps in pollard rho
			int limit = 1 << (n.bitLength() / 4 + 1); // expected number of necessary steps in pollard rho
			
			for (int i = 0; i < 2; i++) { // run pollard rho twice
				BigInteger x1 = i == 0 ? TWO : BigInteger.valueOf(RAND.nextInt()).mod(n);
				BigInteger x2 = x1;
	        	BigInteger tmp = null;
				BigInteger prod = ONE;
				for (int counter = 0; counter < limit; counter++) {

					x1 = x1.pow(2).add(ONE).mod(n);
					x2 = x2.pow(2).add(ONE).mod(n);
					x2 = x2.pow(2).add(ONE).mod(n);

					prod = prod.multiply(x1.subtract(x2).abs()).mod(n); // brent optimisation
					if (counter % 100 == 0) {
						tmp = n.gcd(prod);
						if (!tmp.equals(ONE))
							break;
						prod = ONE;
					}
				}
				if (!tmp.equals(ONE) && !tmp.equals(n)) { // did we find non-trivial gcd?
					gcd = tmp;
					break;
				}
			}
		}
        
        // did we fail?
        if (gcd == null) {
			aborted = true;
			stringBuilder = new StringBuilder("fail" + NEW_LINE);
			return;
    	}
        
        // if we did not fail, then go on and process gcd and n/gcd
        n = n.divide(gcd);
        if (isPrime(n))
        	stringBuilder.append(n + NEW_LINE);
        else
        	factor(n);
        if (!aborted) { // process gcd if we did not abort during processing of n
        	if (isPrime(gcd))
            	stringBuilder.append(gcd + NEW_LINE);
            else
            	factor(gcd);
        }
    }
    
    static boolean isPrime(BigInteger n) {
    	/*
    	if (n.compareTo(COMPOSITE_SIZE_BIG_INTEGER) < 0) {
            return !composite[n.intValue()];
        }
    	else {
    		return n.isProbablePrime(50);
    	}
    	*/
    	return n.isProbablePrime(30);
    }

}
