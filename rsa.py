# Some notes for those unfamiliar with Python:
# The ** operator is exponentiation. 2**5 = 32.
# The % operator is modulus. 17 % 5 = 2
# The // operator is integer division, which rounds down (the "div" operator). 17 // 5 = 3

import math
import random
import time

import aks

# Used by ex_gcd() to display its steps taken.
# Returns a string representing an equation of the form r = s * a + t * b
def format_rsatb(r, s, a, t, b):
    op = "+"
    if t < 0:
        op = "-"
        t = -t
    
    return "%d = %d * %d %s %d * %d" % (r, s, a, op, t, b)

# Extended GCD algorithm. Returns the GCD of a and b, and the multiplicative inverse of a mod b as a 2-tuple.
def ex_gcd(a, b, show_steps):
    if show_steps:
        print("Finding GCD of %d and %d and the inverse of %d mod %d...\n" % (a, b, a, b))
    
    did_swap = False
    if b > a:
        t = a
        a = b
        b = t
        did_swap = True
    
    vals = [a, b]
    while vals[-1] != 0:
        vals.append(vals[-2] % vals[-1])
    vals = vals[:-1]
    
    if show_steps:
        print("Sequence of mod operatorws: " + str(vals))
        print("GCD(%d, %d) = %d\n" % (a, b, vals[-1]))
        
        print("Performing repeated substitution...")
    
    s = 1
    t = -(vals[-3] // vals[-2])
    if show_steps:
        print(format_rsatb(vals[-1], s, vals[-3], t, vals[-2]))
    for i in range(len(vals)-2, 1, -1):
        nt = -(vals[i-2] // vals[i-1])
        
        if show_steps:
            print("  ^ " + format_rsatb(vals[i], 1, vals[i-2], nt, vals[i-1]) + " -> \n")
        
        s_tmp = t
        t = s + t*nt
        s = s_tmp
        
        if show_steps:
            print(format_rsatb(vals[-1], s, vals[i-2], t, vals[i-1]))
    
    if did_swap:
        if show_steps:
            print("The multiplicative inverse of %d mod %d = %d mod %d = %d" % (b, a, t, a, t % a))
        
        return (vals[-1], t % a)
    
    else:
        if show_steps:
            print("The multiplicative inverse of %d mod %d = %d mod %d = %d" % (a, b, s, b, s % b))
        
        return (vals[-1], s % b)

# Returns a pair of integers whose product is the passed integer.
# If given a number that is the product of two primes, this will return those primes.
# If the passed integer is prime, returns None.
# We should really only be checking for divisibility by primes, but we'd have to cache a list of primes first which would complicate the code.
# Notice the time complexity is O(2^(n/2)) (exponential time) where n is the number of bits in N which is log(N)/log(2)
def dual_factor(N):
    for a in range(2, int(N**(1/2) + 1)):
        if N % a == 0:
            return (a, N // a)
    
    return None

# Finds a prime number in the range a to b.
# Repeatedly picks a range of numbers and applies the sieve of erotosthenes to it.
# Important note: Built-in random number generators are almost never cryptographically secure.
# It is vital to ensure that a real crypto implementation uses a secure RNG or an attacker may be able to find the internal state of the generator and figure out which sets of keys your computer will generate next.
def gen_prime(a, b):
    if a < 2 or b < a:
        raise Exception("Prime must be generated in the range a to b where a >= 2 and b > a")
    
    # Generate random numbers in the range until a prime number is found.
    # Careful! Locks up if the range doesn't include a prime!
    while True:
        midpoint = random.randint(int(a), int(b))
        start = max(a, midpoint - 50)
        end = min(b, midpoint + 50)
        len = int(end - start + 1)
        
        is_prime = [True]*len
        for d in range(2, int(end**0.5 + 1)):
            for p in range(start, end+1):
                if p % d == 0:
                    for q in range(p, end+1, d):
                        is_prime[q-start] = False
        
        for i in range(0, len):
            if is_prime[i]:
                return start + i

# Calculates a**b mod N.
def pow(a, b, N):
    ret = 1
    while b > 0:
        if b % 2 == 1:
            ret = ret*a % N
        
        b //= 2
        a = a*a % N
    
    return ret

# This function returns N, e, and d as a 3-tuple.
# The passed value decides the approximate maximum number of decimal digits in N.
def gen_keys(max_digits):
    max_gen = int(10**(max_digits/2))
    
    print("Generating keys...\n")
    p = gen_prime(2, max_gen)
    q = gen_prime(2, max_gen)
    
    N = p*q
    phi = (p-1)*(q-1)
    
    e = gen_prime(max(p, q), max_gen)
    
    print("p = %d, q = %d" % (p, q))
    print("N = pq = %d" % N)
    print("phi = (p-1)(q-1) = (%d)(%d) = %d" % (p-1, q-1, phi))
    print("e = %d\n" % e)
    d = ex_gcd(e, phi, True)[1]
    
    print("\nPublic key: N = %d, e = %d" % (N, e))
    print("Private key: d = %d" % d)
    
    return (N, e, d)

# Encrypt the message m (an integer) using the public key.
def encrypt(m, N, e):
    print("Encrypting message %d..." % m)
    c = pow(m, e, N)
    
    print("c = m^e mod N = %d^%d mod %d = %d\n" % (m, e, N, c))
    return c

# Decrypt the cyphertext c (an integer) using the private key.
def decrypt(c, N, d):
    print("Decrypting message %d..." % c)
    m = pow(c, d, N)
    
    print("m = c^d mod N = %d^%d mod %d = %d\n" % (c, d, N, m))
    return m

# Find the private key from the public key. This runs in expoential time!
def crack(N, e):
    print("Calculating the private key from the public key...")
    
    # The private key d is the multiplicative inverse of e mod phi.
    # In order to calculate phi, we must find the prime factors of N. That's the hard part!
    p, q = dual_factor(N)
    
    # With p, q, and e, we can now trivially calculate the private key.
    phi = (p-1)*(q-1)
    d = ex_gcd(e, phi, False)[1]
    
    print("The prime factors of N = %d are p = %d, q = %d" % (N, p, q))
    print("Phi must be %d. The multiplicative inverse of e = %d mod %d is the private key, d = %d." % (phi, e, phi, d))
    
    return d
    
# Generate keys where N is at most 6 decimal digits long.
N, e, d = gen_keys(5)

print("")

# Our message
m = 12345

# Encrypt with public key.
c = encrypt(m, N, e)

# Decrypt with private key.
m2 = decrypt(c, N, d)

# Calculate the private key from the public key.
d = crack(N, e)