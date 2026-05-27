# =============================================================================
#  Group Modification Name: "SHABUL" 
#
#  MOD 1 — Key Stretching via SHA-256 Hash Chain        (before key schedule)
#  MOD 2 — Pre-IP Key Whitening XOR                     (before Initial Permutation)
#  MOD 3 — S-Box Output Bit Rotation + String Reverse   (inside Feistel rounds)
#  MOD 4 — Post-FP Key Whitening XOR                    (BEFORE MOD 5)
#  MOD 5 - FP Reversal                                  (After Final Permutation)
# =============================================================================

import hashlib  # ============================================================ MOD4: needed for SHA-256 key stretching

# ── Conversion Helpers ────────────────────────────────────────────────────────
def hex2bin(s):
    mp = {'0':"0000",'1':"0001",'2':"0010",'3':"0011",'4':"0100",'5':"0101",
          '6':"0110",'7':"0111",'8':"1000",'9':"1001",'A':"1010",'B':"1011",
          'C':"1100",'D':"1101",'E':"1110",'F':"1111"}
    return "".join(mp[c] for c in s)

def bin2hex(s):
    mp = {"0000":'0',"0001":'1',"0010":'2',"0011":'3',"0100":'4',"0101":'5',
          "0110":'6',"0111":'7',"1000":'8',"1001":'9',"1010":'A',"1011":'B',
          "1100":'C',"1101":'D',"1110":'E',"1111":'F'}
    return "".join(mp[s[i:i+4]] for i in range(0, len(s), 4))

def bin2dec(binary):
    decimal, i, v = 0, 0, int(binary)
    while v:
        decimal += v % 10 * pow(2, i)
        v //= 10; i += 1
    return decimal

def dec2bin(num):
    r = bin(num).replace("0b", "")
    while len(r) < 4: r = '0' + r
    return r

def permute(k, arr, n):   return "".join(k[arr[i]-1] for i in range(n))
def shift_left(k, n):     n %= len(k); return k[n:] + k[:n]
def xor(a, b):            return "".join("0" if a[i]==b[i] else "1" for i in range(len(a)))
def bit_diff(a, b):       return sum(1 for i in range(len(a)) if a[i] != b[i])

# ── DES Standard Tables ───────────────────────────────────────────────────────
initial_perm = [58,50,42,34,26,18,10,2,60,52,44,36,28,20,12,4,
                62,54,46,38,30,22,14,6,64,56,48,40,32,24,16,8,
                57,49,41,33,25,17,9,1,59,51,43,35,27,19,11,3,
                61,53,45,37,29,21,13,5,63,55,47,39,31,23,15,7]

exp_d = [32,1,2,3,4,5,4,5,6,7,8,9,8,9,10,11,12,13,12,13,14,15,16,17,
         16,17,18,19,20,21,20,21,22,23,24,25,24,25,26,27,28,29,28,29,30,31,32,1]

per = [16,7,20,21,29,12,28,17,1,15,23,26,5,18,31,10,
       2,8,24,14,32,27,3,9,19,13,30,6,22,11,4,25]

sbox = [
  [[14,4,13,1,2,15,11,8,3,10,6,12,5,9,0,7],[0,15,7,4,14,2,13,1,10,6,12,11,9,5,3,8],
   [4,1,14,8,13,6,2,11,15,12,9,7,3,10,5,0],[15,12,8,2,4,9,1,7,5,11,3,14,10,0,6,13]],
  [[15,1,8,14,6,11,3,4,9,7,2,13,12,0,5,10],[3,13,4,7,15,2,8,14,12,0,1,10,6,9,11,5],
   [0,14,7,11,10,4,13,1,5,8,12,6,9,3,2,15],[13,8,10,1,3,15,4,2,11,6,7,12,0,5,14,9]],
  [[10,0,9,14,6,3,15,5,1,13,12,7,11,4,2,8],[13,7,0,9,3,4,6,10,2,8,5,14,12,11,15,1],
   [13,6,4,9,8,15,3,0,11,1,2,12,5,10,14,7],[1,10,13,0,6,9,8,7,4,15,14,3,11,5,2,12]],
  [[7,13,14,3,0,6,9,10,1,2,8,5,11,12,4,15],[13,8,11,5,6,15,0,3,4,7,2,12,1,10,14,9],
   [10,6,9,0,12,11,7,13,15,1,3,14,5,2,8,4],[3,15,0,6,10,1,13,8,9,4,5,11,12,7,2,14]],
  [[2,12,4,1,7,10,11,6,8,5,3,15,13,0,14,9],[14,11,2,12,4,7,13,1,5,0,15,10,3,9,8,6],
   [4,2,1,11,10,13,7,8,15,9,12,5,6,3,0,14],[11,8,12,7,1,14,2,13,6,15,0,9,10,4,5,3]],
  [[12,1,10,15,9,2,6,8,0,13,3,4,14,7,5,11],[10,15,4,2,7,12,9,5,6,1,13,14,0,11,3,8],
   [9,14,15,5,2,8,12,3,7,0,4,10,1,13,11,6],[4,3,2,12,9,5,15,10,11,14,1,7,6,0,8,13]],
  [[4,11,2,14,15,0,8,13,3,12,9,7,5,10,6,1],[13,0,11,7,4,9,1,10,14,3,5,12,2,15,8,6],
   [1,4,11,13,12,3,7,14,10,15,6,8,0,5,9,2],[6,11,13,8,1,4,10,7,9,5,0,15,14,2,3,12]],
  [[13,2,8,4,6,15,11,1,10,9,3,14,5,0,12,7],[1,15,13,8,10,3,7,4,12,5,6,11,0,14,9,2],
   [7,11,4,1,9,12,14,2,0,6,10,13,15,3,5,8],[2,1,14,7,4,10,8,13,15,12,9,0,3,5,6,11]]
]

final_perm = [40,8,48,16,56,24,64,32,39,7,47,15,55,23,63,31,
              38,6,46,14,54,22,62,30,37,5,45,13,53,21,61,29,
              36,4,44,12,52,20,60,28,35,3,43,11,51,19,59,27,
              34,2,42,10,50,18,58,26,33,1,41,9,49,17,57,25]

# ── Key Schedule ──────────────────────────────────────────────────────────────
keyp = [57,49,41,33,25,17,9,1,58,50,42,34,26,18,10,2,59,51,43,35,27,19,11,3,            #=================== PERMUTATED CHOICE 1
        60,52,44,36,63,55,47,39,31,23,15,7,62,54,46,38,30,22,14,6,61,53,45,37,
        29,21,13,5,28,20,12,4]
key_comp = [14,17,11,24,1,5,3,28,15,6,21,10,23,19,12,4,26,8,16,7,27,20,13,2,
            41,52,31,37,47,55,30,40,51,45,33,48,44,49,39,56,34,53,46,42,50,36,29,32]   #=================== PERMUTATED CHOICE 2
shift_table = [1,1,2,2,2,2,2,2,1,2,2,2,2,2,2,1]

# ══════════════════════════════════════════════════════════════════════════════
# MODIFICATION 1 — Key Stretching via SHA-256 Hash Chain
# ══════════════════════════════════════════════════════════════════════════════
def stretch_key(key_hex, iterations=100_000):
    """
    MOD4: Hardens the master key against brute-force by running it through
    a SHA-256 hash chain 'iterations' times before it enters the key schedule.

    Steps:
      1. Convert hex key string → raw bytes  (e.g. "AABB..." → b'\\xaa\\xbb...')
      2. Hash the bytes with SHA-256 → get 32 new bytes
      3. Feed those 32 bytes back into SHA-256 → repeat 'iterations' times
      4. Take the first 8 bytes of the final hash → convert back to hex string

    Effect on brute-force:
      Each attacker guess now costs 'iterations' SHA-256 operations instead of 1.
      At 100,000 iterations: 1B guesses/sec → 10,000 guesses/sec effectively.
    """
    k = bytes.fromhex(key_hex)          # Step 1: hex string → raw bytes
    for _ in range(iterations):         # Step 2-3: hash chain loop
        k = hashlib.sha256(k).digest()  #   sha256().digest() returns 32 raw bytes
    return k[:8].hex().upper()          # Step 4: first 8 bytes → hex string (64-bit DES key)

def generate_subkeys(key_hex):
    key_bin = hex2bin(key_hex)
    key_56  = permute(key_bin, keyp, 56)
    lk, rk  = key_56[:28], key_56[28:]
    rkb = []
    rk_hex = []
    for s in shift_table:
        lk = shift_left(lk, s)
        rk = shift_left(rk, s)
        round_key = permute(lk + rk, key_comp, 48)
        rkb.append(round_key)
        rk_hex.append(bin2hex(round_key))
    return rkb, rk_hex

# ══════════════════════════════════════════════════════════════════════════════
# MODIFICATION 2 & 3 — Key Whitening Keys
# ══════════════════════════════════════════════════════════════════════════════
def make_wk1(rkb):
    """MOD2: Pre-IP whitening key derived from K16 (last subkey, 48-bit → 64-bit)"""
    k = rkb[15]; return k + k[:16]

def make_wk2(rkb):
    """MOD3: Post-FP whitening key derived from K1 (first subkey, 48-bit → 64-bit)"""
    k = rkb[0];  return k + k[:16]

# ── Feistel f-function (shared) ───────────────────────────────────────────────
def feistel_f(right, round_key, modified):
    right_expanded = permute(right, exp_d, 48)
    xor_x          = xor(right_expanded, round_key)
    sbox_str = ""
    for j in range(8):
        row = bin2dec(xor_x[j*6] + xor_x[j*6+5])
        col = bin2dec(xor_x[j*6+1] + xor_x[j*6+2] + xor_x[j*6+3] + xor_x[j*6+4])
        sbox_str += dec2bin(sbox[j][row][col])
    if modified:
        # MOD4 and 5: S-Box Output Bit Rotation + Reverse
        sbox_str = sbox_str[3:] + sbox_str[:3]   # Left-rotate 3 bits
        sbox_str = sbox_str[::-1]                  # Reverse entire string
    return permute(sbox_str, per, 32)

def feistel_f_inv(right, round_key, modified):
    right_expanded = permute(right, exp_d, 48)
    xor_x          = xor(right_expanded, round_key)
    sbox_str = ""
    for j in range(8):
        row = bin2dec(xor_x[j*6] + xor_x[j*6+5])
        col = bin2dec(xor_x[j*6+1] + xor_x[j*6+2] + xor_x[j*6+3] + xor_x[j*6+4])
        sbox_str += dec2bin(sbox[j][row][col])
    if modified:
        # MOD5 inverse
        sbox_str = sbox_str[::-1]                  # Undo reverse
        sbox_str = sbox_str[-3:] + sbox_str[:-3]  # Right-rotate 3 (undo left-rotate)
    return permute(sbox_str, per, 32)

# ── 16 Feistel Rounds ─────────────────────────────────────────────────────────
def feistel_rounds(left, right, rkb, rk_hex, is_decrypt, modified, collect=None):
    for i in range(16):
        f_out = (feistel_f_inv if is_decrypt else feistel_f)(right, rkb[i], modified)
        left  = xor(left, f_out)
        if i != 15:
            left, right = right, left
        if collect is not None:
            collect.append((bin2hex(left), bin2hex(right)))
    return left, right

# ── Standard DES Encryption/Decryption (no modifications) ────────────────────
def encrypt_std(pt_hex, rkb, rk_hex):
    tb = permute(hex2bin(pt_hex), initial_perm, 64)
    L, R = tb[:32], tb[32:]
    L, R = feistel_rounds(L, R, rkb, rk_hex, False, False)
    return bin2hex(permute(L + R, final_perm, 64))

def decrypt_std(ct_hex, rkb, rk_hex):
    tb = permute(hex2bin(ct_hex), initial_perm, 64)
    L, R = tb[:32], tb[32:]
    L, R = feistel_rounds(L, R, rkb[::-1], rk_hex[::-1], True, False)
    return bin2hex(permute(L + R, final_perm, 64))

# Encryption/Decryption (all modifications) ────────────────────────
def encrypt(pt_hex, rkb, rk_hex, collect=None): # ══════════════════════════════════════════════════════════════════════════════ encryption
    wk1, wk2 = make_wk1(rkb), make_wk2(rkb)
    tb = xor(hex2bin(pt_hex), wk1)             # MOD2: Pre-IP whitening
    tb = permute(tb, initial_perm, 64)
    L, R = tb[:32], tb[32:]
    L, R = feistel_rounds(L, R, rkb, rk_hex, False, True, collect)
    ft = permute(L + R, final_perm, 64)
    ft = xor(ft, wk2)                          # MOD4: Post-FP whitening
    ft = ft[::-1]                              # MOD5 outer reverse
    return bin2hex(ft)

def decrypt(ct_hex, rkb, rk_hex): # ══════════════════════════════════════════════════════════════════════════════ decryption
    wk1, wk2 = make_wk1(rkb), make_wk2(rkb)
    tb = hex2bin(ct_hex)[::-1]                 # Undo MOD5 outer reverse + convert hex to bin
    tb = xor(tb, wk2)                          # Undo MOD2 using whitening key 2
    tb = permute(tb, initial_perm, 64)
    L, R = tb[:32], tb[32:]                    # split 64bit to 32 bit same as encrypting
    L, R = feistel_rounds(L, R, rkb[::-1], rk_hex[::-1], True, True)    #[::-1]right rotate 3 then reverse
    ft = permute(L + R, final_perm, 64)
    ft = xor(ft, wk1)                          # Undo MOD3 by xor'ing ft with whitening key 1
    return bin2hex(ft)    # decrypted pt

# ══════════════════════════════════════════════════════════════════════════════
if __name__ == "__main__":
    KEY        = "AABB09182736CCDD"  # ======================================== HARD CODED MASTER KEY
    PT         = "123456ABCD132536"
    ITERATIONS = 100_000             # ======================================== MOD4: adjust depending on needs (higher = slower brute-force)

    # ── MOD1: Key Stretching ──────────────────────────────────────────────────
    print("=== MOD1: Key Stretching ===")
    print(f"Original Key  : {KEY}")
    import time
    t_start      = time.time()
    STRETCHED_KEY = stretch_key(KEY, ITERATIONS)   # ========================== STRETCH THE KEY before subkey generation
    t_end        = time.time()
    print(f"Stretched Key : {STRETCHED_KEY}  ({ITERATIONS:,} SHA-256 iterations)")
    print(f"Stretch Time  : {(t_end - t_start)*1000:.1f} ms")
    print(f"Effective brute-force speed: ~{1_000_000_000 // ITERATIONS:,}") 

    # ── All subkeys now derived from STRETCHED_KEY, not raw KEY ──────────────
    rkb, rk_hex = generate_subkeys(STRETCHED_KEY)  # ========================== MOD1: use stretched key here
    wk1 = make_wk1(rkb)     # ================================================ CALL WK1 CREATION FUNCTION
    wk2 = make_wk2(rkb)     # ================================================ CALL WK2 CREATION FUNCTION

    # ── Header ────────────────────────────────────────────────────────────────
    print("\n=== SHA-BUL (MOD1 + MOD2 + MOD3 + MOD4 + MOD5) ===")
    print(f"Key (original) : {KEY}")
    print(f"Key (stretched): {STRETCHED_KEY}")
    print(f"PT             : {PT}")
    print(f"WK1            : {bin2hex(wk1)}")
    print(f"WK2            : {bin2hex(wk2)}")

    # ── Standard DES ──────────────────────────────────────────────────────────
    print("\n=== Standard DES ===")
    CT_STD = encrypt_std(PT, rkb, rk_hex)
    DT_STD = decrypt_std(CT_STD, rkb, rk_hex)
    print(f"CT  : {CT_STD}")
    print(f"DT  : {DT_STD}")
    print(f"Match: {'PASS' if DT_STD == PT else 'FAIL'}")

    # ── SHA-BUL ───────────────────────────────────────────────────────────────
    print("\n=== SHA-BUL Encryption ===")
    rounds_mod = []
    CT = encrypt(PT, rkb, rk_hex, collect=rounds_mod)
    DT = decrypt(CT, rkb, rk_hex)
    print(f"CT  : {CT}")
    print(f"DT  : {DT}")
    print(f"Match: {'PASS' if DT == PT else 'FAIL'}")

    # ── Plaintext Avalanche ───────────────────────────────────────────────────
    # ── Plaintext Avalanche ───────────────────────────────────────────────────
    print("\n=== Avalanche: 1-bit Plaintext Change (SHA-BUL) ===")
    PT2 = "123456ABCD132537"
    rounds_pt1 = []
    rounds_pt2 = []
    CT2 = encrypt(PT2, rkb, rk_hex, collect=rounds_pt2)
    encrypt(PT, rkb, rk_hex, collect=rounds_pt1)
    pt_diff = bit_diff(hex2bin(CT), hex2bin(CT2))
    print(f"PT1: {PT} -> {CT}")
    print(f"PT2: {PT2} -> {CT2}")
    print(f"Bits differ: {pt_diff}/64 ({pt_diff/64*100:.1f}%)")

    print(f"\n{'Rnd':>3}  {'Bits Differ':>11}  {'%':>6}")
    print("-" * 25)
    for i in range(16):
        l1, r1 = rounds_pt1[i]
        l2, r2 = rounds_pt2[i]
        d = bit_diff(hex2bin(l1) + hex2bin(r1), hex2bin(l2) + hex2bin(r2))
        print(f"{i+1:>3}  {d:>6} / 64  {d/64*100:>5.1f}%")
    print(f"CT   {pt_diff:>6} / 64  {pt_diff/64*100:>5.1f}%")

    # ── Key Avalanche ─────────────────────────────────────────────────────────
    print("\n=== Avalanche: 1-bit Key Change (SHA-BUL) ===")
    kb   = hex2bin(KEY)
    fk   = kb[:8] + ('1' if kb[8]=='0' else '0') + kb[9:]   # takes bit 8 then flips == if 1 > 0 then binary
    KEY2 = bin2hex(fk)

    # MOD1: stretch the flipped key too before generating its subkeys
    STRETCHED_KEY2 = stretch_key(KEY2, ITERATIONS)  
    rkb2, rk_hex2  = generate_subkeys(STRETCHED_KEY2)

    rounds_key1 = []
    rounds_key2 = []
    encrypt(PT, rkb,  rk_hex,  collect=rounds_key1)
    CT3 = encrypt(PT, rkb2, rk_hex2, collect=rounds_key2)
    k_diff = bit_diff(hex2bin(CT), hex2bin(CT3))
    print(f"KEY1 (original) : {KEY}  ->  stretched: {STRETCHED_KEY}  ->  CT: {CT}")
    print(f"KEY2 (1-bit off): {KEY2}  ->  stretched: {STRETCHED_KEY2}  ->  CT: {CT3}")
    print(f"Bits differ: {k_diff}/64 ({k_diff/64*100:.1f}%)")

    print(f"\n{'Rnd':>3}  {'Bits Differ':>11}  {'%':>6}")
    print("-" * 25)
    for i in range(16):
        l1, r1 = rounds_key1[i]
        l2, r2 = rounds_key2[i]
        d = bit_diff(hex2bin(l1) + hex2bin(r1), hex2bin(l2) + hex2bin(r2))
        print(f"{i+1:>3}  {d:>6} / 64  {d/64*100:>5.1f}%")
    print(f"CT   {k_diff:>6} / 64  {k_diff/64*100:>5.1f}%")