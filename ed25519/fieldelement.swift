//
//  FieldElement.swift
//  ErisKeys
//
//  Created by Alex Tran Qui on 07/06/16.
//  Port of go implementation of ed25519
//  Copyright © 2016 Katalysis / Alex Tran Qui  (alex.tranqui@gmail.com). All rights reserved.
//
//  Licensed under the Apache License, Version 2.0 (the "License");
//  you may not use this file except in compliance with the License.
//  You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
//  Unless required by applicable law or agreed to in writing, software
//  distributed under the License is distributed on an "AS IS" BASIS,
//  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//  See the License for the specific language governing permissions and
//  limitations under the License.
//
//  Implements the Ed25519 signature algorithm. See
// http://ed25519.cr.yp.to/.

// This code is a port of the public domain, "ref10" implementation of ed25519
// from SUPERCOP.

import Foundation


typealias FieldElement = [Int32]

func FeZero(_ fe: inout FieldElement) {
    assert(fe.count == 10)
    for i in 0..<fe.count {
        fe[i] = 0
    }
}

func FeOne(_ fe: inout FieldElement) {
    assert(fe.count == 10)
    FeZero(&fe)
    fe[0] = 1
}

func FeAdd(_ dst: inout FieldElement,_  a: FieldElement, _ b: FieldElement) {
    assert(dst.count == 10)
    for i in 0..<dst.count {
        dst[i] = a[i] + b[i]
    }
}

func FeSub(_ dst: inout FieldElement,_  a: FieldElement, _ b: FieldElement) {
    assert(dst.count == 10)
    for i in 0..<dst.count {
        dst[i] = a[i] - b[i]
    }
}

func FeCopy(_ dst: inout FieldElement, _ src: FieldElement) {
    assert(dst.count == 10)
    for i in 0..<dst.count {
        dst[i] = src[i]
    }
}

// Replace (f,g) with (g,g) if b == 1;
// replace (f,g) with (f,g) if b == 0.
//
// Preconditions: b in {0,1}.
func FeCMove(_ f: inout FieldElement, _ g: FieldElement, _ b: Int32) {
    var x = FieldElement(repeating: 0, count: 10)
    let c = -b
    for i in 0..<x.count {
        x[i] = c & (f[i] ^ g[i])
    }
    
    for i in 0..<x.count {
        f[i] ^= x[i]
    }
}

func load3(_ byteArray: [byte]) -> Int64 {
    var r: Int64
    r = Int64(byteArray[0])
    r |= Int64(byteArray[1]) << 8
    r |= Int64(byteArray[2]) << 16
    return r
}

func load3(_ byteArraySlice: ArraySlice<byte>) -> Int64 {
    return load3(Array(byteArraySlice))
}

func load4(_ byteArray: [byte]) -> Int64 {
    var r: Int64
    r = Int64(byteArray[0])
    r |= Int64(byteArray[1]) << 8
    r |= Int64(byteArray[2]) << 16
    r |= Int64(byteArray[3]) << 24
    return r
}

func load4(_ byteArraySlice: ArraySlice<byte>) -> Int64 {
    return load4(Array(byteArraySlice))
}

func FeFromBytes(_ dst: inout FieldElement, _ src: [byte]) {
    let last = src.count - 1
    var h0 = load4(src)
    var h1 = load3(src[4...last]) << 6
    var h2 = load3(src[7...last]) << 5
    var h3 = load3(src[10...last]) << 3
    var h4 = load3(src[13...last]) << 2
    var h5 = load4(src[16...last])
    var h6 = load3(src[20...last]) << 7
    var h7 = load3(src[23...last]) << 5
    var h8 = load3(src[26...last]) << 4
    var h9 = (load3(src[29...last]) & 8388607) << 2
    
    var carry = [Int64](repeating: 0, count: 10)
    carry[9] = (h9 + 1<<24) >> 25
    h0 += carry[9] * 19
    h9 -= carry[9] << 25
    carry[1] = (h1 + 1<<24) >> 25
    h2 += carry[1]
    h1 -= carry[1] << 25
    carry[3] = (h3 + 1<<24) >> 25
    h4 += carry[3]
    h3 -= carry[3] << 25
    carry[5] = (h5 + 1<<24) >> 25
    h6 += carry[5]
    h5 -= carry[5] << 25
    carry[7] = (h7 + 1<<24) >> 25
    h8 += carry[7]
    h7 -= carry[7] << 25
    
    carry[0] = (h0 + 1<<25) >> 26
    h1 += carry[0]
    h0 -= carry[0] << 26
    carry[2] = (h2 + 1<<25) >> 26
    h3 += carry[2]
    h2 -= carry[2] << 26
    carry[4] = (h4 + 1<<25) >> 26
    h5 += carry[4]
    h4 -= carry[4] << 26
    carry[6] = (h6 + 1<<25) >> 26
    h7 += carry[6]
    h6 -= carry[6] << 26
    carry[8] = (h8 + 1<<25) >> 26
    h9 += carry[8]
    h8 -= carry[8] << 26
    
    dst[0] = Int32(h0)
    dst[1] = Int32(h1)
    dst[2] = Int32(h2)
    dst[3] = Int32(h3)
    dst[4] = Int32(h4)
    dst[5] = Int32(h5)
    dst[6] = Int32(h6)
    dst[7] = Int32(h7)
    dst[8] = Int32(h8)
    dst[9] = Int32(h9)
}

// FeToBytes marshals h to s.
// Preconditions:
//   |h| bounded by 1.1*2^25,1.1*2^24,1.1*2^25,1.1*2^24,etc.
//
// Write p=2^255-19; q=floor(h/p).
// Basic claim: q = floor(2^(-255)(h + 19 2^(-25)h9 + 2^(-1))).
//
// Proof:
//   Have |h|<=p so |q|<=1 so |19^2 2^(-255) q|<1/4.
//   Also have |h-2^230 h9|<2^230 so |19 2^(-255)(h-2^230 h9)|<1/4.
//
//   Write y=2^(-1)-19^2 2^(-255)q-19 2^(-255)(h-2^230 h9).
//   Then 0<y<1.
//
//   Write r=h-pq.
//   Have 0<=r<=p-1=2^255-20.
//   Thus 0<=r+19(2^-255)r<r+19(2^-255)2^255<=2^255-1.
//
//   Write x=r+19(2^-255)r+y.
//   Then 0<x<2^255 so floor(2^(-255)x) = 0 so floor(q+2^(-255)x) = q.
//
//   Have q+2^(-255)x = 2^(-255)(h + 19 2^(-25) h9 + 2^(-1))
//   so floor(2^(-255)(h + 19 2^(-25) h9 + 2^(-1))) = q.
func FeToBytes(_ s: inout [byte], _ h: FieldElement) {
    var carry = [Int64](repeating: 0, count: 10)
    
    var h0 = Int64(h[0])
    var h1 = Int64(h[1])
    var h2 = Int64(h[2])
    var h3 = Int64(h[3])
    var h4 = Int64(h[4])
    var h5 = Int64(h[5])
    var h6 = Int64(h[6])
    var h7 = Int64(h[7])
    var h8 = Int64(h[8])
    var h9 = Int64(h[9])
    
    
    var q: Int64 = (19*h9 + (1 << 24)) >> 25
    q = (h0 + q) >> 26
    q = (h1 + q) >> 25
    q = (h2 + q) >> 26
    q = (h3 + q) >> 25
    q = (h4 + q) >> 26
    q = (h5 + q) >> 25
    q = (h6 + q) >> 26
    q = (h7 + q) >> 25
    q = (h8 + q) >> 26
    q = (h9 + q) >> 25
    
    // Goal: Output h-(2^255-19)q, which is between 0 and 2^255-20.
    h0 += 19 * q
    // Goal: Output h-2^255 q, which is between 0 and 2^255-20.
    
    carry[0] = h0 >> 26
    h1 += carry[0]
    h0 -= carry[0] << 26
    carry[1] = h1 >> 25
    h2 += carry[1]
    h1 -= carry[1] << 25
    carry[2] = h2 >> 26
    h3 += carry[2]
    h2 -= carry[2] << 26
    carry[3] = h3 >> 25
    h4 += carry[3]
    h3 -= carry[3] << 25
    carry[4] = h4 >> 26
    h5 += carry[4]
    h4 -= carry[4] << 26
    carry[5] = h5 >> 25
    h6 += carry[5]
    h5 -= carry[5] << 25
    carry[6] = h6 >> 26
    h7 += carry[6]
    h6 -= carry[6] << 26
    carry[7] = h7 >> 25
    h8 += carry[7]
    h7 -= carry[7] << 25
    carry[8] = h8 >> 26
    h9 += carry[8]
    h8 -= carry[8] << 26
    carry[9] = h9 >> 25
    h9 -= carry[9] << 25
    // h10 = carry9
    
    // Goal: Output h[0]+...+2^255 h10-2^255 q, which is between 0 and 2^255-20.
    // Have h[0]+...+2^230 h[9] between 0 and 2^255-1;
    // evidently 2^255 h10-2^255 q = 0.
    // Goal: Output h[0]+...+2^230 h[9].
    
    s[0] = byte(h0 >> 0 % 256)
    s[1] = byte(h0 >> 8 % 256)
    s[2] = byte(h0 >> 16 % 256)
    s[3] = byte(((h0 >> 24) | (h1 << 2)) % 256)
    s[4] = byte(h1 >> 6 % 256)
    s[5] = byte(h1 >> 14 % 256)
    s[6] = byte(((h1 >> 22) | (h2 << 3)) % 256)
    s[7] = byte(h2 >> 5 % 256)
    s[8] = byte(h2 >> 13 % 256)
    s[9] = byte(((h2 >> 21) | (h3 << 5)) % 256)
    s[10] = byte(h3 >> 3 % 256)
    s[11] = byte(h3 >> 11 % 256)
    s[12] = byte(((h3 >> 19) | (h4 << 6)) % 256)
    s[13] = byte(h4 >> 2 % 256)
    s[14] = byte(h4 >> 10 % 256)
    s[15] = byte(h4 >> 18 % 256)
    s[16] = byte(h5 >> 0 % 256)
    s[17] = byte(h5 >> 8 % 256)
    s[18] = byte(h5 >> 16 % 256)
    s[19] = byte(((h5 >> 24) | (h6 << 1)) % 256)
    s[20] = byte(h6 >> 7 % 256)
    s[21] = byte(h6 >> 15 % 256)
    s[22] = byte(((h6 >> 23) | (h7 << 3)) % 256)
    s[23] = byte(h7 >> 5 % 256)
    s[24] = byte(h7 >> 13 % 256)
    s[25] = byte(((h7 >> 21) | (h8 << 4)) % 256)
    s[26] = byte(h8 >> 4 % 256)
    s[27] = byte(h8 >> 12 % 256)
    s[28] = byte(((h8 >> 20) | (h9 << 6)) % 256)
    s[29] = byte(h9 >> 2 % 256)
    s[30] = byte(h9 >> 10 % 256)
    s[31] = byte(h9 >> 18 % 256)
}

func FeIsNegative(_ f: inout FieldElement) -> byte {
    var s = [byte](repeating: 0, count: 32)
    FeToBytes(&s, f)
    return s[0] & 1
}

func FeIsNonZero(_ f: inout FieldElement) -> Int32 {
    var s = [byte](repeating: 0, count: 32)
    FeToBytes(&s, f)
    var x: UInt8 = 0
    for b in s {
        x |= b
    }
    x |= x >> 4
    x |= x >> 2
    x |= x >> 1
    return Int32(x & 1)
}

// FeNeg sets h = -f
//
// Preconditions:
//    |f| bounded by 1.1*2^25,1.1*2^24,1.1*2^25,1.1*2^24,etc.
//
// Postconditions:
//    |h| bounded by 1.1*2^25,1.1*2^24,1.1*2^25,1.1*2^24,etc.
func FeNeg(_ h: inout FieldElement, _ f: FieldElement) {
    for i in 0..<f.count {
        h[i] = -f[i]
    }
}

// FeMul calculates h = f * g
// Can overlap h with f or g.
//
// Preconditions:
//    |f| bounded by 1.1*2^26,1.1*2^25,1.1*2^26,1.1*2^25,etc.
//    |g| bounded by 1.1*2^26,1.1*2^25,1.1*2^26,1.1*2^25,etc.
//
// Postconditions:
//    |h| bounded by 1.1*2^25,1.1*2^24,1.1*2^25,1.1*2^24,etc.
//
// Notes on implementation strategy:
//
// Using schoolbook multiplication.
// Karatsuba would save a little in some cost models.
//
// Most multiplications by 2 and 19 are 32-bit precomputations;
// cheaper than 64-bit postcomputations.
//
// There is one remaining multiplication by 19 in the carry chain;
// one *19 precomputation can be merged into this,
// but the resulting data flow is considerably less clean.
//
// There are 12 carries below.
// 10 of them are 2-way parallelizable and vectorizable.
// Can get away with 11 carries, but then data flow is much deeper.
//
// With tighter constraints on inputs can squeeze carries into Int32.
func FeMul(_ h: inout FieldElement, _ f: FieldElement, _ g: FieldElement) {
    let f0 = Int64(f[0])
    let f1 = Int64(f[1])
    let f2 = Int64(f[2])
    let f3 = Int64(f[3])
    let f4 = Int64(f[4])
    let f5 = Int64(f[5])
    let f6 = Int64(f[6])
    let f7 = Int64(f[7])
    let f8 = Int64(f[8])
    let f9 = Int64(f[9])
    
    let f1_2 = Int64(2 * f[1])
    let f3_2 = Int64(2 * f[3])
    let f5_2 = Int64(2 * f[5])
    let f7_2 = Int64(2 * f[7])
    let f9_2 = Int64(2 * f[9])
    
    let g0 = Int64(g[0])
    let g1 = Int64(g[1])
    let g2 = Int64(g[2])
    let g3 = Int64(g[3])
    let g4 = Int64(g[4])
    let g5 = Int64(g[5])
    let g6 = Int64(g[6])
    let g7 = Int64(g[7])
    let g8 = Int64(g[8])
    let g9 = Int64(g[9])
    
    let g1_19 = Int64(19 * g[1]) /* 1.4*2^29 */
    let g2_19 = Int64(19 * g[2]) /* 1.4*2^30; still ok */
    let g3_19 = Int64(19 * g[3])
    let g4_19 = Int64(19 * g[4])
    let g5_19 = Int64(19 * g[5])
    let g6_19 = Int64(19 * g[6])
    let g7_19 = Int64(19 * g[7])
    let g8_19 = Int64(19 * g[8])
    let g9_19 = Int64(19 * g[9])
    
    var h0 = f0*g0 + f1_2*g9_19 + f2*g8_19 + f3_2*g7_19 + f4*g6_19 + f5_2*g5_19 + f6*g4_19 + f7_2*g3_19 + f8*g2_19 + f9_2*g1_19
    var h1 = f0*g1 + f1*g0 + f2*g9_19 + f3*g8_19 + f4*g7_19 + f5*g6_19 + f6*g5_19 + f7*g4_19 + f8*g3_19 + f9*g2_19
    var h2 = f0*g2 + f1_2*g1 + f2*g0 + f3_2*g9_19 + f4*g8_19 + f5_2*g7_19 + f6*g6_19 + f7_2*g5_19 + f8*g4_19 + f9_2*g3_19
    var h3 = f0*g3 + f1*g2 + f2*g1 + f3*g0 + f4*g9_19 + f5*g8_19 + f6*g7_19 + f7*g6_19 + f8*g5_19 + f9*g4_19
    var h4 = f0*g4 + f1_2*g3 + f2*g2 + f3_2*g1 + f4*g0 + f5_2*g9_19 + f6*g8_19 + f7_2*g7_19 + f8*g6_19 + f9_2*g5_19
    var h5 = f0*g5 + f1*g4 + f2*g3 + f3*g2 + f4*g1 + f5*g0 + f6*g9_19 + f7*g8_19 + f8*g7_19 + f9*g6_19
    var h6 = f0*g6 + f1_2*g5 + f2*g4 + f3_2*g3 + f4*g2 + f5_2*g1 + f6*g0 + f7_2*g9_19 + f8*g8_19 + f9_2*g7_19
    var h7 = f0*g7 + f1*g6 + f2*g5 + f3*g4 + f4*g3 + f5*g2 + f6*g1 + f7*g0 + f8*g9_19 + f9*g8_19
    var h8 = f0*g8 + f1_2*g7 + f2*g6 + f3_2*g5 + f4*g4 + f5_2*g3 + f6*g2 + f7_2*g1 + f8*g0 + f9_2*g9_19
    var h9 = f0*g9 + f1*g8 + f2*g7 + f3*g6 + f4*g5 + f5*g4 + f6*g3 + f7*g2 + f8*g1 + f9*g0
    
    var carry = [Int64](repeating: 0, count: 10)
    
    /*
     |h0| <= (1.1*1.1*2^52*(1+19+19+19+19)+1.1*1.1*2^50*(38+38+38+38+38))
     i.e. |h0| <= 1.2*2^59; narrower ranges for h2, h4, h6, h8
     |h1| <= (1.1*1.1*2^51*(1+1+19+19+19+19+19+19+19+19))
     i.e. |h1| <= 1.5*2^58; narrower ranges for h3, h5, h7, h9
     */
    
    carry[0] = (h0 + (1 << 25)) >> 26
    h1 += carry[0]
    h0 -= carry[0] << 26
    carry[4] = (h4 + (1 << 25)) >> 26
    h5 += carry[4]
    h4 -= carry[4] << 26
    /* |h0| <= 2^25 */
    /* |h4| <= 2^25 */
    /* |h1| <= 1.51*2^58 */
    /* |h5| <= 1.51*2^58 */
    
    carry[1] = (h1 + (1 << 24)) >> 25
    h2 += carry[1]
    h1 -= carry[1] << 25
    carry[5] = (h5 + (1 << 24)) >> 25
    h6 += carry[5]
    h5 -= carry[5] << 25
    /* |h1| <= 2^24; from now on fits into Int32 */
    /* |h5| <= 2^24; from now on fits into Int32 */
    /* |h2| <= 1.21*2^59 */
    /* |h6| <= 1.21*2^59 */
    
    carry[2] = (h2 + (1 << 25)) >> 26
    h3 += carry[2]
    h2 -= carry[2] << 26
    carry[6] = (h6 + (1 << 25)) >> 26
    h7 += carry[6]
    h6 -= carry[6] << 26
    /* |h2| <= 2^25; from now on fits into Int32 unchanged */
    /* |h6| <= 2^25; from now on fits into Int32 unchanged */
    /* |h3| <= 1.51*2^58 */
    /* |h7| <= 1.51*2^58 */
    
    carry[3] = (h3 + (1 << 24)) >> 25
    h4 += carry[3]
    h3 -= carry[3] << 25
    carry[7] = (h7 + (1 << 24)) >> 25
    h8 += carry[7]
    h7 -= carry[7] << 25
    /* |h3| <= 2^24; from now on fits into Int32 unchanged */
    /* |h7| <= 2^24; from now on fits into Int32 unchanged */
    /* |h4| <= 1.52*2^33 */
    /* |h8| <= 1.52*2^33 */
    
    carry[4] = (h4 + (1 << 25)) >> 26
    h5 += carry[4]
    h4 -= carry[4] << 26
    carry[8] = (h8 + (1 << 25)) >> 26
    h9 += carry[8]
    h8 -= carry[8] << 26
    /* |h4| <= 2^25; from now on fits into Int32 unchanged */
    /* |h8| <= 2^25; from now on fits into Int32 unchanged */
    /* |h5| <= 1.01*2^24 */
    /* |h9| <= 1.51*2^58 */
    
    carry[9] = (h9 + (1 << 24)) >> 25
    h0 += carry[9] * 19
    h9 -= carry[9] << 25
    /* |h9| <= 2^24; from now on fits into Int32 unchanged */
    /* |h0| <= 1.8*2^37 */
    
    carry[0] = (h0 + (1 << 25)) >> 26
    h1 += carry[0]
    h0 -= carry[0] << 26
    /* |h0| <= 2^25; from now on fits into Int32 unchanged */
    /* |h1| <= 1.01*2^24 */
    
    h[0] = Int32(h0)
    h[1] = Int32(h1)
    h[2] = Int32(h2)
    h[3] = Int32(h3)
    h[4] = Int32(h4)
    h[5] = Int32(h5)
    h[6] = Int32(h6)
    h[7] = Int32(h7)
    h[8] = Int32(h8)
    h[9] = Int32(h9)
}

// FeSquare calculates h = f*f. Can overlap h with f.
//
// Preconditions:
//    |f| bounded by 1.1*2^26,1.1*2^25,1.1*2^26,1.1*2^25,etc.
//
// Postconditions:
//    |h| bounded by 1.1*2^25,1.1*2^24,1.1*2^25,1.1*2^24,etc.
func FeSquare(_ h: inout FieldElement,_ f: FieldElement) {
    let f0 = f[0]
    let f1 = f[1]
    let f2 = f[2]
    let f3 = f[3]
    let f4 = f[4]
    let f5 = f[5]
    let f6 = f[6]
    let f7 = f[7]
    let f8 = f[8]
    let f9 = f[9]
    let f0_2 = 2 * f0
    let f1_2 = 2 * f1
    let f2_2 = 2 * f2
    let f3_2 = 2 * f3
    let f4_2 = 2 * f4
    let f5_2 = 2 * f5
    let f6_2 = 2 * f6
    let f7_2 = 2 * f7
    let f5_38 = 38 * f5 // 1.31*2^30
    let f6_19 = 19 * f6 // 1.31*2^30
    let f7_38 = 38 * f7 // 1.31*2^30
    let f8_19 = 19 * f8 // 1.31*2^30
    let f9_38 = 38 * f9 // 1.31*2^30
    let f0f0 = Int64(f0) * Int64(f0)
    let f0f1_2 = Int64(f0_2) * Int64(f1)
    let f0f2_2 = Int64(f0_2) * Int64(f2)
    let f0f3_2 = Int64(f0_2) * Int64(f3)
    let f0f4_2 = Int64(f0_2) * Int64(f4)
    let f0f5_2 = Int64(f0_2) * Int64(f5)
    let f0f6_2 = Int64(f0_2) * Int64(f6)
    let f0f7_2 = Int64(f0_2) * Int64(f7)
    let f0f8_2 = Int64(f0_2) * Int64(f8)
    let f0f9_2 = Int64(f0_2) * Int64(f9)
    let f1f1_2 = Int64(f1_2) * Int64(f1)
    let f1f2_2 = Int64(f1_2) * Int64(f2)
    let f1f3_4 = Int64(f1_2) * Int64(f3_2)
    let f1f4_2 = Int64(f1_2) * Int64(f4)
    let f1f5_4 = Int64(f1_2) * Int64(f5_2)
    let f1f6_2 = Int64(f1_2) * Int64(f6)
    let f1f7_4 = Int64(f1_2) * Int64(f7_2)
    let f1f8_2 = Int64(f1_2) * Int64(f8)
    let f1f9_76 = Int64(f1_2) * Int64(f9_38)
    let f2f2 = Int64(f2) * Int64(f2)
    let f2f3_2 = Int64(f2_2) * Int64(f3)
    let f2f4_2 = Int64(f2_2) * Int64(f4)
    let f2f5_2 = Int64(f2_2) * Int64(f5)
    let f2f6_2 = Int64(f2_2) * Int64(f6)
    let f2f7_2 = Int64(f2_2) * Int64(f7)
    let f2f8_38 = Int64(f2_2) * Int64(f8_19)
    let f2f9_38 = Int64(f2) * Int64(f9_38)
    let f3f3_2 = Int64(f3_2) * Int64(f3)
    let f3f4_2 = Int64(f3_2) * Int64(f4)
    let f3f5_4 = Int64(f3_2) * Int64(f5_2)
    let f3f6_2 = Int64(f3_2) * Int64(f6)
    let f3f7_76 = Int64(f3_2) * Int64(f7_38)
    let f3f8_38 = Int64(f3_2) * Int64(f8_19)
    let f3f9_76 = Int64(f3_2) * Int64(f9_38)
    let f4f4 = Int64(f4) * Int64(f4)
    let f4f5_2 = Int64(f4_2) * Int64(f5)
    let f4f6_38 = Int64(f4_2) * Int64(f6_19)
    let f4f7_38 = Int64(f4) * Int64(f7_38)
    let f4f8_38 = Int64(f4_2) * Int64(f8_19)
    let f4f9_38 = Int64(f4) * Int64(f9_38)
    let f5f5_38 = Int64(f5) * Int64(f5_38)
    let f5f6_38 = Int64(f5_2) * Int64(f6_19)
    let f5f7_76 = Int64(f5_2) * Int64(f7_38)
    let f5f8_38 = Int64(f5_2) * Int64(f8_19)
    let f5f9_76 = Int64(f5_2) * Int64(f9_38)
    let f6f6_19 = Int64(f6) * Int64(f6_19)
    let f6f7_38 = Int64(f6) * Int64(f7_38)
    let f6f8_38 = Int64(f6_2) * Int64(f8_19)
    let f6f9_38 = Int64(f6) * Int64(f9_38)
    let f7f7_38 = Int64(f7) * Int64(f7_38)
    let f7f8_38 = Int64(f7_2) * Int64(f8_19)
    let f7f9_76 = Int64(f7_2) * Int64(f9_38)
    let f8f8_19 = Int64(f8) * Int64(f8_19)
    let f8f9_38 = Int64(f8) * Int64(f9_38)
    let f9f9_38 = Int64(f9) * Int64(f9_38)
    var h0 = f0f0 + f1f9_76 + f2f8_38 + f3f7_76 + f4f6_38 + f5f5_38
    var h1 = f0f1_2 + f2f9_38 + f3f8_38 + f4f7_38 + f5f6_38
    var h2 = f0f2_2 + f1f1_2 + f3f9_76 + f4f8_38 + f5f7_76 + f6f6_19
    var h3 = f0f3_2 + f1f2_2 + f4f9_38 + f5f8_38 + f6f7_38
    var h4 = f0f4_2 + f1f3_4 + f2f2 + f5f9_76 + f6f8_38 + f7f7_38
    var h5 = f0f5_2 + f1f4_2 + f2f3_2 + f6f9_38 + f7f8_38
    var h6 = f0f6_2 + f1f5_4 + f2f4_2 + f3f3_2 + f7f9_76 + f8f8_19
    var h7 = f0f7_2 + f1f6_2 + f2f5_2 + f3f4_2 + f8f9_38
    var h8 = f0f8_2 + f1f7_4 + f2f6_2 + f3f5_4 + f4f4 + f9f9_38
    var h9 = f0f9_2 + f1f8_2 + f2f7_2 + f3f6_2 + f4f5_2
    
    var carry = [Int64](repeating: 0, count: 10)
    
    carry[0] = (h0 + (1 << 25)) >> 26
    h1 += carry[0]
    h0 -= carry[0] << 26
    carry[4] = (h4 + (1 << 25)) >> 26
    h5 += carry[4]
    h4 -= carry[4] << 26
    
    carry[1] = (h1 + (1 << 24)) >> 25
    h2 += carry[1]
    h1 -= carry[1] << 25
    carry[5] = (h5 + (1 << 24)) >> 25
    h6 += carry[5]
    h5 -= carry[5] << 25
    
    carry[2] = (h2 + (1 << 25)) >> 26
    h3 += carry[2]
    h2 -= carry[2] << 26
    carry[6] = (h6 + (1 << 25)) >> 26
    h7 += carry[6]
    h6 -= carry[6] << 26
    
    carry[3] = (h3 + (1 << 24)) >> 25
    h4 += carry[3]
    h3 -= carry[3] << 25
    carry[7] = (h7 + (1 << 24)) >> 25
    h8 += carry[7]
    h7 -= carry[7] << 25
    
    carry[4] = (h4 + (1 << 25)) >> 26
    h5 += carry[4]
    h4 -= carry[4] << 26
    carry[8] = (h8 + (1 << 25)) >> 26
    h9 += carry[8]
    h8 -= carry[8] << 26
    
    carry[9] = (h9 + (1 << 24)) >> 25
    h0 += carry[9] * 19
    h9 -= carry[9] << 25
    
    carry[0] = (h0 + (1 << 25)) >> 26
    h1 += carry[0]
    h0 -= carry[0] << 26
    
    h[0] = Int32(h0)
    h[1] = Int32(h1)
    h[2] = Int32(h2)
    h[3] = Int32(h3)
    h[4] = Int32(h4)
    h[5] = Int32(h5)
    h[6] = Int32(h6)
    h[7] = Int32(h7)
    h[8] = Int32(h8)
    h[9] = Int32(h9)
}

// FeSquare2 sets h = 2 * f * f
//
// Can overlap h with f.
//
// Preconditions:
//    |f| bounded by 1.65*2^26,1.65*2^25,1.65*2^26,1.65*2^25,etc.
//
// Postconditions:
//    |h| bounded by 1.01*2^25,1.01*2^24,1.01*2^25,1.01*2^24,etc.
// See fe_mul.c for discussion of implementation strategy.
func FeSquare2(_ h: inout FieldElement, _ f: FieldElement) {
    let f0 = f[0]
    let f1 = f[1]
    let f2 = f[2]
    let f3 = f[3]
    let f4 = f[4]
    let f5 = f[5]
    let f6 = f[6]
    let f7 = f[7]
    let f8 = f[8]
    let f9 = f[9]
    let f0_2 = 2 * f0
    let f1_2 = 2 * f1
    let f2_2 = 2 * f2
    let f3_2 = 2 * f3
    let f4_2 = 2 * f4
    let f5_2 = 2 * f5
    let f6_2 = 2 * f6
    let f7_2 = 2 * f7
    let f5_38 = 38 * f5 // 1.959375*2^30
    let f6_19 = 19 * f6 // 1.959375*2^30
    let f7_38 = 38 * f7 // 1.959375*2^30
    let f8_19 = 19 * f8 // 1.959375*2^30
    let f9_38 = 38 * f9 // 1.959375*2^30
    let f0f0 = Int64(f0) * Int64(f0)
    let f0f1_2 = Int64(f0_2) * Int64(f1)
    let f0f2_2 = Int64(f0_2) * Int64(f2)
    let f0f3_2 = Int64(f0_2) * Int64(f3)
    let f0f4_2 = Int64(f0_2) * Int64(f4)
    let f0f5_2 = Int64(f0_2) * Int64(f5)
    let f0f6_2 = Int64(f0_2) * Int64(f6)
    let f0f7_2 = Int64(f0_2) * Int64(f7)
    let f0f8_2 = Int64(f0_2) * Int64(f8)
    let f0f9_2 = Int64(f0_2) * Int64(f9)
    let f1f1_2 = Int64(f1_2) * Int64(f1)
    let f1f2_2 = Int64(f1_2) * Int64(f2)
    let f1f3_4 = Int64(f1_2) * Int64(f3_2)
    let f1f4_2 = Int64(f1_2) * Int64(f4)
    let f1f5_4 = Int64(f1_2) * Int64(f5_2)
    let f1f6_2 = Int64(f1_2) * Int64(f6)
    let f1f7_4 = Int64(f1_2) * Int64(f7_2)
    let f1f8_2 = Int64(f1_2) * Int64(f8)
    let f1f9_76 = Int64(f1_2) * Int64(f9_38)
    let f2f2 = Int64(f2) * Int64(f2)
    let f2f3_2 = Int64(f2_2) * Int64(f3)
    let f2f4_2 = Int64(f2_2) * Int64(f4)
    let f2f5_2 = Int64(f2_2) * Int64(f5)
    let f2f6_2 = Int64(f2_2) * Int64(f6)
    let f2f7_2 = Int64(f2_2) * Int64(f7)
    let f2f8_38 = Int64(f2_2) * Int64(f8_19)
    let f2f9_38 = Int64(f2) * Int64(f9_38)
    let f3f3_2 = Int64(f3_2) * Int64(f3)
    let f3f4_2 = Int64(f3_2) * Int64(f4)
    let f3f5_4 = Int64(f3_2) * Int64(f5_2)
    let f3f6_2 = Int64(f3_2) * Int64(f6)
    let f3f7_76 = Int64(f3_2) * Int64(f7_38)
    let f3f8_38 = Int64(f3_2) * Int64(f8_19)
    let f3f9_76 = Int64(f3_2) * Int64(f9_38)
    let f4f4 = Int64(f4) * Int64(f4)
    let f4f5_2 = Int64(f4_2) * Int64(f5)
    let f4f6_38 = Int64(f4_2) * Int64(f6_19)
    let f4f7_38 = Int64(f4) * Int64(f7_38)
    let f4f8_38 = Int64(f4_2) * Int64(f8_19)
    let f4f9_38 = Int64(f4) * Int64(f9_38)
    let f5f5_38 = Int64(f5) * Int64(f5_38)
    let f5f6_38 = Int64(f5_2) * Int64(f6_19)
    let f5f7_76 = Int64(f5_2) * Int64(f7_38)
    let f5f8_38 = Int64(f5_2) * Int64(f8_19)
    let f5f9_76 = Int64(f5_2) * Int64(f9_38)
    let f6f6_19 = Int64(f6) * Int64(f6_19)
    let f6f7_38 = Int64(f6) * Int64(f7_38)
    let f6f8_38 = Int64(f6_2) * Int64(f8_19)
    let f6f9_38 = Int64(f6) * Int64(f9_38)
    let f7f7_38 = Int64(f7) * Int64(f7_38)
    let f7f8_38 = Int64(f7_2) * Int64(f8_19)
    let f7f9_76 = Int64(f7_2) * Int64(f9_38)
    let f8f8_19 = Int64(f8) * Int64(f8_19)
    let f8f9_38 = Int64(f8) * Int64(f9_38)
    let f9f9_38 = Int64(f9) * Int64(f9_38)
    var h0 = f0f0 + f1f9_76 + f2f8_38 + f3f7_76 + f4f6_38 + f5f5_38
    var h1 = f0f1_2 + f2f9_38 + f3f8_38 + f4f7_38 + f5f6_38
    var h2 = f0f2_2 + f1f1_2 + f3f9_76 + f4f8_38 + f5f7_76 + f6f6_19
    var h3 = f0f3_2 + f1f2_2 + f4f9_38 + f5f8_38 + f6f7_38
    var h4 = f0f4_2 + f1f3_4 + f2f2 + f5f9_76 + f6f8_38 + f7f7_38
    var h5 = f0f5_2 + f1f4_2 + f2f3_2 + f6f9_38 + f7f8_38
    var h6 = f0f6_2 + f1f5_4 + f2f4_2 + f3f3_2 + f7f9_76 + f8f8_19
    var h7 = f0f7_2 + f1f6_2 + f2f5_2 + f3f4_2 + f8f9_38
    var h8 = f0f8_2 + f1f7_4 + f2f6_2 + f3f5_4 + f4f4 + f9f9_38
    var h9 = f0f9_2 + f1f8_2 + f2f7_2 + f3f6_2 + f4f5_2
    var carry = [Int64](repeating: 0, count: 10)
    
    h0 += h0
    h1 += h1
    h2 += h2
    h3 += h3
    h4 += h4
    h5 += h5
    h6 += h6
    h7 += h7
    h8 += h8
    h9 += h9
    
    carry[0] = (h0 + (1 << 25)) >> 26
    h1 += carry[0]
    h0 -= carry[0] << 26
    carry[4] = (h4 + (1 << 25)) >> 26
    h5 += carry[4]
    h4 -= carry[4] << 26
    
    carry[1] = (h1 + (1 << 24)) >> 25
    h2 += carry[1]
    h1 -= carry[1] << 25
    carry[5] = (h5 + (1 << 24)) >> 25
    h6 += carry[5]
    h5 -= carry[5] << 25
    
    carry[2] = (h2 + (1 << 25)) >> 26
    h3 += carry[2]
    h2 -= carry[2] << 26
    carry[6] = (h6 + (1 << 25)) >> 26
    h7 += carry[6]
    h6 -= carry[6] << 26
    
    carry[3] = (h3 + (1 << 24)) >> 25
    h4 += carry[3]
    h3 -= carry[3] << 25
    carry[7] = (h7 + (1 << 24)) >> 25
    h8 += carry[7]
    h7 -= carry[7] << 25
    
    carry[4] = (h4 + (1 << 25)) >> 26
    h5 += carry[4]
    h4 -= carry[4] << 26
    carry[8] = (h8 + (1 << 25)) >> 26
    h9 += carry[8]
    h8 -= carry[8] << 26
    
    carry[9] = (h9 + (1 << 24)) >> 25
    h0 += carry[9] * 19
    h9 -= carry[9] << 25
    
    carry[0] = (h0 + (1 << 25)) >> 26
    h1 += carry[0]
    h0 -= carry[0] << 26
    
    h[0] = Int32(h0)
    h[1] = Int32(h1)
    h[2] = Int32(h2)
    h[3] = Int32(h3)
    h[4] = Int32(h4)
    h[5] = Int32(h5)
    h[6] = Int32(h6)
    h[7] = Int32(h7)
    h[8] = Int32(h8)
    h[9] = Int32(h9)
}

func FeInvert(_ out: inout FieldElement, _ z:FieldElement) {
    var t0 = FieldElement(repeating: 0, count: 10)
    var t1 = FieldElement(repeating: 0, count: 10)
    var t2 = FieldElement(repeating: 0, count: 10)
    var t3 = FieldElement(repeating: 0, count: 10)
    
    FeSquare(&t0, z)        // 2^1
    FeSquare(&t1, t0)      // 2^2
    for _ in 1..<2{ // 2^3
        FeSquare(&t1, t1)
    }
    FeMul(&t1, z, t1)      // 2^3 + 2^0
    FeMul(&t0, t0, t1)    // 2^3 + 2^1 + 2^0
    FeSquare(&t2, t0)      // 2^4 + 2^2 + 2^1
    FeMul(&t1, t1, t2)    // 2^4 + 2^3 + 2^2 + 2^1 + 2^0
    FeSquare(&t2, t1)      // 5,4,3,2,1
    for _ in 1..<5 { // 9,8,7,6,5
        FeSquare(&t2, t2)
    }
    FeMul(&t1, t2, t1)     // 9,8,7,6,5,4,3,2,1,0
    FeSquare(&t2, t1)       // 10..1
    for _ in 1..<10 { // 19..10
        FeSquare(&t2, t2)
    }
    FeMul(&t2, t2, t1)     // 19..0
    FeSquare(&t3, t2)       // 20..1
    for _ in 1..<20 { // 39..20
        FeSquare(&t3, t3)
    }
    FeMul(&t2, t3, t2)     // 39..0
    FeSquare(&t2, t2)       // 40..1
    for _ in 1..<10 { // 49..10
        FeSquare(&t2, t2)
    }
    FeMul(&t1, t2, t1)     // 49..0
    FeSquare(&t2, t1)       // 50..1
    for _ in 1..<50 { // 99..50
        FeSquare(&t2, t2)
    }
    FeMul(&t2, t2, t1)      // 99..0
    FeSquare(&t3, t2)        // 100..1
    for _ in 1..<100 { // 199..100
        FeSquare(&t3, t3)
    }
    FeMul(&t2, t3, t2)     // 199..0
    FeSquare(&t2, t2)       // 200..1
    for _ in 1..<50 { // 249..50
        FeSquare(&t2, t2)
    }
    FeMul(&t1, t2, t1)    // 249..0
    FeSquare(&t1, t1)      // 250..1
    for _ in 1..<5 { // 254..5
        FeSquare(&t1, t1)
    }
    FeMul(&out, t1, t0) // 254..5,3,1,0
}

func fePow22523(_ out: inout FieldElement, _ z: FieldElement) {
    var t0 = FieldElement(repeating: 0, count: 10)
    var t1 = FieldElement(repeating: 0, count: 10)
    var t2 = FieldElement(repeating: 0, count: 10)
    
    FeSquare(&t0, z)
    /* TODO: This is in the original code too, never executed. not sure if this is correct.
     for _ in 1..< 1 {
     FeSquare(&t0, t0)
     }
     */
    FeSquare(&t1, t0)
    for _ in 1..<2 {
        FeSquare(&t1, t1)
    }
    FeMul(&t1, z, t1)
    FeMul(&t0, t0, t1)
    FeSquare(&t0, t0)
    /* TODO: This is in the original code too, never executed. not sure if this is correct.
     for _ in 1..< 1 {
     FeSquare(&t0, t0)
     }
     */
    FeMul(&t0, t1, t0)
    FeSquare(&t1, t0)
    for _ in 1..<5 {
        FeSquare(&t1, t1)
    }
    FeMul(&t0, t1, t0)
    FeSquare(&t1, t0)
    for _ in 1..<10 {
        FeSquare(&t1, t1)
    }
    FeMul(&t1, t1, t0)
    FeSquare(&t2, t1)
    for _ in 1..<20 {
        FeSquare(&t2, t2)
    }
    FeMul(&t1, t2, t1)
    FeSquare(&t1, t1)
    for _ in 1..<10 {
        FeSquare(&t1, t1)
    }
    FeMul(&t0, t1, t0)
    FeSquare(&t1, t0)
    for _ in 1..<50 {
        FeSquare(&t1, t1)
    }
    FeMul(&t1, t1, t0)
    FeSquare(&t2, t1)
    for _ in 1..<100 {
        FeSquare(&t2, t2)
    }
    FeMul(&t1, t2, t1)
    FeSquare(&t1, t1)
    for _ in 1..<50 {
        FeSquare(&t1, t1)
    }
    FeMul(&t0, t1, t0)
    FeSquare(&t0, t0)
    for _ in 1..<2  {
        FeSquare(&t0, t0)
    }
    FeMul(&out, t0, z)
}
