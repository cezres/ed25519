//
//  edwards25519.swift
//  ErisKeys
//
//  Created by Alex Tran Qui on 06/06/16.
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
// Implements operations in GF(2**255-19) and on an
// Edwards curve that is isomorphic to curve25519. See
// http://ed25519.cr.yp.to/.

// This code is a port of the public domain, "ref10" implementation of ed25519
// from SUPERCOP.

// FieldElement represents an element of the field GF(2^255 - 19).  An element
// t, entries t[0]...t[9], represents the integer t[0]+2^26 t[1]+2^51 t[2]+2^77
// t[3]+2^102 t[4]+...+2^230 t[9].  Bounds on each t[i] vary depending on
// context.

import Foundation

func geAdd(_ r: inout CompletedGroupElement, _ p: ExtendedGroupElement, _ q: CachedGroupElement) {
    var t0 = FieldElement(repeating: 0,  count: 10)
    
    FeAdd(&r.X, p.Y, p.X)
    FeSub(&r.Y, p.Y, p.X)
    FeMul(&r.Z, r.X, q.yPlusX)
    FeMul(&r.Y, r.Y, q.yMinusX)
    FeMul(&r.T, q.T2d, p.T)
    FeMul(&r.X, p.Z, q.Z)
    FeAdd(&t0, r.X, r.X)
    FeSub(&r.X, r.Z, r.Y)
    FeAdd(&r.Y, r.Z, r.Y)
    FeAdd(&r.Z, t0, r.T)
    FeSub(&r.T, t0, r.T)
}

func geSub(_ r: inout CompletedGroupElement, _ p: ExtendedGroupElement, _ q: CachedGroupElement) {
    var t0 = FieldElement(repeating: 0,  count: 10)
    
    FeAdd(&r.X, p.Y, p.X)
    FeSub(&r.Y, p.Y, p.X)
    FeMul(&r.Z, r.X, q.yMinusX)
    FeMul(&r.Y, r.Y, q.yPlusX)
    FeMul(&r.T, q.T2d, p.T)
    FeMul(&r.X, p.Z, q.Z)
    FeAdd(&t0, r.X, r.X)
    FeSub(&r.X, r.Z, r.Y)
    FeAdd(&r.Y, r.Z, r.Y)
    FeSub(&r.Z, t0, r.T)
    FeAdd(&r.T, t0, r.T)
}

func geMixedAdd(_ r: inout CompletedGroupElement, _ p: ExtendedGroupElement, _ q: PreComputedGroupElement) {
    var t0 = FieldElement(repeating: 0,  count: 10)
    
    FeAdd(&r.X, p.Y, p.X)
    FeSub(&r.Y, p.Y, p.X)
    FeMul(&r.Z, r.X, q.yPlusX)
    FeMul(&r.Y, r.Y, q.yMinusX)
    FeMul(&r.T, q.xy2d, p.T)
    FeAdd(&t0, p.Z, p.Z)
    FeSub(&r.X, r.Z, r.Y)
    FeAdd(&r.Y, r.Z, r.Y)
    FeAdd(&r.Z, t0, r.T)
    FeSub(&r.T, t0, r.T)
}

func geMixedSub(_ r: inout CompletedGroupElement, _ p: ExtendedGroupElement, _ q: PreComputedGroupElement) {
    var t0 = FieldElement(repeating: 0,  count: 10)
    
    FeAdd(&r.X, p.Y, p.X)
    FeSub(&r.Y, p.Y, p.X)
    FeMul(&r.Z, r.X, q.yMinusX)
    FeMul(&r.Y, r.Y, q.yPlusX)
    FeMul(&r.T, q.xy2d, p.T)
    FeAdd(&t0, p.Z, p.Z)
    FeSub(&r.X, r.Z, r.Y)
    FeAdd(&r.Y, r.Z, r.Y)
    FeSub(&r.Z, t0, r.T)
    FeAdd(&r.T, t0, r.T)
}

func slide(_ r: inout [Int8], _ a: [byte]) { // r.count == 256, a.count == 32
    for i in 0..<256 {
        r[i] = Int8(1 & (a[i>>3] >> byte(i&7)))
    }
    
    for i in 0..<256 {
        if r[i] != 0 {
            var b = 1
            while (b <= 6 && i+b < 256) {
                if r[i+b] != 0 {
                    if r[i]+(r[i+b]<<Int8(b)) <= 15 {
                        r[i] += r[i+b] << Int8(b)
                        r[i+b] = 0
                    } else if r[i]-(r[i+b]<<Int8(b)) >= -15 {
                        r[i] -= r[i+b] << Int8(b)
                        for k in i+b..<256 {
                            if r[k] == 0 {
                                r[k] = 1
                                break
                            }
                            r[k] = 0
                        }
                    } else {
                        break
                    }
                }
                b += 1
            }
        }
    }
}

// GeDoubleScalarMultVartime sets r = a*A + b*B
// where a = a[0]+256*a[1]+...+256^31 a[31].
// and b = b[0]+256*b[1]+...+256^31 b[31].
// B is the Ed25519 base point (x,4/5) with x positive.
func GeDoubleScalarMultVartime(_ r: inout ProjectiveGroupElement, _ a: [byte], _ A: ExtendedGroupElement, _ b: [byte]) { // a.count == b.count == 32
    var aSlide = [Int8](repeating: 0, count: 256)
    var bSlide = [Int8](repeating: 0, count: 256)
    var Ai = [CachedGroupElement](repeating: CachedGroupElement(), count: 8) // A,3A,5A,7A,9A,11A,13A,15A Ai.count == 8
    var t = CompletedGroupElement()
    var u =  ExtendedGroupElement()
    var A2 = ExtendedGroupElement()
    
    slide(&aSlide, a)
    slide(&bSlide, b)
    
    A.ToCached(&Ai[0])
    A.Double(&t)
    t.ToExtended(&A2)
    
    for i in 0..<7 {
        geAdd(&t, A2, Ai[i])
        t.ToExtended(&u)
        u.ToCached(&Ai[i+1])
    }
    
    r.Zero()
    
    var counter = 255
    while(counter >= 0) {
        if aSlide[counter] != 0 || bSlide[counter] != 0 {
            break
        }
        counter -= 1
    }
    
    while (counter >= 0) {
        r.Double(&t)
        
        if aSlide[counter] > 0 {
            t.ToExtended(&u)
            geAdd(&t, u, Ai[Int(aSlide[counter])/2])
        } else if aSlide[counter] < 0 {
            t.ToExtended(&u)
            geSub(&t, u, Ai[Int(-aSlide[counter])/2])
        }
        
        if bSlide[counter] > 0 {
            t.ToExtended(&u)
            geMixedAdd(&t, u, bi[Int(bSlide[counter])/2])
        } else if bSlide[counter] < 0 {
            t.ToExtended(&u)
            geMixedSub(&t, u, bi[Int(-bSlide[counter])/2])
        }
        
        t.ToProjective(&r)
        counter -= 1
    }
}

// equal returns 1 if b == c and 0 otherwise.
func equal(_ b: Int32, _ c: Int32) -> Int32 {
    if (b==c) {
        return 1 }
    return 0
    /* / original code, which breaks due to UInt8 and x-=1
     var x = UInt32(b ^ c)
     x-=1
     return Int32(x >> 31)*/
}

// negative returns 1 if b < 0 and 0 otherwise.
func negative(_ b: Int32) -> Int32 {
    if (b<0) {
        return 1 }
    return 0
    
    /* // original code
     return (b >> 31) & 1
     */
}

func PreComputedGroupElementCMove(_ t: inout PreComputedGroupElement, _ u: PreComputedGroupElement, _ b: Int32) {
    FeCMove(&t.yPlusX, u.yPlusX, b)
    FeCMove(&t.yMinusX, u.yMinusX, b)
    FeCMove(&t.xy2d, u.xy2d, b)
}

func selectPoint(_ t: inout PreComputedGroupElement, _ pos: Int32, _ b: Int32) {
    var minusT = PreComputedGroupElement()
    let bNegative = negative(b)
    let bAbs = b - (((-bNegative) & b) << 1)
    
    t.Zero()
    for i in 0..<8 {
        PreComputedGroupElementCMove(&t, base[Int(pos)][i], equal(bAbs, Int32(i+1)))
    }
    FeCopy(&minusT.yPlusX, t.yMinusX)
    FeCopy(&minusT.yMinusX, t.yPlusX)
    FeNeg(&minusT.xy2d, t.xy2d)
    PreComputedGroupElementCMove(&t, minusT, bNegative)
}

// GeScalarMultBase computes h = a*B, where
//   a = a[0]+256*a[1]+...+256^31 a[31]
//   B is the Ed25519 base point (x,4/5) with x positive.
//
// Preconditions:
//   a[31] <= 127
func GeScalarMultBase(_ h: inout ExtendedGroupElement, _ a: [byte]) {
    var e = [Int8](repeating: 0, count: 64)
    
    for i in 0..<a.count {
        e[2*i] = Int8(a[i] & 15)
        e[2*i+1] = Int8((a[i] >> 4) & 15)
    }
    
    // each e[i] is between 0 and 15 and e[63] is between 0 and 7.
    
    var carry = Int8(0)
    for i in 0..<63 {
        e[i] += carry
        carry = (e[i] + 8) >> 4
        e[i] -= carry << 4
    }
    e[63] += carry
    // each e[i] is between -8 and 8.
    
    h.Zero()
    var t = PreComputedGroupElement()
    var r = CompletedGroupElement()
    for i in 0..<32 {
        selectPoint(&t, Int32(i), Int32(e[2 * i+1]))
        geMixedAdd(&r, h, t)
        r.ToExtended(&h)
    }
    
    var s = ProjectiveGroupElement()
    
    h.Double(&r)
    r.ToProjective(&s)
    s.Double(&r)
    r.ToProjective(&s)
    s.Double(&r)
    r.ToProjective(&s)
    s.Double(&r)
    r.ToExtended(&h)
    
    for i in 0..<32 {
        selectPoint(&t, Int32(i), Int32(e[2 * i]))
        geMixedAdd(&r, h, t)
        r.ToExtended(&h)
    }
}

// The scalars are GF(2^252 + 27742317777372353535851937790883648493).

// Input:
//   a[0]+256*a[1]+...+256^31*a[31] = a
//   b[0]+256*b[1]+...+256^31*b[31] = b
//   c[0]+256*c[1]+...+256^31*c[31] = c
//
// Output:
//   s[0]+256*s[1]+...+256^31*s[31] = (ab+c) mod l
//   where l = 2^252 + 27742317777372353535851937790883648493.
func ScMulAdd(_ s: inout [byte],_ a: [byte],_ b: [byte], _ c: [byte]) {
    let lasta = a.count - 1
    let a0 = 2097151 & load3(a)
    let a1 = 2097151 & (load4(a[2...lasta]) >> 5)
    let a2 = 2097151 & (load3(a[5...lasta]) >> 2)
    let a3 = 2097151 & (load4(a[7...lasta]) >> 7)
    let a4 = 2097151 & (load4(a[10...lasta]) >> 4)
    let a5 = 2097151 & (load3(a[13...lasta]) >> 1)
    let a6 = 2097151 & (load4(a[15...lasta]) >> 6)
    let a7 = 2097151 & (load3(a[18...lasta]) >> 3)
    let a8 = 2097151 & load3(a[21...lasta])
    let a9 = 2097151 & (load4(a[23...lasta]) >> 5)
    let a10 = 2097151 & (load3(a[26...lasta]) >> 2)
    let a11 = (load4(a[28...lasta]) >> 7)
    let lastb = b.count - 1
    let b0 = 2097151 & load3(b)
    let b1 = 2097151 & (load4(b[2...lastb]) >> 5)
    let b2 = 2097151 & (load3(b[5...lastb]) >> 2)
    let b3 = 2097151 & (load4(b[7...lastb]) >> 7)
    let b4 = 2097151 & (load4(b[10...lastb]) >> 4)
    let b5 = 2097151 & (load3(b[13...lastb]) >> 1)
    let b6 = 2097151 & (load4(b[15...lastb]) >> 6)
    let b7 = 2097151 & (load3(b[18...lastb]) >> 3)
    let b8 = 2097151 & load3(b[21...lastb])
    let b9 = 2097151 & (load4(b[23...lastb]) >> 5)
    let b10 = 2097151 & (load3(b[26...lastb]) >> 2)
    let b11 = (load4(b[28...lastb]) >> 7)
    let lastc = c.count - 1
    let c0 = 2097151 & load3(c)
    let c1 = 2097151 & (load4(c[2...lastc]) >> 5)
    let c2 = 2097151 & (load3(c[5...lastc]) >> 2)
    let c3 = 2097151 & (load4(c[7...lastc]) >> 7)
    let c4 = 2097151 & (load4(c[10...lastc]) >> 4)
    let c5 = 2097151 & (load3(c[13...lastc]) >> 1)
    let c6 = 2097151 & (load4(c[15...lastc]) >> 6)
    let c7 = 2097151 & (load3(c[18...lastc]) >> 3)
    let c8 = 2097151 & load3(c[21...lastc])
    let c9 = 2097151 & (load4(c[23...lastc]) >> 5)
    let c10 = 2097151 & (load3(c[26...lastc]) >> 2)
    let c11 = (load4(c[28...lastc]) >> 7)
    var carry = [Int64](repeating: 0, count: 23)
    
    var s0 = c0 + a0*b0
    var s1 = c1 + a0*b1 + a1*b0
    var s2 = c2 + a0*b2 + a1*b1 + a2*b0
    var s3 = c3 + a0*b3 + a1*b2 + a2*b1 + a3*b0
    var s4 = c4 + a0*b4 + a1*b3 + a2*b2 + a3*b1 + a4*b0
    var s5 = c5 + a0*b5 + a1*b4 + a2*b3 + a3*b2 + a4*b1 + a5*b0
    var s6 = c6 + a0*b6 + a1*b5 + a2*b4 + a3*b3 + a4*b2 + a5*b1 + a6*b0
    var s7 = c7 + a0*b7 + a1*b6 + a2*b5 + a3*b4 + a4*b3 + a5*b2 + a6*b1 + a7*b0
    var s8 = c8 + a0*b8 + a1*b7 + a2*b6 + a3*b5 + a4*b4 + a5*b3 + a6*b2 + a7*b1 + a8*b0
    var s9 = c9 + a0*b9 + a1*b8 + a2*b7 + a3*b6 + a4*b5 + a5*b4 + a6*b3 + a7*b2 + a8*b1 + a9*b0
    var s10 = c10 + a0*b10 + a1*b9 + a2*b8 + a3*b7 + a4*b6 + a5*b5 + a6*b4 + a7*b3 + a8*b2 + a9*b1 + a10*b0
    var s11 = c11 + a0*b11 + a1*b10 + a2*b9 + a3*b8 + a4*b7 + a5*b6 + a6*b5 + a7*b4 + a8*b3 + a9*b2 + a10*b1 + a11*b0
    var s12 = a1*b11 + a2*b10 + a3*b9 + a4*b8 + a5*b7 + a6*b6 + a7*b5 + a8*b4 + a9*b3 + a10*b2 + a11*b1
    var s13 = a2*b11 + a3*b10 + a4*b9 + a5*b8 + a6*b7 + a7*b6 + a8*b5 + a9*b4 + a10*b3 + a11*b2
    var s14 = a3*b11 + a4*b10 + a5*b9 + a6*b8 + a7*b7 + a8*b6 + a9*b5 + a10*b4 + a11*b3
    var s15 = a4*b11 + a5*b10 + a6*b9 + a7*b8 + a8*b7 + a9*b6 + a10*b5 + a11*b4
    var s16 = a5*b11 + a6*b10 + a7*b9 + a8*b8 + a9*b7 + a10*b6 + a11*b5
    var s17 = a6*b11 + a7*b10 + a8*b9 + a9*b8 + a10*b7 + a11*b6
    var s18 = a7*b11 + a8*b10 + a9*b9 + a10*b8 + a11*b7
    var s19 = a8*b11 + a9*b10 + a10*b9 + a11*b8
    var s20 = a9*b11 + a10*b10 + a11*b9
    var s21 = a10*b11 + a11*b10
    var s22 = a11 * b11
    var s23 = Int64(0)
    
    carry[0] = (s0 + (1 << 20)) >> 21
    s1 += carry[0]
    s0 -= carry[0] << 21
    carry[2] = (s2 + (1 << 20)) >> 21
    s3 += carry[2]
    s2 -= carry[2] << 21
    carry[4] = (s4 + (1 << 20)) >> 21
    s5 += carry[4]
    s4 -= carry[4] << 21
    carry[6] = (s6 + (1 << 20)) >> 21
    s7 += carry[6]
    s6 -= carry[6] << 21
    carry[8] = (s8 + (1 << 20)) >> 21
    s9 += carry[8]
    s8 -= carry[8] << 21
    carry[10] = (s10 + (1 << 20)) >> 21
    s11 += carry[10]
    s10 -= carry[10] << 21
    carry[12] = (s12 + (1 << 20)) >> 21
    s13 += carry[12]
    s12 -= carry[12] << 21
    carry[14] = (s14 + (1 << 20)) >> 21
    s15 += carry[14]
    s14 -= carry[14] << 21
    carry[16] = (s16 + (1 << 20)) >> 21
    s17 += carry[16]
    s16 -= carry[16] << 21
    carry[18] = (s18 + (1 << 20)) >> 21
    s19 += carry[18]
    s18 -= carry[18] << 21
    carry[20] = (s20 + (1 << 20)) >> 21
    s21 += carry[20]
    s20 -= carry[20] << 21
    carry[22] = (s22 + (1 << 20)) >> 21
    s23 += carry[22]
    s22 -= carry[22] << 21
    
    carry[1] = (s1 + (1 << 20)) >> 21
    s2 += carry[1]
    s1 -= carry[1] << 21
    carry[3] = (s3 + (1 << 20)) >> 21
    s4 += carry[3]
    s3 -= carry[3] << 21
    carry[5] = (s5 + (1 << 20)) >> 21
    s6 += carry[5]
    s5 -= carry[5] << 21
    carry[7] = (s7 + (1 << 20)) >> 21
    s8 += carry[7]
    s7 -= carry[7] << 21
    carry[9] = (s9 + (1 << 20)) >> 21
    s10 += carry[9]
    s9 -= carry[9] << 21
    carry[11] = (s11 + (1 << 20)) >> 21
    s12 += carry[11]
    s11 -= carry[11] << 21
    carry[13] = (s13 + (1 << 20)) >> 21
    s14 += carry[13]
    s13 -= carry[13] << 21
    carry[15] = (s15 + (1 << 20)) >> 21
    s16 += carry[15]
    s15 -= carry[15] << 21
    carry[17] = (s17 + (1 << 20)) >> 21
    s18 += carry[17]
    s17 -= carry[17] << 21
    carry[19] = (s19 + (1 << 20)) >> 21
    s20 += carry[19]
    s19 -= carry[19] << 21
    carry[21] = (s21 + (1 << 20)) >> 21
    s22 += carry[21]
    s21 -= carry[21] << 21
    
    s11 += s23 * 666643
    s12 += s23 * 470296
    s13 += s23 * 654183
    s14 -= s23 * 997805
    s15 += s23 * 136657
    s16 -= s23 * 683901
    s23 = 0
    
    s10 += s22 * 666643
    s11 += s22 * 470296
    s12 += s22 * 654183
    s13 -= s22 * 997805
    s14 += s22 * 136657
    s15 -= s22 * 683901
    s22 = 0
    
    s9 += s21 * 666643
    s10 += s21 * 470296
    s11 += s21 * 654183
    s12 -= s21 * 997805
    s13 += s21 * 136657
    s14 -= s21 * 683901
    s21 = 0
    
    s8 += s20 * 666643
    s9 += s20 * 470296
    s10 += s20 * 654183
    s11 -= s20 * 997805
    s12 += s20 * 136657
    s13 -= s20 * 683901
    s20 = 0
    
    s7 += s19 * 666643
    s8 += s19 * 470296
    s9 += s19 * 654183
    s10 -= s19 * 997805
    s11 += s19 * 136657
    s12 -= s19 * 683901
    s19 = 0
    
    s6 += s18 * 666643
    s7 += s18 * 470296
    s8 += s18 * 654183
    s9 -= s18 * 997805
    s10 += s18 * 136657
    s11 -= s18 * 683901
    s18 = 0
    
    carry[6] = (s6 + (1 << 20)) >> 21
    s7 += carry[6]
    s6 -= carry[6] << 21
    carry[8] = (s8 + (1 << 20)) >> 21
    s9 += carry[8]
    s8 -= carry[8] << 21
    carry[10] = (s10 + (1 << 20)) >> 21
    s11 += carry[10]
    s10 -= carry[10] << 21
    carry[12] = (s12 + (1 << 20)) >> 21
    s13 += carry[12]
    s12 -= carry[12] << 21
    carry[14] = (s14 + (1 << 20)) >> 21
    s15 += carry[14]
    s14 -= carry[14] << 21
    carry[16] = (s16 + (1 << 20)) >> 21
    s17 += carry[16]
    s16 -= carry[16] << 21
    
    carry[7] = (s7 + (1 << 20)) >> 21
    s8 += carry[7]
    s7 -= carry[7] << 21
    carry[9] = (s9 + (1 << 20)) >> 21
    s10 += carry[9]
    s9 -= carry[9] << 21
    carry[11] = (s11 + (1 << 20)) >> 21
    s12 += carry[11]
    s11 -= carry[11] << 21
    carry[13] = (s13 + (1 << 20)) >> 21
    s14 += carry[13]
    s13 -= carry[13] << 21
    carry[15] = (s15 + (1 << 20)) >> 21
    s16 += carry[15]
    s15 -= carry[15] << 21
    
    s5 += s17 * 666643
    s6 += s17 * 470296
    s7 += s17 * 654183
    s8 -= s17 * 997805
    s9 += s17 * 136657
    s10 -= s17 * 683901
    s17 = 0
    
    s4 += s16 * 666643
    s5 += s16 * 470296
    s6 += s16 * 654183
    s7 -= s16 * 997805
    s8 += s16 * 136657
    s9 -= s16 * 683901
    s16 = 0
    
    s3 += s15 * 666643
    s4 += s15 * 470296
    s5 += s15 * 654183
    s6 -= s15 * 997805
    s7 += s15 * 136657
    s8 -= s15 * 683901
    s15 = 0
    
    s2 += s14 * 666643
    s3 += s14 * 470296
    s4 += s14 * 654183
    s5 -= s14 * 997805
    s6 += s14 * 136657
    s7 -= s14 * 683901
    s14 = 0
    
    s1 += s13 * 666643
    s2 += s13 * 470296
    s3 += s13 * 654183
    s4 -= s13 * 997805
    s5 += s13 * 136657
    s6 -= s13 * 683901
    s13 = 0
    
    s0 += s12 * 666643
    s1 += s12 * 470296
    s2 += s12 * 654183
    s3 -= s12 * 997805
    s4 += s12 * 136657
    s5 -= s12 * 683901
    s12 = 0
    
    carry[0] = (s0 + (1 << 20)) >> 21
    s1 += carry[0]
    s0 -= carry[0] << 21
    carry[2] = (s2 + (1 << 20)) >> 21
    s3 += carry[2]
    s2 -= carry[2] << 21
    carry[4] = (s4 + (1 << 20)) >> 21
    s5 += carry[4]
    s4 -= carry[4] << 21
    carry[6] = (s6 + (1 << 20)) >> 21
    s7 += carry[6]
    s6 -= carry[6] << 21
    carry[8] = (s8 + (1 << 20)) >> 21
    s9 += carry[8]
    s8 -= carry[8] << 21
    carry[10] = (s10 + (1 << 20)) >> 21
    s11 += carry[10]
    s10 -= carry[10] << 21
    
    carry[1] = (s1 + (1 << 20)) >> 21
    s2 += carry[1]
    s1 -= carry[1] << 21
    carry[3] = (s3 + (1 << 20)) >> 21
    s4 += carry[3]
    s3 -= carry[3] << 21
    carry[5] = (s5 + (1 << 20)) >> 21
    s6 += carry[5]
    s5 -= carry[5] << 21
    carry[7] = (s7 + (1 << 20)) >> 21
    s8 += carry[7]
    s7 -= carry[7] << 21
    carry[9] = (s9 + (1 << 20)) >> 21
    s10 += carry[9]
    s9 -= carry[9] << 21
    carry[11] = (s11 + (1 << 20)) >> 21
    s12 += carry[11]
    s11 -= carry[11] << 21
    
    s0 += s12 * 666643
    s1 += s12 * 470296
    s2 += s12 * 654183
    s3 -= s12 * 997805
    s4 += s12 * 136657
    s5 -= s12 * 683901
    s12 = 0
    
    carry[0] = s0 >> 21
    s1 += carry[0]
    s0 -= carry[0] << 21
    carry[1] = s1 >> 21
    s2 += carry[1]
    s1 -= carry[1] << 21
    carry[2] = s2 >> 21
    s3 += carry[2]
    s2 -= carry[2] << 21
    carry[3] = s3 >> 21
    s4 += carry[3]
    s3 -= carry[3] << 21
    carry[4] = s4 >> 21
    s5 += carry[4]
    s4 -= carry[4] << 21
    carry[5] = s5 >> 21
    s6 += carry[5]
    s5 -= carry[5] << 21
    carry[6] = s6 >> 21
    s7 += carry[6]
    s6 -= carry[6] << 21
    carry[7] = s7 >> 21
    s8 += carry[7]
    s7 -= carry[7] << 21
    carry[8] = s8 >> 21
    s9 += carry[8]
    s8 -= carry[8] << 21
    carry[9] = s9 >> 21
    s10 += carry[9]
    s9 -= carry[9] << 21
    carry[10] = s10 >> 21
    s11 += carry[10]
    s10 -= carry[10] << 21
    carry[11] = s11 >> 21
    s12 += carry[11]
    s11 -= carry[11] << 21
    
    s0 += s12 * 666643
    s1 += s12 * 470296
    s2 += s12 * 654183
    s3 -= s12 * 997805
    s4 += s12 * 136657
    s5 -= s12 * 683901
    s12 = 0
    
    carry[0] = s0 >> 21
    s1 += carry[0]
    s0 -= carry[0] << 21
    carry[1] = s1 >> 21
    s2 += carry[1]
    s1 -= carry[1] << 21
    carry[2] = s2 >> 21
    s3 += carry[2]
    s2 -= carry[2] << 21
    carry[3] = s3 >> 21
    s4 += carry[3]
    s3 -= carry[3] << 21
    carry[4] = s4 >> 21
    s5 += carry[4]
    s4 -= carry[4] << 21
    carry[5] = s5 >> 21
    s6 += carry[5]
    s5 -= carry[5] << 21
    carry[6] = s6 >> 21
    s7 += carry[6]
    s6 -= carry[6] << 21
    carry[7] = s7 >> 21
    s8 += carry[7]
    s7 -= carry[7] << 21
    carry[8] = s8 >> 21
    s9 += carry[8]
    s8 -= carry[8] << 21
    carry[9] = s9 >> 21
    s10 += carry[9]
    s9 -= carry[9] << 21
    carry[10] = s10 >> 21
    s11 += carry[10]
    s10 -= carry[10] << 21
    
    s[0] = byte(s0 >> 0 % 256)
    s[1] = byte(s0 >> 8 % 256)
    s[2] = byte(((s0 >> 16) | (s1 << 5)) % 256)
    s[3] = byte(s1 >> 3 % 256)
    s[4] = byte(s1 >> 11 % 256)
    s[5] = byte(((s1 >> 19) | (s2 << 2)) % 256)
    s[6] = byte(s2 >> 6 % 256)
    s[7] = byte(((s2 >> 14) | (s3 << 7)) % 256)
    s[8] = byte(s3 >> 1 % 256)
    s[9] = byte(s3 >> 9 % 256)
    s[10] = byte(((s3 >> 17) | (s4 << 4)) % 256)
    s[11] = byte(s4 >> 4 % 256)
    s[12] = byte(s4 >> 12 % 256)
    s[13] = byte(((s4 >> 20) | (s5 << 1)) % 256)
    s[14] = byte(s5 >> 7 % 256)
    s[15] = byte(((s5 >> 15) | (s6 << 6)) % 256)
    s[16] = byte(s6 >> 2 % 256)
    s[17] = byte(s6 >> 10 % 256)
    s[18] = byte(((s6 >> 18) | (s7 << 3)) % 256)
    s[19] = byte(s7 >> 5 % 256)
    s[20] = byte(s7 >> 13 % 256)
    s[21] = byte(s8 >> 0 % 256)
    s[22] = byte(s8 >> 8 % 256)
    s[23] = byte(((s8 >> 16) | (s9 << 5)) % 256)
    s[24] = byte(s9 >> 3 % 256)
    s[25] = byte(s9 >> 11 % 256)
    s[26] = byte(((s9 >> 19) | (s10 << 2)) % 256)
    s[27] = byte(s10 >> 6 % 256)
    s[28] = byte(((s10 >> 14) | (s11 << 7)) % 256)
    s[29] = byte(s11 >> 1 % 256)
    s[30] = byte(s11 >> 9 % 256)
    s[31] = byte(s11 >> 17 % 256)
}

// Input:
//   s[0]+256*s[1]+...+256^63*s[63] = s
//
// Output:
//   s[0]+256*s[1]+...+256^31*s[31] = s mod l
//   where l = 2^252 + 27742317777372353535851937790883648493.
func ScReduce(_ out: inout [byte], _ s: [byte]) {
    let lasts = s.count - 1
    var s0 = 2097151 & load3(s)
    var s1 = 2097151 & (load4(s[2...lasts]) >> 5)
    var s2 = 2097151 & (load3(s[5...lasts]) >> 2)
    var s3 = 2097151 & (load4(s[7...lasts]) >> 7)
    var s4 = 2097151 & (load4(s[10...lasts]) >> 4)
    var s5 = 2097151 & (load3(s[13...lasts]) >> 1)
    var s6 = 2097151 & (load4(s[15...lasts]) >> 6)
    var s7 = 2097151 & (load3(s[18...lasts]) >> 3)
    var s8 = 2097151 & load3(s[21...lasts])
    var s9 = 2097151 & (load4(s[23...lasts]) >> 5)
    var s10 = 2097151 & (load3(s[26...lasts]) >> 2)
    var s11 = 2097151 & (load4(s[28...lasts]) >> 7)
    var s12 = 2097151 & (load4(s[31...lasts]) >> 4)
    var s13 = 2097151 & (load3(s[34...lasts]) >> 1)
    var s14 = 2097151 & (load4(s[36...lasts]) >> 6)
    var s15 = 2097151 & (load3(s[39...lasts]) >> 3)
    var s16 = 2097151 & load3(s[42...lasts])
    var s17 = 2097151 & (load4(s[44...lasts]) >> 5)
    var s18 = 2097151 & (load3(s[47...lasts]) >> 2)
    var s19 = 2097151 & (load4(s[49...lasts]) >> 7)
    var s20 = 2097151 & (load4(s[52...lasts]) >> 4)
    var s21 = 2097151 & (load3(s[55...lasts]) >> 1)
    var s22 = 2097151 & (load4(s[57...lasts]) >> 6)
    var s23 = (load4(s[60...lasts]) >> 3)
    
    s11 += s23 * 666643
    s12 += s23 * 470296
    s13 += s23 * 654183
    s14 -= s23 * 997805
    s15 += s23 * 136657
    s16 -= s23 * 683901
    s23 = 0
    
    s10 += s22 * 666643
    s11 += s22 * 470296
    s12 += s22 * 654183
    s13 -= s22 * 997805
    s14 += s22 * 136657
    s15 -= s22 * 683901
    s22 = 0
    
    s9 += s21 * 666643
    s10 += s21 * 470296
    s11 += s21 * 654183
    s12 -= s21 * 997805
    s13 += s21 * 136657
    s14 -= s21 * 683901
    s21 = 0
    
    s8 += s20 * 666643
    s9 += s20 * 470296
    s10 += s20 * 654183
    s11 -= s20 * 997805
    s12 += s20 * 136657
    s13 -= s20 * 683901
    s20 = 0
    
    s7 += s19 * 666643
    s8 += s19 * 470296
    s9 += s19 * 654183
    s10 -= s19 * 997805
    s11 += s19 * 136657
    s12 -= s19 * 683901
    s19 = 0
    
    s6 += s18 * 666643
    s7 += s18 * 470296
    s8 += s18 * 654183
    s9 -= s18 * 997805
    s10 += s18 * 136657
    s11 -= s18 * 683901
    s18 = 0
    
    var carry = [Int64](repeating: 0, count: 17)
    
    carry[6] = (s6 + (1 << 20)) >> 21
    s7 += carry[6]
    s6 -= carry[6] << 21
    carry[8] = (s8 + (1 << 20)) >> 21
    s9 += carry[8]
    s8 -= carry[8] << 21
    carry[10] = (s10 + (1 << 20)) >> 21
    s11 += carry[10]
    s10 -= carry[10] << 21
    carry[12] = (s12 + (1 << 20)) >> 21
    s13 += carry[12]
    s12 -= carry[12] << 21
    carry[14] = (s14 + (1 << 20)) >> 21
    s15 += carry[14]
    s14 -= carry[14] << 21
    carry[16] = (s16 + (1 << 20)) >> 21
    s17 += carry[16]
    s16 -= carry[16] << 21
    
    carry[7] = (s7 + (1 << 20)) >> 21
    s8 += carry[7]
    s7 -= carry[7] << 21
    carry[9] = (s9 + (1 << 20)) >> 21
    s10 += carry[9]
    s9 -= carry[9] << 21
    carry[11] = (s11 + (1 << 20)) >> 21
    s12 += carry[11]
    s11 -= carry[11] << 21
    carry[13] = (s13 + (1 << 20)) >> 21
    s14 += carry[13]
    s13 -= carry[13] << 21
    carry[15] = (s15 + (1 << 20)) >> 21
    s16 += carry[15]
    s15 -= carry[15] << 21
    
    s5 += s17 * 666643
    s6 += s17 * 470296
    s7 += s17 * 654183
    s8 -= s17 * 997805
    s9 += s17 * 136657
    s10 -= s17 * 683901
    s17 = 0
    
    s4 += s16 * 666643
    s5 += s16 * 470296
    s6 += s16 * 654183
    s7 -= s16 * 997805
    s8 += s16 * 136657
    s9 -= s16 * 683901
    s16 = 0
    
    s3 += s15 * 666643
    s4 += s15 * 470296
    s5 += s15 * 654183
    s6 -= s15 * 997805
    s7 += s15 * 136657
    s8 -= s15 * 683901
    s15 = 0
    
    s2 += s14 * 666643
    s3 += s14 * 470296
    s4 += s14 * 654183
    s5 -= s14 * 997805
    s6 += s14 * 136657
    s7 -= s14 * 683901
    s14 = 0
    
    s1 += s13 * 666643
    s2 += s13 * 470296
    s3 += s13 * 654183
    s4 -= s13 * 997805
    s5 += s13 * 136657
    s6 -= s13 * 683901
    s13 = 0
    
    s0 += s12 * 666643
    s1 += s12 * 470296
    s2 += s12 * 654183
    s3 -= s12 * 997805
    s4 += s12 * 136657
    s5 -= s12 * 683901
    s12 = 0
    
    carry[0] = (s0 + (1 << 20)) >> 21
    s1 += carry[0]
    s0 -= carry[0] << 21
    carry[2] = (s2 + (1 << 20)) >> 21
    s3 += carry[2]
    s2 -= carry[2] << 21
    carry[4] = (s4 + (1 << 20)) >> 21
    s5 += carry[4]
    s4 -= carry[4] << 21
    carry[6] = (s6 + (1 << 20)) >> 21
    s7 += carry[6]
    s6 -= carry[6] << 21
    carry[8] = (s8 + (1 << 20)) >> 21
    s9 += carry[8]
    s8 -= carry[8] << 21
    carry[10] = (s10 + (1 << 20)) >> 21
    s11 += carry[10]
    s10 -= carry[10] << 21
    
    carry[1] = (s1 + (1 << 20)) >> 21
    s2 += carry[1]
    s1 -= carry[1] << 21
    carry[3] = (s3 + (1 << 20)) >> 21
    s4 += carry[3]
    s3 -= carry[3] << 21
    carry[5] = (s5 + (1 << 20)) >> 21
    s6 += carry[5]
    s5 -= carry[5] << 21
    carry[7] = (s7 + (1 << 20)) >> 21
    s8 += carry[7]
    s7 -= carry[7] << 21
    carry[9] = (s9 + (1 << 20)) >> 21
    s10 += carry[9]
    s9 -= carry[9] << 21
    carry[11] = (s11 + (1 << 20)) >> 21
    s12 += carry[11]
    s11 -= carry[11] << 21
    
    s0 += s12 * 666643
    s1 += s12 * 470296
    s2 += s12 * 654183
    s3 -= s12 * 997805
    s4 += s12 * 136657
    s5 -= s12 * 683901
    s12 = 0
    
    carry[0] = s0 >> 21
    s1 += carry[0]
    s0 -= carry[0] << 21
    carry[1] = s1 >> 21
    s2 += carry[1]
    s1 -= carry[1] << 21
    carry[2] = s2 >> 21
    s3 += carry[2]
    s2 -= carry[2] << 21
    carry[3] = s3 >> 21
    s4 += carry[3]
    s3 -= carry[3] << 21
    carry[4] = s4 >> 21
    s5 += carry[4]
    s4 -= carry[4] << 21
    carry[5] = s5 >> 21
    s6 += carry[5]
    s5 -= carry[5] << 21
    carry[6] = s6 >> 21
    s7 += carry[6]
    s6 -= carry[6] << 21
    carry[7] = s7 >> 21
    s8 += carry[7]
    s7 -= carry[7] << 21
    carry[8] = s8 >> 21
    s9 += carry[8]
    s8 -= carry[8] << 21
    carry[9] = s9 >> 21
    s10 += carry[9]
    s9 -= carry[9] << 21
    carry[10] = s10 >> 21
    s11 += carry[10]
    s10 -= carry[10] << 21
    carry[11] = s11 >> 21
    s12 += carry[11]
    s11 -= carry[11] << 21
    
    s0 += s12 * 666643
    s1 += s12 * 470296
    s2 += s12 * 654183
    s3 -= s12 * 997805
    s4 += s12 * 136657
    s5 -= s12 * 683901
    s12 = 0
    
    carry[0] = s0 >> 21
    s1 += carry[0]
    s0 -= carry[0] << 21
    carry[1] = s1 >> 21
    s2 += carry[1]
    s1 -= carry[1] << 21
    carry[2] = s2 >> 21
    s3 += carry[2]
    s2 -= carry[2] << 21
    carry[3] = s3 >> 21
    s4 += carry[3]
    s3 -= carry[3] << 21
    carry[4] = s4 >> 21
    s5 += carry[4]
    s4 -= carry[4] << 21
    carry[5] = s5 >> 21
    s6 += carry[5]
    s5 -= carry[5] << 21
    carry[6] = s6 >> 21
    s7 += carry[6]
    s6 -= carry[6] << 21
    carry[7] = s7 >> 21
    s8 += carry[7]
    s7 -= carry[7] << 21
    carry[8] = s8 >> 21
    s9 += carry[8]
    s8 -= carry[8] << 21
    carry[9] = s9 >> 21
    s10 += carry[9]
    s9 -= carry[9] << 21
    carry[10] = s10 >> 21
    s11 += carry[10]
    s10 -= carry[10] << 21
    
    out[0] = byte(s0 >> 0 % 256)
    out[1] = byte(s0 >> 8 % 256)
    out[2] = byte(((s0 >> 16) | (s1 << 5)) % 256)
    out[3] = byte(s1 >> 3 % 256)
    out[4] = byte(s1 >> 11 % 256)
    out[5] = byte(((s1 >> 19) | (s2 << 2)) % 256)
    out[6] = byte(s2 >> 6 % 256)
    out[7] = byte(((s2 >> 14) | (s3 << 7)) % 256)
    out[8] = byte(s3 >> 1 % 256)
    out[9] = byte(s3 >> 9 % 256)
    out[10] = byte(((s3 >> 17) | (s4 << 4)) % 256)
    out[11] = byte(s4 >> 4 % 256)
    out[12] = byte(s4 >> 12 % 256)
    out[13] = byte(((s4 >> 20) | (s5 << 1)) % 256)
    out[14] = byte(s5 >> 7 % 256)
    out[15] = byte(((s5 >> 15) | (s6 << 6)) % 256)
    out[16] = byte(s6 >> 2 % 256)
    out[17] = byte(s6 >> 10 % 256)
    out[18] = byte(((s6 >> 18) | (s7 << 3)) % 256)
    out[19] = byte(s7 >> 5 % 256)
    out[20] = byte(s7 >> 13 % 256)
    out[21] = byte(s8 >> 0 % 256)
    out[22] = byte(s8 >> 8 % 256)
    out[23] = byte(((s8 >> 16) | (s9 << 5)) % 256)
    out[24] = byte(s9 >> 3 % 256)
    out[25] = byte(s9 >> 11 % 256)
    out[26] = byte(((s9 >> 19) | (s10 << 2)) % 256)
    out[27] = byte(s10 >> 6 % 256)
    out[28] = byte(((s10 >> 14) | (s11 << 7)) % 256)
    out[29] = byte(s11 >> 1 % 256)
    out[30] = byte(s11 >> 9 % 256)
    out[31] = byte(s11 >> 17 % 256)
}
