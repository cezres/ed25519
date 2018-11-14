//
//  ed25519.swift
//  ErisKeys
//
//  Created by Alex Tran Qui on 08/06/16.
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

//  Implements the Ed25519 signature algorithm. See
// http://ed25519.cr.yp.to/.

// This code is a port of the public domain, "ref10" implementation of ed25519
// from SUPERCOP.

import Foundation
//import CryptoSwift


let PublicKeySize  = 32
let PrivateKeySize = 64
let SignatureSize  = 64

//public typealias byte = UInt8


//// GenerateKey generates a public/private key pair using a random array of 32 bytes
//public func GenerateKey(_ rand32UInt8: [byte]) -> (publicKey: [byte], privateKey: [byte]) {
//    let publicKey = MakePublicKey(rand32UInt8)
//    return (publicKey,rand32UInt8+publicKey)
//}
//
//// MakePublicKey makes a publicKey from the first half of privateKey.
//public func MakePublicKey(_ privateKeySeed: [byte]) -> [byte] {
//    var publicKey  = [byte](repeating: 0, count: PublicKeySize)
//
//    var digest = privateKeySeed.sha512()
//
//    digest[0] &= 248
//    digest[31] &= 127
//    digest[31] |= 64
//
//    var A = ExtendedGroupElement()
//
//    GeScalarMultBase(&A, Array(digest[0..<32]))
//    A.ToBytes(&publicKey)
//
//    return publicKey
//}
//
//// Sign signs the message with privateKey and returns a signature.
//public func Sign(_ privateKey: [byte], _ message: [byte]) -> [byte] {
//    let privateKeySeed = Array(privateKey[0..<32])
//
//    var digest1 = privateKeySeed.sha512()
//
//    var expandedSecretKey  = [byte](repeating: 0, count: 32)
//
//    expandedSecretKey = Array(digest1[0..<32])
//    expandedSecretKey[0] &= 248
//    expandedSecretKey[31] &= 63
//    expandedSecretKey[31] |= 64
//
//
//    var data = Array(digest1[32..<64]) + message
//
//    let messageDigest = data.sha512()
//
//    var messageDigestReduced  = [byte](repeating: 0, count: 32)
//    ScReduce(&messageDigestReduced, messageDigest)
//    var R = ExtendedGroupElement()
//    GeScalarMultBase(&R, messageDigestReduced)
//
//    var encodedR  = [byte](repeating: 0, count: 32)
//    R.ToBytes(&encodedR)
//
//    data = encodedR + Array(privateKey[32..<64]) + message
//
//    let hramDigest = data.sha512()
//
//    var hramDigestReduced  = [byte](repeating: 0, count: 32)
//    ScReduce(&hramDigestReduced, hramDigest)
//
//    var s  = [byte](repeating: 0, count: 32)
//    ScMulAdd(&s, hramDigestReduced, expandedSecretKey, messageDigestReduced)
//
//    let signature  = encodedR + s // should be 64 bytes
//
//    return signature
//}
//
//
//
//// Verify returns true iff sig is a valid signature of message by publicKey.
//public func Verify(_ publicKey: [byte], _ message: [byte], _ sig: [byte]) -> Bool {
//    if sig[63]&224 != 0 {
//        return false
//    }
//
//    var A = ExtendedGroupElement()
//    if !A.FromBytes(publicKey) {
//        return false
//    }
//
//    let data = Array(sig[0..<32]) + publicKey + message
//
//    let digest = data.sha512()
//
//    var hReduced = [byte](repeating: 0, count: 32)
//    ScReduce(&hReduced, digest)
//
//    var R = ProjectiveGroupElement()
//    let b = Array(sig[32..<64])
//    GeDoubleScalarMultVartime(&R, hReduced, A, b)
//
//    var checkR  = [byte](repeating: 0, count: 32)
//    R.ToBytes(&checkR)
//
//    for i in 0..<32
//    {
//        if sig[i] != checkR[i] {
//            return false
//        }
//    }
//
//    return true
//}

