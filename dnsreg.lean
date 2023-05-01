import data.buffer
import data.buffer.parser
import data.byte_array.parser
import data.nat.basic
import data.nat.gcd
import data.nat.prime
import data.set.basic
import data.string.basic
import init.data.nat.basic
import init.data.nat.gcd
import init.data.nat.prime

namespace DNSSEC

constant byte : Type := fin 256

structure RR : Type :=
(name : list byte)
(tpe : nat)
(cls : nat)
(ttl : nat)
(rdata : list byte)

structure DNSKEY : Type :=
(flags : nat)
(protocol : nat)
(algorithm : nat)
(key : list byte)

constant DNSKEY.toRR : DNSKEY → RR

structure DS : Type :=
(keyTag : nat)
(algorithm : nat)
(digestType : nat)
(digest : list byte)

constant DS.toRR : DS → RR

structure NSEC : Type :=
(nextDomainName : list byte)
(typesBitmap : list byte)

constant NSEC.toRR : NSEC → RR

structure RRSet : Type :=
(name : list byte)
(tpe : nat)
(cls : nat)
(ttl : nat)
(rrs : list RR)

structure RRSetWithSignature : Type :=
(rrset : RRSet)
(sig : list byte)

structure DNSSEC : Type :=
(keyCache : list DNSKEY)
(digestCache : list DS)
(rrsetCache : list RRSet)
(nsecCache : list NSEC)
(now : nat)

constant DNSSEC.sign : DNSKEY → list byte → list byte

constant DNSSEC.verify : list byte → DNSKEY → list byte → bool

constant DNSSEC.verifyRRSet : DNSSEC → RRSetWithSignature → (list byte × nat)

end DNSSEC

namespace DNSClaimChecker

constant getOwnerAddress : list byte → list byte → (option address × bool)

end DNSClaimChecker

namespace PublicSuffixList

constant isPublicSuffix : list byte → bool

end PublicSuffixList

namespace AddrResolver

constant setAddr : bytes32 → address → bool

end AddrResolver

namespace ENS

constant owner : bytes32 → address

constant resolver : bytes32 → address

constant setSubnodeOwner : bytes32 → bytes32 → address → bool

constant setSubnodeRecord : bytes32 → bytes32 → address → address → nat → bool

end ENS

namespace Root

constant owner : address

constant setSubnodeOwner : bytes32 → address → bool

end Root

namespace DNSRegistrar

constant inceptions : list (nat × bytes32) := []

constant NoOwnerRecordFound : Exception

constant PermissionDenied : address → address → Exception

constant PreconditionNotMet : Exception

constant StaleProof : Exception

constant InvalidPublicSuffix : list byte → Exception

structure OwnerRecord : Type :=
(name : list byte)
(owner : address)
(resolver : address)
(ttl : nat)

constant DNSRegistrar : Type :=
(previousRegistrar : address)
(resolver : address)
(dnssec : DNSSEC)
(suffixes : PublicSuffixList)
(ens : ENS)
(event Claim (node : bytes32) (owner : address) (dnsname : list byte) (inception : nat))

def DNSRegistrar.enableNode (domain : list byte) : bytes32 :=
let parent := DNSRegistrar.enableNode (list.drop (n + 1) domain),
label := hash (list.as_bytes [domain.head] |ₜ list.as_bytes domain.tail :: []),
node := hash (list.as_bytes parent :: list.as_bytes label :: []),
owner := ENS.owner node in
if owner = address.zero ∨ owner = DNSRegistrar.previousRegistrar then
let rootNode := if parent = bytes32.empty then bytes32.from_nat 0 else parent in
if parent = bytes32.empty then
let rootOwner := Root.owner in
let _ : msg.sender = rootOwner := sorry,
_ : ENS.setSubnodeOwner bytes32.empty label DNSRegistrar.ens = tt := sorry,
_ : ENS.setResolver node DNSRegistrar.resolver = tt := sorry in
else
let _ : msg.sender = owner := sorry,
_ : ENS.setSubnodeRecord parent label DNSRegistrar = tt := sorry,
_ : DNSRegistrar.resolver ≠ address.zero := sorry,
node' := hash (list.as_bytes parent :: list.as_bytes label :: []),
_ : owner = ENS.owner node' := sorry,
_ : addr ≠ address.zero → AddrResolver.setAddr node' addr := sorry in
node
else if owner = DNSRegistrar.ens.owner rootNode ∧ ownerRecord.owner = msg.sender then
let _ : ENS.setSubnodeRecord rootNode label owner DNSRegistrar.resolver 0 = tt := sorry,
node' := hash (list.as_bytes rootNode :: list.as_bytes label :: []),
_ : AddrResolver.setAddr node' addr := sorry in
node
else
throw PermissionDenied msg.sender owner

def DNSRegistrar._claim (name : list byte) (input : list DNSSEC.RRSetWithSignature) : (bytes32 × bytes32 × address) :=
let (rrset, sig) := input.head,
(data, inception) := DNSSEC.verifyRRSet DNSRegistrar.dnssec { rrset := rrset, sig := sig },
labelLen : nat := name.head.to_nat,
labelHash : bytes32 := hash (list.as_bytes name.tail.take labelLen :: []),
parentName : list byte := name.tail.drop labelLen + 1,
parentNode : bytes32 := DNSRegistrar.enableNode parentName,
node : bytes32 := hash (list.as_bytes parentNode :: list.as_bytes labelHash :: []),
_ : ∀ (n : nat), (n, node) ∈ DNSRegistrar.inceptions → n ≤ inception := sorry,
_ : node ∉ (λ x, prod.snd x) '' DNSRegistrar.inceptions := sorry,
owner : address := let (o, found) := DNSClaimChecker.getOwnerAddress name data in if ¬ found then throw DNSRegistrar.NoOwnerRecordFound else o,
_ : owner ∈ { Root.owner, DNSRegistrar.previousRegistrar, address } := sorry,
addr : address := if ¬ addr.is_zero input2 ∧ input2.head = rrset.tpe ∧ input2.tail.length = 20 then input2.tail.as_bytes.to_address else address.zero,
_ : owner = ENS.owner node := sorry,
_ : ENS.setSubnodeOwner parentNode labelHash owner = tt := sorry,
_ : DNSRegistrar.Claim.node = node ∧ DNSRegistrar.Claim.owner = owner ∧ DNSRegistrar.Claim.dnsname = name ∧ DNSRegistrar.Claim.inception = inception := sorry in
(parentNode, labelHash, owner)

def DNSRegistrar.proveAndClaimWithResolver (name : list byte) (input : list DNSSEC.RRSetWithSignature) (resolver : address) (addr : address) : bool :=
let (rootNode, labelHash, owner) := _claim name input in
if ¬ msg.sender = owner then throw (PermissionDenied msg.sender owner)
else
let _ : ENS.setSubnodeRecord rootNode labelHash owner resolver 0 = tt := sorry,
_ : addr ≠ address.zero → resolver ≠ address.zero := sorry,
node : bytes32 := hash (list.as_bytes rootNode :: list.as_bytes labelHash :: []),
_ : AddrResolver.setAddr node addr = tt := sorry in E

end DNSRegistrar
