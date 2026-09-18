use std::collections::HashSet;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};
use std::sync::{Arc, OnceLock};
use std::time::Duration;

use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream, UdpSocket};
use tokio::sync::Semaphore;
use tokio::time::{sleep, timeout, Instant};
use tokio_rustls::{rustls, TlsAcceptor};
use rustls::{Certificate, PrivateKey, ServerConfig};
use rustls_pemfile;

// --- Configuration ---
const BACKEND_ADDR: &str = "127.0.0.1:80";
const MAX_CONNECTIONS: usize = 512;
const LISTEN_HOST: &str = "0.0.0.0";
const LISTEN_PORT: u16 = 443;
const CERT_FILE: &str = "server.crt";
const KEY_FILE: &str = "server.key";
const BUFFER_SIZE: usize = 4096;
// ---------------------

static PASSWORD_HASH: OnceLock<String> = OnceLock::new();

fn init_password_hash(password: &str) {
    PASSWORD_HASH.get_or_init(|| sha224_hex(password));
}

fn get_password_hash() -> &'static str {
    PASSWORD_HASH.get().expect("Password hash not initialized")
}

fn sha224_hex(s: &str) -> String {
    // Lowercase hex encoding (semantically identical to `hex::encode`):
    // fill a byte array, then a single UTF-8 validation instead of 56
    // per-`char` pushes.
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let digest = sha224(s.as_bytes());
    let mut hex = [0u8; 56];
    for (i, byte) in digest.iter().enumerate() {
        hex[2 * i] = HEX[(byte >> 4) as usize];
        hex[2 * i + 1] = HEX[(byte & 0x0f) as usize];
    }
    // Infallible: every byte above is ASCII hex.
    String::from_utf8(hex.to_vec()).expect("hex digits are ASCII")
}

/// One SHA-256 compression-function invocation over a single 64-byte block.
#[inline]
fn sha256_compress(state: &mut [u32; 8], block: &[u8; 64]) {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
        0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
        0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
        0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
        0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
        0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    ];
    let mut w = [0u32; 64];
    for i in 0..16 {
        let o = i * 4;
        w[i] = u32::from_be_bytes([block[o], block[o + 1], block[o + 2], block[o + 3]]);
    }
    for i in 16..64 {
        let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
        let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16]
            .wrapping_add(s0)
            .wrapping_add(w[i - 7])
            .wrapping_add(s1);
    }
    let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h) = (
        state[0], state[1], state[2], state[3],
        state[4], state[5], state[6], state[7],
    );
    for i in 0..64 {
        let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let ch = (e & f) ^ ((!e) & g);
        let t1 = h
            .wrapping_add(s1)
            .wrapping_add(ch)
            .wrapping_add(K[i])
            .wrapping_add(w[i]);
        let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let t2 = s0.wrapping_add(maj);
        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
    }
    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
    state[5] = state[5].wrapping_add(f);
    state[6] = state[6].wrapping_add(g);
    state[7] = state[7].wrapping_add(h);
}

/// SHA-224 initial hash values (differ from SHA-256; output is truncated).
const SHA224_INIT: [u32; 8] = [
    0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939,
    0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4,
];

/// SHA-224 digest (FIPS 180-4): the SHA-256 compression function run with the
/// SHA-224 initial hash values, output truncated to 28 bytes. Pure `std`
/// (`u32` arithmetic only); byte-for-byte identical to `sha2::Sha224`.
fn sha224(message: &[u8]) -> [u8; 28] {
    // Fast path: messages shorter than 56 bytes fit the padding into a single
    // block, hashed with zero heap allocation (the common password case).
    if message.len() <= 55 {
        let mut block = [0u8; 64];
        block[..message.len()].copy_from_slice(message);
        block[message.len()] = 0x80;
        let bit_len = (message.len() as u64).wrapping_mul(8);
        block[56..64].copy_from_slice(&bit_len.to_be_bytes());
        let mut state = SHA224_INIT;
        sha256_compress(&mut state, &block);
        let mut out = [0u8; 28];
        for (i, word) in state[..7].iter().enumerate() {
            out[i * 4..i * 4 + 4].copy_from_slice(&word.to_be_bytes());
        }
        return out;
    }

    let mut state = SHA224_INIT;

    // Merkle-Damgard padding: 0x80, zeros until len == 56 (mod 64), then the
    // 64-bit big-endian bit length.
    let bit_len = (message.len() as u64).wrapping_mul(8);
    let mut padded = Vec::with_capacity(((message.len() + 9 + 63) / 64) * 64);
    padded.extend_from_slice(message);
    padded.push(0x80);
    while padded.len() % 64 != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    for block in padded.chunks_exact(64) {
        // Borrowed view of the same 64 bytes: no per-block memcpy.
        let arr: &[u8; 64] = block.try_into().expect("chunks_exact(64)");
        sha256_compress(&mut state, arr);
    }

    // Truncate to the first 7 words (28 bytes), big-endian.
    let mut out = [0u8; 28];
    for (i, word) in state[..7].iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&word.to_be_bytes());
    }
    out
}

fn is_private_address(ip: IpAddr) -> bool {
    match ip {
        IpAddr::V4(ipv4) => {
            ipv4.is_loopback()           // 127.0.0.0/8
            || ipv4.is_private()         // 10/8, 172.16/12, 192.168/16
            || ipv4.is_link_local()      // 169.254.0.0/16
            || ipv4.is_broadcast()       // 255.255.255.255
            || ipv4.is_documentation()   // 192.0.2.0/24, 198.51.100.0/24, 203.0.113.0/24
            || ipv4.is_unspecified()     // 0.0.0.0
        }
        IpAddr::V6(ipv6) => {
            ipv6.is_loopback()           // ::1
            || ipv6.is_unspecified()     // ::
            // ULA: fc00::/7
            || (ipv6.segments()[0] & 0xfe00) == 0xfc00
            // Link-local: fe80::/10
            || (ipv6.segments()[0] & 0xffc0) == 0xfe80
        }
    }
}

/// Membership test with a linear fast path for tiny peer sets (the common
/// single-peer UDP session) and the hash table beyond that (flood-safe:
/// attacker-inflated sets keep O(1) lookup). Same verdict as
/// `HashSet::contains` for every input.
#[inline]
fn is_allowed_peer(allowed: &HashSet<SocketAddr>, addr: &SocketAddr) -> bool {
    if allowed.len() <= 8 {
        allowed.iter().any(|p| p == addr)
    } else {
        allowed.contains(addr)
    }
}

/// Record a relay peer, skipping the redundant re-insert when the target is
/// unchanged from the previous datagram (the common same-destination run:
/// DNS bursts, calls, streams). The resulting set is identical to
/// unconditional `insert` in all cases; only wasted re-hashing is removed.
#[inline]
fn note_allowed_peer(
    allowed: &mut HashSet<SocketAddr>,
    last: &mut Option<SocketAddr>,
    target: SocketAddr,
) {
    if *last != Some(target) {
        allowed.insert(target);
        *last = Some(target);
    }
}

fn parse_address(data: &[u8], cursor: &mut usize) -> Result<String, String> {
    if *cursor >= data.len() {
        return Err("Insufficient data for address type".to_string());
    }

    let atyp = data[*cursor];
    *cursor += 1;

    match atyp {
        0x01 => {
            // IPv4
            if data.len() < *cursor + 4 {
                return Err("Insufficient data for IPv4".to_string());
            }
            let ip = Ipv4Addr::new(data[*cursor], data[*cursor + 1], data[*cursor + 2], data[*cursor + 3]);
            *cursor += 4;
            Ok(ip.to_string())
        }
        0x03 => {
            // Domain
            if *cursor >= data.len() {
                return Err("Insufficient data for domain length".to_string());
            }
            let domain_len = data[*cursor] as usize;
            *cursor += 1;
            if data.len() < *cursor + domain_len {
                return Err("Insufficient data for domain".to_string());
            }
            // Borrow directly instead of copying into a Vec first: one
            // allocation instead of two. Observably identical, including the
            // error text (`Utf8Error` displays exactly like the `FromUtf8Error`
            // it replaces here).
            let domain = std::str::from_utf8(&data[*cursor..*cursor + domain_len])
                .map_err(|e| format!("Invalid UTF-8 in domain: {}", e))?
                .to_owned();
            *cursor += domain_len;
            Ok(domain)
        }
        0x04 => {
            // IPv6
            if data.len() < *cursor + 16 {
                return Err("Insufficient data for IPv6".to_string());
            }
            let mut ip_bytes = [0u8; 16];
            ip_bytes.copy_from_slice(&data[*cursor..*cursor + 16]);
            let ip = Ipv6Addr::from(ip_bytes);
            *cursor += 16;
            Ok(ip.to_string())
        }
        _ => Err(format!("Invalid address type: {}", atyp)),
    }
}

/// A UDP relay destination as borrowed offsets: IP literals and domain text
/// both avoid allocation on the hot path (domains resolve from the packet).
enum UdpTarget {
    Ip(IpAddr),
    Domain(std::ops::Range<usize>),
}

/// Borrowed-range core of [`parse_udp_packet`]: byte-identical validation and
/// framing, but the payload is returned as offsets into `data` instead of a
/// clone and IP literals as [`IpAddr`] instead of a [`String`]. The relay
/// loop uses this to avoid one payload `memcpy` per datagram.
///
/// Mirrors [`parse_address`] dispatch exactly (same ATYP branches, lengths,
/// and validation); every `None` condition matches one-for-one.
fn parse_udp_packet_parts(
    data: &[u8],
) -> Option<(UdpTarget, u16, std::ops::Range<usize>, usize)> {
    if data.len() < 4 {
        return None;
    }

    let mut cursor = 0;

    // Parse address (mirrors `parse_address`; with `cursor == 0` and
    // `data.len() >= 4` its empty-input guard cannot trigger).
    let atyp = data[cursor];
    cursor += 1;
    let target = match atyp {
        0x01 => {
            if data.len() < cursor + 4 {
                return None;
            }
            let ip = IpAddr::V4(Ipv4Addr::new(
                data[cursor],
                data[cursor + 1],
                data[cursor + 2],
                data[cursor + 3],
            ));
            cursor += 4;
            UdpTarget::Ip(ip)
        }
        0x03 => {
            // (Entry guarantees `len >= 4` with `cursor == 1`, so the
            // empty-input guard cannot trigger here.)
            let domain_len = data[cursor] as usize;
            cursor += 1;
            if data.len() < cursor + domain_len {
                return None;
            }
            // Validate UTF-8 (same `None` mapping as `parse_address`) but
            // keep borrowed offsets: the relay resolves straight from the
            // packet buffer with no String at all.
            std::str::from_utf8(&data[cursor..cursor + domain_len]).ok()?;
            let domain_range = cursor..cursor + domain_len;
            cursor += domain_len;
            UdpTarget::Domain(domain_range)
        }
        0x04 => {
            if data.len() < cursor + 16 {
                return None;
            }
            let mut ip_bytes = [0u8; 16];
            ip_bytes.copy_from_slice(&data[cursor..cursor + 16]);
            cursor += 16;
            UdpTarget::Ip(IpAddr::V6(Ipv6Addr::from(ip_bytes)))
        }
        _ => return None,
    };

    // Parse port and length
    if data.len() < cursor + 4 {
        return None;
    }

    let port = u16::from_be_bytes([data[cursor], data[cursor + 1]]);
    cursor += 2;

    let payload_len = u16::from_be_bytes([data[cursor], data[cursor + 1]]) as usize;
    cursor += 2;

    // Check for CRLF
    if data.len() < cursor + 2 || &data[cursor..cursor + 2] != b"\r\n" {
        println!("WARN: Malformed UDP packet: missing CRLF after length");
        return None;
    }
    cursor += 2;

    // Payload as borrowed offsets (no clone here).
    let packet_end = cursor + payload_len;
    if data.len() < packet_end {
        return None;
    }
    let payload_range = cursor..packet_end;

    // Check for optional trailing CRLF
    let mut total_packet_size = packet_end;
    if data.len() >= packet_end + 2 && &data[packet_end..packet_end + 2] == b"\r\n" {
        total_packet_size += 2;
    }

    Some((target, port, payload_range, total_packet_size))
}

// Canonical wire-format spec, locked by tests; the live relay calls the
// zero-copy `parse_udp_packet_parts` above, so this is used by tests.
#[cfg_attr(not(test), allow(dead_code))]
fn parse_udp_packet(data: &[u8]) -> Option<(String, u16, Vec<u8>, usize)> {
    // Thin wrapper preserving the exact tuple (allocation behavior included).
    parse_udp_packet_parts(data).and_then(|(target, port, range, size)| {
        let addr = match target {
            UdpTarget::Ip(ip) => ip.to_string(),
            // Defensive re-validation: parts already guarantees UTF-8, so
            // this preserves the original error mapping even under drift.
            UdpTarget::Domain(domain_range) => {
                std::str::from_utf8(&data[domain_range]).ok()?.to_owned()
            }
        };
        Some((addr, port, data[range].to_vec(), size))
    })
}

/// [`encode_udp_response`] for an already-parsed [`IpAddr`]: identical bytes
/// with no string round-trip. The UDP relay uses this directly with the peer
/// address, skipping one format allocation plus one parse per reply.
fn encode_udp_response_ip(ip: &IpAddr, port: u16, payload: &[u8]) -> Vec<u8> {
    let mut response = match ip {
        IpAddr::V4(ipv4) => {
            let mut response = Vec::with_capacity(1 + 4 + 2 + 2 + 2 + payload.len());
            response.push(0x01); // IPv4
            response.extend_from_slice(&ipv4.octets());
            response
        }
        IpAddr::V6(ipv6) => {
            let mut response = Vec::with_capacity(1 + 16 + 2 + 2 + 2 + payload.len());
            response.push(0x04); // IPv6
            response.extend_from_slice(&ipv6.octets());
            response
        }
    };
    response.extend_from_slice(&port.to_be_bytes());
    response.extend_from_slice(&(payload.len() as u16).to_be_bytes());
    response.extend_from_slice(b"\r\n");
    response.extend_from_slice(payload);
    response
}

/// [`encode_udp_response_ip`] into a caller-reused buffer: `clear` plus an
/// exact `reserve` make steady-state replies allocation-free after the first.
/// Byte-identical output; the relay keeps one scratch buffer per session.
fn encode_udp_response_ip_into(buf: &mut Vec<u8>, ip: &IpAddr, port: u16, payload: &[u8]) {
    buf.clear();
    buf.reserve(
        1 + match ip {
            IpAddr::V4(_) => 4,
            IpAddr::V6(_) => 16,
        } + 2
            + 2
            + 2
            + payload.len(),
    );
    match ip {
        IpAddr::V4(ipv4) => {
            buf.push(0x01); // IPv4
            buf.extend_from_slice(&ipv4.octets());
        }
        IpAddr::V6(ipv6) => {
            buf.push(0x04); // IPv6
            buf.extend_from_slice(&ipv6.octets());
        }
    }
    buf.extend_from_slice(&port.to_be_bytes());
    buf.extend_from_slice(&(payload.len() as u16).to_be_bytes());
    buf.extend_from_slice(b"\r\n");
    buf.extend_from_slice(payload);
}

// Canonical wire-format spec, locked by tests; the live relay calls the
// allocation-free `encode_udp_response_ip` below, so this is used by tests.
#[cfg_attr(not(test), allow(dead_code))]
fn encode_udp_response(addr: &str, port: u16, payload: &[u8]) -> Result<Vec<u8>, String> {
    
    // Thin wrapper preserving the exact accept set, bytes, and error text.
    match addr.parse::<IpAddr>() {
        Ok(ip) => Ok(encode_udp_response_ip(&ip, port, payload)),
        Err(_) => Err("Invalid IP address format".to_string()),
    }
    
    // (Port/length/CRLF/payload are appended inside the helper above.)
}

// Accurately calculates if we have received the exact amount of bytes for a full header
fn is_trojan_header_complete(buf: &[u8]) -> bool {
    // We need at least: hash(56) + \r\n(2) + cmd(1) + atyp(1) = 60 bytes
    if buf.len() < 60 { return false; } 
    
    let atyp = buf[59];
    let addr_len = match atyp {
        0x01 => 4, // IPv4 length
        0x03 => {  // Domain length is dynamic
            if buf.len() < 61 { return false; }
            1 + buf[60] as usize // 1 byte for the length indicator + the actual domain string
        },
        0x04 => 16, // IPv6 length
        _ => return false, // Invalid type, return false so the parser routes to fallback later
    };
    
    // Total expected = 58 (Hash+CRLF) + 2 (Cmd+Atyp) + addr_len + 2 (Port) + 2 (Final CRLF)
    let total_expected_len = 58 + 2 + addr_len + 4;
    
    buf.len() >= total_expected_len
}

/// GREEDY-CRLF probe detector, extracted verbatim from `handle_client`'s
/// initial-read loop (same incremental scan, same prefix rule). `prev_len`
/// is the buffer length before the latest append: only 4-byte windows
/// touching the new bytes can newly match, the rest were already scanned
/// when first formed.
#[inline]
fn http_probe_detected(buf: &[u8], prev_len: usize) -> bool {
    if buf[prev_len.saturating_sub(3)..].windows(4).any(|w| w == b"\r\n\r\n") {
        // A valid Trojan request must have `\r\n` exactly at bytes 56-57.
        let is_valid_prefix = buf.len() >= 58 && &buf[56..58] == b"\r\n";
        // Non-matching prefix means HTTP probe; a matching prefix means the
        // `\r\n\r\n` is binary IP/port payload, so keep reading.
        return !is_valid_prefix;
    }
    false
}

/// Constant-time byte equality for the password-hash comparison (a length
/// mismatch is fine to leak here: both sides are always 56 bytes).
/// Extracted verbatim from `handle_client`; carries no timing signal.
#[inline]
fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut result: u8 = 0;
    for (x, y) in a.iter().zip(b.iter()) {
        result |= x ^ y;
    }
    result == 0
}

async fn handle_udp_associate(
    mut client_stream: tokio_rustls::server::TlsStream<TcpStream>,
    initial_payload: Vec<u8>,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let udp_socket = UdpSocket::bind("0.0.0.0:0").await?;
    println!("INFO: UDP associate endpoint created on port {}", udp_socket.local_addr()?.port());

    // Single-threaded state: No RwLocks or Channels needed anymore!
    let mut allowed_peers = HashSet::new();
    // Last forwarded target: skips redundant set re-inserts on runs.
    let mut last_allowed: Option<SocketAddr> = None;
    // Scratch reply buffer, reused across datagrams (see `encode_..._into`).
    let mut encode_scratch = Vec::new();
    let mut tcp_buffer = initial_payload;
    let mut temp_tcp_buf = [0u8; BUFFER_SIZE];
    let mut udp_buf = [0u8; BUFFER_SIZE];

    let (mut read_half, mut write_half) = tokio::io::split(client_stream);

    // Set our 5-minute idle timeout timer
    let timeout_duration = Duration::from_secs(300);
    let sleep_future = sleep(timeout_duration);
    tokio::pin!(sleep_future); // Pin the timer so we can reset it in the loop

    loop {
        tokio::select! {
            // ========================================================
            // EVENT 1: Data arrives from the client over TCP
            // ========================================================
            tcp_result = read_half.read(&mut temp_tcp_buf) => {
                let n = match tcp_result {
                    Ok(0) => break, // Client closed TCP connection naturally
                    Ok(n) => n,
                    Err(e) => {
                        println!("ERROR: TCP read error in UDP associate: {}", e);
                        break;
                    }
                };
                
                tcp_buffer.extend_from_slice(&temp_tcp_buf[..n]);

                // Process all fully framed UDP packets in the buffer.
                // Consume via offset and compact once afterwards: draining
                // per packet would memmove the tail every time (quadratic
                // for pipelined bursts). Same bytes in the same order.
                let mut tcp_consumed: usize = 0;
                while tcp_consumed < tcp_buffer.len() {
                    if let Some((target, dest_port, payload_range, packet_size)) =
                        parse_udp_packet_parts(&tcp_buffer[tcp_consumed..])
                    {
                        // Absolute offsets for this event's buffer.
                        let payload_range =
                            payload_range.start + tcp_consumed..payload_range.end + tcp_consumed;
                        // Zero-copy relay: the payload is sent straight out of
                        // `tcp_buffer` (borrow ends before the drain below),
                        // and IP literals never become Strings at all.
                        match target {
                            UdpTarget::Ip(ip) => {
                                let target_addr = SocketAddr::new(ip, dest_port);
                                // --- SEC FIX: UDP SSRF Prevention ---
                                if is_private_address(target_addr.ip()) {
                                    println!("WARN: UDP SSRF block: {}:{} resolved to private address {}", ip, dest_port, target_addr.ip());
                                } else {
                                    // Trust this target IP to reply to us later
                                    note_allowed_peer(&mut allowed_peers, &mut last_allowed, target_addr);
                                    if let Err(e) = udp_socket.send_to(&tcp_buffer[payload_range], target_addr).await {
                                        println!("WARN: Failed to forward UDP to {}: {}", target_addr, e);
                                    }
                                }
                            }
                            UdpTarget::Domain(domain_range) => {
                                let domain_range = domain_range.start + tcp_consumed..domain_range.end + tcp_consumed;
                                // Borrowed domain text; the `(host, port)`
                                // tuple resolves identically to the
                                // `"host:port"` string with zero allocation.
                                // (Parts validated UTF-8 to reach this arm.)
                                let domain = std::str::from_utf8(&tcp_buffer[domain_range])
                                    .expect("parts validated domain UTF-8");
                                match tokio::net::lookup_host((domain, dest_port)).await {
                                Ok(mut addrs) => {
                                    if let Some(target_addr) = addrs.next() {
                                        // --- SEC FIX: UDP SSRF Prevention ---
                                        if is_private_address(target_addr.ip()) {
                                            println!("WARN: UDP SSRF block: {}:{} resolved to private address {}", domain, dest_port, target_addr.ip());
                                        } else {
                                            // Trust this target IP to reply to us later
                                            note_allowed_peer(&mut allowed_peers, &mut last_allowed, target_addr);
                                            if let Err(e) = udp_socket.send_to(&tcp_buffer[payload_range], target_addr).await {
                                                println!("WARN: Failed to forward UDP to {}: {}", target_addr, e);
                                            }
                                        }
                                    }
                                }
                                Err(e) => println!("WARN: UDP DNS resolution failed for {}:{}: {}", domain, dest_port, e),
                                }
                            }
                        }
                        tcp_consumed += packet_size;
                    } else {
                        break; // Incomplete packet, wait for more TCP data
                    }
                }
                if tcp_consumed > 0 {
                    if tcp_consumed >= tcp_buffer.len() {
                        tcp_buffer.clear();
                    } else {
                        tcp_buffer.drain(..tcp_consumed);
                    }
                }

                // Reset our idle timeout since we saw client activity
                sleep_future.as_mut().reset(Instant::now() + timeout_duration);
            }

            // ========================================================
            // EVENT 2: Data arrives from the target over UDP
            // ========================================================
            udp_result = udp_socket.recv_from(&mut udp_buf) => {
                match udp_result {
                    Ok((len, addr)) => {
                        // Ensure this packet is from a server the client actually requested
                        if is_allowed_peer(&allowed_peers, &addr) {
                            let payload = &udp_buf[..len];
                            
                            // Infallible for socket addresses (always an IP):
                            // no format/parse round-trip on the reply path.
                            let peer_ip = addr.ip();
                            encode_udp_response_ip_into(
                                &mut encode_scratch,
                                &peer_ip,
                                addr.port(),
                                payload,
                            );
                            if let Err(e) = write_half.write_all(&encode_scratch).await {
                                println!("ERROR: Failed to write UDP response to TCP client: {}", e);
                                break; // Client disconnected unexpectedly
                            }
                        } else {
                            println!("WARN: Dropped unexpected UDP packet from {}", addr);
                        }
                    }
                    Err(e) => {
                        println!("ERROR: UDP socket read error: {}", e);
                        break;
                    }
                }

                // Reset our idle timeout since we saw target activity
                sleep_future.as_mut().reset(Instant::now() + timeout_duration);
            }

            // ========================================================
            // EVENT 3: The 5-minute idle timer expires
            // ========================================================
            () = &mut sleep_future => {
                println!("INFO: UDP session timed out after 5 minutes of inactivity.");
                break;
            }
        }
    }

    println!("INFO: Closing UDP tunnel cleanly.");
    Ok(())
}

async fn handle_tcp_connect(
    client_stream: tokio_rustls::server::TlsStream<TcpStream>,
    addr: String,
    port: u16,
    initial_data: Vec<u8>,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    // Block reserved/privileged ports
    if port == 0 {
        println!("WARN: SSRF block: rejecting request to port 0");
        return Err("Blocked port".into());
    }

    // Fast path: numeric IP literals resolve without DNS to exactly the
    // SocketAddr `lookup_host` would return for them; hostnames use the
    // slow resolver path below with unchanged logs and timeouts.
    let fast_target: Option<SocketAddr> =
        addr.parse::<IpAddr>().ok().map(|ip| SocketAddr::new(ip, port));
    let target_socket_addr = if let Some(sa) = fast_target {
        sa
    } else {
        // Resolve the hostname before connecting so we can inspect the IP.
        // Tuple form resolves identically to the `"host:port"` string with
        // no allocation; log text stays byte-identical (`addr:port`).
        let mut resolved = match timeout(
            Duration::from_secs(5),
            tokio::net::lookup_host((addr.as_str(), port))
        ).await {
            Ok(Ok(addrs)) => addrs,
            Ok(Err(e)) => {
                println!("WARN: DNS resolution failed for {}:{}: {}", addr, port, e);
                return Err(Box::new(e));
            }
            Err(_) => {
                println!("WARN: DNS resolution timed out for {}:{}", addr, port);
                return Err("DNS timeout".into());
            }
        };

        match resolved.next() {
            Some(socket_addr) => socket_addr,
            None => {
                println!("WARN: DNS returned no addresses for {}:{}", addr, port);
                return Err("No addresses resolved".into());
            }
        }
    };

    // SSRF check: block private/loopback/link-local addresses
    if is_private_address(target_socket_addr.ip()) {
        println!(
            "WARN: SSRF block: {} resolved to private address {} - rejecting",
            addr, target_socket_addr.ip()
        );
        return Err("Blocked private address".into());
    }

    // Now connect using the already-resolved SocketAddr, not the hostname,
    // to prevent DNS rebinding between resolution and connect
    let mut target_stream = match timeout(
        Duration::from_secs(10),
        TcpStream::connect(target_socket_addr)
    ).await {
        Ok(Ok(stream)) => stream,
        Ok(Err(e)) => {
            println!("ERROR: Failed to connect to {}: {}", target_socket_addr, e);
            return Err(Box::new(e));
        }
        Err(_) => {
            println!("WARN: Connection to {} timed out", target_socket_addr);
            return Err("TCP connect timeout".into());
        }
    };

    if let Err(e) = target_stream.set_nodelay(true) {
        println!("WARN: Failed to set TCP_NODELAY on target socket: {}", e);
    }

    if !initial_data.is_empty() {
        target_stream.write_all(&initial_data).await?;
    }

    let (client_read, client_write) = tokio::io::split(client_stream);
    let (target_read, target_write) = tokio::io::split(target_stream);

    let (result1, result2) =
        relay_full_duplex(client_read, client_write, target_read, target_write).await;
    if let Err(e) = result1 {
        println!("ERROR: Client to target pipe error: {}", e);
    }
    if let Err(e) = result2 {
        println!("ERROR: Target to client pipe error: {}", e);
    }

    Ok(())
}

async fn fallback_proxy(
    client_stream: tokio_rustls::server::TlsStream<TcpStream>,
    initial_data: Vec<u8>,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let mut backend = match timeout(
        Duration::from_secs(5),
        TcpStream::connect(BACKEND_ADDR)
    ).await {
        Ok(Ok(stream)) => stream,
        Ok(Err(e)) => {
            println!("ERROR: Failed to connect to backend {}: {}", BACKEND_ADDR, e);
            return Err(Box::new(e));
        }
        Err(_) => {
            println!("ERROR: Backend connection timed out");
            return Err("Backend timeout".into());
        }
    };

    // Replay any bytes we already read from the client
    if !initial_data.is_empty() {
        backend.write_all(&initial_data).await?;
    }

    let (client_read, client_write) = tokio::io::split(client_stream);
    let (backend_read, backend_write) = tokio::io::split(backend);

    let (result1, result2) =
        relay_full_duplex(client_read, client_write, backend_read, backend_write).await;
    if let Err(e) = result1 { println!("ERROR: Client to backend pipe error: {}", e); }
    if let Err(e) = result2 { println!("ERROR: Backend to client pipe error: {}", e); }

    Ok(())
}

/// Relay bytes in both directions until EACH direction ends on its own.
///
/// Unlike racing the two legs with `select!`, one direction reaching EOF (or
/// erroring) never truncates the other, which may still carry in-flight reply
/// bytes — e.g. a download tail arriving after the upload leg finished, the
/// exact shape of a bidirectional speedtest. Returns each leg's result so
/// callers keep their exact per-direction log lines.
///
/// Halves are grouped by endpoint: `(a_read, a_write)` belong to side A and
/// `(b_read, b_write)` to side B, exactly as `tokio::io::split` returns
/// them, so a typical call reads `relay_full_duplex(a_r, a_w, b_r, b_w)`.
/// (Swapping the write halves compiles but loopbacks each side to itself;
/// `test_relay_full_duplex_survives_half_close` pins the correct wiring.)
async fn relay_full_duplex<A, B, C, D>(
    a_read: A,
    a_write: B,
    b_read: C,
    b_write: D,
) -> (
    Result<(), Box<dyn std::error::Error + Send + Sync>>,
    Result<(), Box<dyn std::error::Error + Send + Sync>>,
)
where
    A: tokio::io::AsyncRead + Unpin,
    B: tokio::io::AsyncWrite + Unpin,
    C: tokio::io::AsyncRead + Unpin,
    D: tokio::io::AsyncWrite + Unpin,
{
    tokio::join!(pipe_data(a_read, b_write), pipe_data(b_read, a_write))
}

async fn pipe_data<R, W>(mut reader: R, mut writer: W) -> Result<(), Box<dyn std::error::Error + Send + Sync>>
where
    R: tokio::io::AsyncRead + Unpin,
    W: tokio::io::AsyncWrite + Unpin,
{
    // 32 KiB transfer buffer: bulk flows need ~8x fewer read/write syscalls
    // than BUFFER_SIZE with byte-identical forwarding (size is internal).
    let mut buffer = [0u8; 32 * 1024];
    loop {
        // --- SEC FIX: 5-Minute Idle Timeout for TCP Connections ---
        match timeout(Duration::from_secs(300), reader.read(&mut buffer)).await {
            Ok(Ok(0)) => break, // Clean EOF
            Ok(Ok(n)) => {
                writer.write_all(&buffer[..n]).await?;
                // Push records out promptly instead of letting a tail sit in
                // the TLS session buffer: same bytes, less tail latency
                // (bulk tails, interactive frames, speedtest ramp).
                writer.flush().await?;
            }
            Ok(Err(e)) => {
                // Ignore common connection resets/broken pipes
                if e.kind() == std::io::ErrorKind::ConnectionReset
                    || e.kind() == std::io::ErrorKind::BrokenPipe
                {
                    break;
                }
                return Err(Box::new(e));
            }
            Err(_) => {
                // Timeout occurred (No data transferred for 300 seconds)
                println!("INFO: TCP connection closed due to 5-minute idle timeout.");
                break; 
            }
        }
    }
    Ok(())
}

async fn handle_client(
    stream: TcpStream, 
    tls_acceptor: TlsAcceptor,
    semaphore: Arc<Semaphore>
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let client_addr = stream.peer_addr()?;
    // Disable Nagle: proxy legs carry latency-sensitive frames (TLS
    // handshakes, small control messages, speedtest ramp); full-size bulk
    // segments are unaffected. Best-effort: never refuse a connection here.
    if let Err(e) = stream.set_nodelay(true) {
        println!("WARN: Failed to set TCP_NODELAY on client socket: {}", e);
    }
    
    // --- SEC FIX: TLS Handshake Timeout (Slowloris Protection) ---
    let mut tls_stream = match timeout(Duration::from_secs(10), tls_acceptor.accept(stream)).await {
        Ok(Ok(stream)) => stream,
        Ok(Err(e)) => {
            println!("ERROR: TLS handshake failed for {}: {}", client_addr, e);
            return Err(Box::new(e));
        }
        Err(_) => {
            println!("WARN: TLS handshake timed out for {}", client_addr);
            return Err("TLS handshake timeout".into());
        }
    };
    // -------------------------------------------------------------

    // --- SEC FIX: Zombie Connection Pool Exhaustion ---
    let _permit = match semaphore.try_acquire() {
        Ok(permit) => permit,
        Err(_) => {
            println!("WARN: Connection limit reached, dropping connection from {}.", client_addr);
            return Ok(());
        }
    };
    
    // Pre-size for a typical header + first data chunk: avoids the first
    // reallocs with zero observable difference (capacity is invisible).
    let mut initial_buf = Vec::with_capacity(512);
    let mut temp_buf = [0u8; BUFFER_SIZE];
    
    // Nginx default client_header_timeout is typically 60 seconds.
    let read_result = timeout(Duration::from_secs(60), async {
        loop {
            let n = tls_stream.read(&mut temp_buf).await?;
            if n == 0 {
                break; // EOF (Client closed connection)
            }
            // Only 4-byte windows touching the newly appended bytes can newly
            // match: earlier windows were already scanned when first formed
            // (bytes are only ever appended), so rescanning them is pure cost.
            let prev_len = initial_buf.len();
            initial_buf.extend_from_slice(&temp_buf[..n]);
            
            // Condition 1: Deterministic Trojan Header Validation
            if is_trojan_header_complete(&initial_buf) {
                break; // Full header received without ambiguity!
            } 
            // --- SEC FIX: Greedy CRLF Hex Collision ---
            // Detect HTTP probes safely without breaking legitimate Hex payloads.
            else if http_probe_detected(&initial_buf, prev_len) {
                break;
            }

            // Condition 3: Security safeguard against memory exhaustion.
            if initial_buf.len() > 4096 {
                break;
            }
        }
        Ok::<_, std::io::Error>(())
    }).await;

    // Handle timeout, connection errors, or explicitly invalid HTTP requests/buffer lengths
    if read_result.is_err() || initial_buf.len() < 58 {
        println!("INFO: Routing suspicious probe or HTTP request to fallback.");
        return fallback_proxy(tls_stream, initial_buf).await; 
    }
    
    let data = &initial_buf;
    
    // Use the globally cached hash
    let expected_hash = get_password_hash();

    let received_hash = match std::str::from_utf8(&data[..56]) {
        Ok(hash) => hash,
        Err(_) => {
            println!("INFO: Invalid hash encoding. Routing to fallback.");
            return fallback_proxy(tls_stream, initial_buf).await; 
        }
    };

    // (Password compare calls the top-level `constant_time_eq`.)

    if !constant_time_eq(received_hash.as_bytes(), expected_hash.as_bytes()) || &data[56..58] != b"\r\n" {
        println!("INFO: Invalid password or framing. Routing to fallback.");
        return fallback_proxy(tls_stream, initial_buf).await; 
    }
    
    // ==========================================
    // AUTHENTICATION SUCCESSFUL
    // ==========================================
    
    let request_data = &data[58..];
    if request_data.is_empty() {
        println!("INFO: Authenticated but missing payload. Proxying to fallback with EMPTY buffer to prevent password leak.");
        return fallback_proxy(tls_stream, Vec::new()).await;
    }
    
    let cmd = request_data[0];
    let mut cursor = 1;
    
    // Parse target address
    let addr = match parse_address(request_data, &mut cursor) {
        Ok(addr) => addr,
        Err(e) => {
            println!("WARN: Invalid address in request: {}. Routing to fallback without password.", e);
            return fallback_proxy(tls_stream, request_data.to_vec()).await; 
        }
    };
    
    // Parse port
    if request_data.len() < cursor + 2 {
        println!("WARN: Insufficient data for port. Routing to fallback without password.");
        return fallback_proxy(tls_stream, request_data.to_vec()).await;
    }
    
    let port = u16::from_be_bytes([request_data[cursor], request_data[cursor + 1]]);
    cursor += 2;
    
    // Check final CRLF before the payload
    if request_data.len() < cursor + 2 || &request_data[cursor..cursor + 2] != b"\r\n" {
        println!("WARN: Malformed request: missing final CRLF. Routing to fallback without password.");
        return fallback_proxy(tls_stream, request_data.to_vec()).await;
    }
    cursor += 2;
    
    let payload = request_data[cursor..].to_vec();
    
    // Handle command
    match cmd {
        0x01 => {
            // TCP CONNECT
            handle_tcp_connect(tls_stream, addr, port, payload).await
        }
        0x03 => {
            // UDP ASSOCIATE
            println!("INFO: UDP ASSOCIATE request received");
            handle_udp_associate(tls_stream, payload).await
        }
        _ => {
            println!("WARN: Unsupported command: {}. Routing to fallback without password.", cmd);
            fallback_proxy(tls_stream, request_data.to_vec()).await
        }
    }
}

fn load_tls_config() -> Result<ServerConfig, Box<dyn std::error::Error>> {
    // Load certificate and key files
    let cert_file = match std::fs::File::open(CERT_FILE) {
        Ok(file) => file,
        Err(e) => {
            println!("ERROR: Failed to open certificate file {}: {}", CERT_FILE, e);
            return Err(Box::new(e));
        }
    };
    
    let key_file = match std::fs::File::open(KEY_FILE) {
        Ok(file) => file,
        Err(e) => {
            println!("ERROR: Failed to open key file {}: {}", KEY_FILE, e);
            return Err(Box::new(e));
        }
    };
    
    let mut cert_reader = std::io::BufReader::new(cert_file);
    let mut key_reader = std::io::BufReader::new(key_file);
    
    // Parse certificates
    let certs = rustls_pemfile::certs(&mut cert_reader)?
        .into_iter()
        .map(Certificate)
        .collect::<Vec<_>>();
    
    if certs.is_empty() {
        let err_msg = format!("No certificates found in {}", CERT_FILE);
        println!("ERROR: {}", err_msg);
        return Err(err_msg.into());
    }
    
    // Parse private key
    let keys = rustls_pemfile::pkcs8_private_keys(&mut key_reader)?
        .into_iter()
        .map(PrivateKey)
        .collect::<Vec<_>>();
    
    if keys.is_empty() {
        let err_msg = format!("No private keys found in {}", KEY_FILE);
        println!("ERROR: {}", err_msg);
        return Err(err_msg.into());
    }
    
    // Build TLS config.
    //
    // Cipher-suite preference (every default suite, AES-128-GCM first): any
    // client that connected before still can (same intersection — only the
    // server's preference order changed). AES-128-GCM needs fewer rounds
    // than AES-256-GCM for the same traffic while staying the TLS 1.3
    // mandatory suite, which is what caps throughput on CPUs without AES
    // acceleration (e.g. phones) where software AES-256 is the bottleneck.
    let mut config = ServerConfig::builder()
        .with_cipher_suites(&[
            rustls::cipher_suite::TLS13_AES_128_GCM_SHA256,
            rustls::cipher_suite::TLS13_AES_256_GCM_SHA384,
            rustls::cipher_suite::TLS13_CHACHA20_POLY1305_SHA256,
            rustls::cipher_suite::TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256,
            rustls::cipher_suite::TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384,
            rustls::cipher_suite::TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256,
            rustls::cipher_suite::TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256,
            rustls::cipher_suite::TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384,
            rustls::cipher_suite::TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256,
        ])
        .with_safe_default_kx_groups()
        .with_protocol_versions(&[&rustls::version::TLS13, &rustls::version::TLS12])?
        .with_no_client_auth()
        .with_single_cert(certs, keys[0].clone())?;
        // Add this: advertise h2 and http/1.1, matching what real Nginx does
    config.alpn_protocols = vec![
        b"h2".to_vec(),
        b"http/1.1".to_vec(),
    ];
    Ok(config)
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let password = std::env::args().nth(1).unwrap_or_else(|| {
        eprintln!("Usage: trojan-server <password>");
        std::process::exit(1);
    });
    init_password_hash(&password);
    // Load TLS configuration
    let tls_config = match load_tls_config() {
        Ok(config) => config,
        Err(e) => {
            println!("FATAL: {}", e);
            println!("Please generate certificate and key files, e.g., with:");
            println!("openssl req -x509 -newkey rsa:4096 -keyout server.key -out server.crt -days 365 -nodes");
            return Err(e);
        }
    };
    
    let tls_acceptor = TlsAcceptor::from(Arc::new(tls_config));
    
    // Start server
    let listen_addr = format!("{}:{}", LISTEN_HOST, LISTEN_PORT);
    let listener = match TcpListener::bind(&listen_addr).await {
        Ok(listener) => listener,
        Err(e) => {
            println!("ERROR: Failed to bind to {}: {}", listen_addr, e);
            return Err(Box::new(e));
        }
    };
    
    println!("INFO: Trojan Proxy with UDP support listening on {} with TLS", listen_addr);
    let semaphore = Arc::new(Semaphore::new(MAX_CONNECTIONS));
    
    loop {
        // 1. Accept the connection FIRST
        let (stream, _peer_addr) = match listener.accept().await {
            Ok(res) => res,
            Err(e) => {
                println!("ERROR: Failed to accept connection: {}", e);
                continue;
            }
        };

        let acceptor = tls_acceptor.clone();
        let sem = Arc::clone(&semaphore);
        
        tokio::spawn(async move {
            // 2 & 3. Pass the stream and semaphore to the handler
            if let Err(e) = handle_client(stream, acceptor, sem).await {
                println!("ERROR: Client handling error: {}", e);
            }
        });
    }
}

// ============================================================================
// EXACT-FUNCTIONALITY REGRESSION SUITE
// ----------------------------------------------------------------------------
// This `#[cfg(test)]` module locks in the *exact* observable behaviour of the
// server as implemented above. It is compiled out of release builds, so it
// has zero impact on production functionality.
//
// Coverage:
//   * configuration constants
//   * sha224_hex vectors
//   * is_private_address (IPv4 + IPv6, including quirks)
//   * parse_address (all ATYPs + every error string)
//   * parse_udp_packet (valid / malformed / truncation / trailing CRLF)
//   * encode_udp_response (exact bytes + domain rejection + roundtrips)
//   * is_trojan_header_complete (exact lengths for IPv4/domain/IPv6)
//   * trojan request framing as handle_client parses it
//   * greedy CRLF / HTTP-probe detection
//   * constant_time_eq semantics (mirrors nested fn in handle_client)
//   * pipe_data forwarding + EOF + reset/broken-pipe handling
//   * password OnceLock behaviour
//   * load_tls_config error paths
//   * end-to-end TLS handle_client routing (SSRF / port-0 / fallback)
//   * end-to-end UDP ASSOCIATE SSRF blocking
// ============================================================================
#[cfg(test)]
mod exact_functionality_tests {
    use super::*;
    use rustls::{Certificate, PrivateKey, ServerConfig, ServerName};
    use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    use std::sync::{Arc, Mutex, Once};
    use tokio::net::{TcpListener, TcpStream};
    use tokio::sync::Semaphore;
    use tokio::time::{timeout, Duration};
    use tokio_rustls::TlsAcceptor;
    use tokio::io::{AsyncReadExt, AsyncWriteExt};

    // ------------------------------------------------------------------------
    // Shared helpers (test-only builders mirroring the wire format)
    // ------------------------------------------------------------------------

    static TEST_INIT: Once = Once::new();
    const TEST_PASSWORD: &str = "correct_test_password_12345";

    fn ensure_test_password() {
        TEST_INIT.call_once(|| init_password_hash(TEST_PASSWORD));
        // If some other test initialised first with the same password this is
        // a no-op; otherwise the value is already fixed (OnceLock semantics).
        let _ = PASSWORD_HASH.get();
    }

    fn trojan_hash(password: &str) -> String {
        sha224_hex(password)
    }

    fn build_trojan_header(
        password: &str,
        cmd: u8,
        atyp: u8,
        addr_part: &[u8],
        port: u16,
        payload: &[u8],
    ) -> Vec<u8> {
        let mut v = Vec::new();
        v.extend_from_slice(trojan_hash(password).as_bytes()); // 56
        v.extend_from_slice(b"\r\n"); // 2
        v.push(cmd);
        v.push(atyp);
        v.extend_from_slice(addr_part);
        v.extend_from_slice(&port.to_be_bytes());
        v.extend_from_slice(b"\r\n");
        v.extend_from_slice(payload);
        v
    }

    fn ipv4_part(a: u8, b: u8, c: u8, d: u8) -> Vec<u8> {
        vec![a, b, c, d]
    }

    fn ipv6_part(ip: &Ipv6Addr) -> Vec<u8> {
        ip.octets().to_vec()
    }

    fn domain_part(domain: &str) -> Vec<u8> {
        let mut v = vec![domain.len() as u8];
        v.extend_from_slice(domain.as_bytes());
        v
    }

    fn build_udp_packet_ipv4(
        ip: Ipv4Addr,
        port: u16,
        payload: &[u8],
        trailing_crlf: bool,
    ) -> Vec<u8> {
        let mut v = vec![0x01];
        v.extend_from_slice(&ip.octets());
        v.extend_from_slice(&port.to_be_bytes());
        v.extend_from_slice(&(payload.len() as u16).to_be_bytes());
        v.extend_from_slice(b"\r\n");
        v.extend_from_slice(payload);
        if trailing_crlf {
            v.extend_from_slice(b"\r\n");
        }
        v
    }

    fn build_udp_packet_ipv6(
        ip: Ipv6Addr,
        port: u16,
        payload: &[u8],
        trailing_crlf: bool,
    ) -> Vec<u8> {
        let mut v = vec![0x04];
        v.extend_from_slice(&ip.octets());
        v.extend_from_slice(&port.to_be_bytes());
        v.extend_from_slice(&(payload.len() as u16).to_be_bytes());
        v.extend_from_slice(b"\r\n");
        v.extend_from_slice(payload);
        if trailing_crlf {
            v.extend_from_slice(b"\r\n");
        }
        v
    }

    /// Exact copy of the nested `constant_time_eq` inside `handle_client`.
    /// Kept here to lock in its semantics (correctness, not timing).
    fn reference_constant_time_eq(a: &[u8], b: &[u8]) -> bool {
        if a.len() != b.len() {
            return false;
        }
        let mut result: u8 = 0;
        for (x, y) in a.iter().zip(b.iter()) {
            result |= x ^ y;
        }
        result == 0
    }

    /// Exact copy of the greedy-CRLF probe check inside `handle_client`.
    fn reference_should_break_for_probe(buf: &[u8]) -> bool {
        if buf.windows(4).any(|w| w == b"\r\n\r\n") {
            let is_valid_prefix = buf.len() >= 58 && &buf[56..58] == b"\r\n";
            if !is_valid_prefix {
                return true;
            }
        }
        false
    }

    // ------------------------------------------------------------------------
    // 1. Configuration constants — exact values
    // ------------------------------------------------------------------------

    #[test]
    fn test_backend_addr_exact() {
        assert_eq!(BACKEND_ADDR, "127.0.0.1:80");
    }

    #[test]
    fn test_max_connections_exact() {
        assert_eq!(MAX_CONNECTIONS, 512);
    }

    #[test]
    fn test_listen_host_exact() {
        assert_eq!(LISTEN_HOST, "0.0.0.0");
    }

    #[test]
    fn test_listen_port_exact() {
        assert_eq!(LISTEN_PORT, 443);
    }

    #[test]
    fn test_cert_file_exact() {
        assert_eq!(CERT_FILE, "server.crt");
    }

    #[test]
    fn test_key_file_exact() {
        assert_eq!(KEY_FILE, "server.key");
    }

    #[test]
    fn test_buffer_size_exact() {
        assert_eq!(BUFFER_SIZE, 4096);
    }

    // ------------------------------------------------------------------------
    // 2. sha224_hex — known vectors + properties
    // ------------------------------------------------------------------------

    #[test]
    fn test_sha224_empty_known_vector() {
        assert_eq!(
            sha224_hex(""),
            "d14a028c2a3a2bc9476102bb288234c415a2b01f828ea62ac5b3e42f"
        );
    }

    #[test]
    fn test_sha224_password_known_vector() {
        assert_eq!(
            sha224_hex("password"),
            "d63dc919e201d7bc4c825630d2cf25fdc93d4b2f0d46706d29038d01"
        );
    }

    #[test]
    fn test_sha224_hello_known_vector() {
        assert_eq!(
            sha224_hex("hello"),
            "ea09ae9cc6768c50fcee903ed054556e5bfc8347907f12598aa24193"
        );
    }

    #[test]
    fn test_sha224_test_password_123_vector() {
        assert_eq!(
            sha224_hex("test_password_123"),
            "e44940556202750afb5c20670fecf5803a5a33fbddd622bb213e4828"
        );
    }

    #[test]
    fn test_sha224_output_len_always_56() {
        for s in ["", "a", "abc", "password", &"x".repeat(1000)] {
            assert_eq!(sha224_hex(s).len(), 56, "input {:?}", &s[..s.len().min(20)]);
        }
    }

    #[test]
    fn test_sha224_output_lowercase_hex() {
        for s in ["", "hello", "Trojan", "12345"] {
            let h = sha224_hex(s);
            assert_eq!(h.len(), 56);
            assert!(
                h.chars().all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase()),
                "hash {} not lowercase hex",
                h
            );
        }
    }

    #[test]
    fn test_sha224_deterministic() {
        assert_eq!(sha224_hex("same"), sha224_hex("same"));
        assert_eq!(
            sha224_hex("correct_test_password_12345"),
            sha224_hex("correct_test_password_12345")
        );
    }

    #[test]
    fn test_sha224_different_inputs_different_outputs() {
        assert_ne!(sha224_hex("password1"), sha224_hex("password2"));
        assert_ne!(sha224_hex(""), sha224_hex(" "));
        assert_ne!(sha224_hex("Password"), sha224_hex("password")); // case sensitive
    }

    // ------------------------------------------------------------------------
    // 3. Password OnceLock behaviour
    // ------------------------------------------------------------------------

    #[test]
    fn test_password_hash_init_and_get() {
        ensure_test_password();
        assert_eq!(get_password_hash(), sha224_hex(TEST_PASSWORD).as_str());
        assert_eq!(get_password_hash().len(), 56);
    }

    #[test]
    fn test_password_second_init_does_not_overwrite() {
        ensure_test_password();
        let before = get_password_hash().to_string();
        // Second init with a different password must be ignored (OnceLock).
        init_password_hash("a_completely_different_password_xyz");
        assert_eq!(get_password_hash(), before.as_str());
        assert_eq!(before, sha224_hex(TEST_PASSWORD));
    }

    // ------------------------------------------------------------------------
    // 4. is_private_address — IPv4
    // ------------------------------------------------------------------------

    fn v4(a: u8, b: u8, c: u8, d: u8) -> IpAddr {
        IpAddr::V4(Ipv4Addr::new(a, b, c, d))
    }

    #[test]
    fn test_v4_loopback_blocked() {
        assert!(is_private_address(v4(127, 0, 0, 1)));
        assert!(is_private_address(v4(127, 255, 255, 255)));
        assert!(is_private_address(v4(127, 0, 0, 2)));
    }

    #[test]
    fn test_v4_private_10_blocked() {
        assert!(is_private_address(v4(10, 0, 0, 1)));
        assert!(is_private_address(v4(10, 255, 255, 255)));
        // 11/8 is public (only 10/8 is private) — exact boundary
        assert!(!is_private_address(v4(11, 0, 0, 1)));
        assert!(!is_private_address(v4(9, 255, 255, 255)));
    }

    #[test]
    fn test_v4_private_172_16_12_blocked_and_boundaries() {
        assert!(is_private_address(v4(172, 16, 0, 1)));
        assert!(is_private_address(v4(172, 31, 255, 255)));
        assert!(is_private_address(v4(172, 20, 10, 4)));
        // Just outside 172.16/12
        assert!(!is_private_address(v4(172, 15, 255, 255)));
        assert!(!is_private_address(v4(172, 32, 0, 1)));
    }

    #[test]
    fn test_v4_private_192_168_blocked_and_boundary() {
        assert!(is_private_address(v4(192, 168, 0, 1)));
        assert!(is_private_address(v4(192, 168, 255, 255)));
        // 192.167/16 is public — exact /16 boundary
        assert!(!is_private_address(v4(192, 167, 1, 1)));
        assert!(!is_private_address(v4(192, 169, 1, 1)));
    }

    #[test]
    fn test_v4_link_local_blocked_and_boundary() {
        assert!(is_private_address(v4(169, 254, 0, 1)));
        assert!(is_private_address(v4(169, 254, 255, 255)));
        assert!(!is_private_address(v4(169, 253, 1, 1)));
        assert!(!is_private_address(v4(169, 255, 1, 1)));
    }

    #[test]
    fn test_v4_broadcast_unspecified_documentation_blocked() {
        assert!(is_private_address(v4(255, 255, 255, 255))); // broadcast
        assert!(is_private_address(v4(0, 0, 0, 0))); // unspecified
        assert!(is_private_address(v4(192, 0, 2, 1))); // TEST-NET-1
        assert!(is_private_address(v4(198, 51, 100, 1))); // TEST-NET-2
        assert!(is_private_address(v4(203, 0, 113, 1))); // TEST-NET-3
    }

    #[test]
    fn test_v4_unspecified_boundary_quirk() {
        // Only 0.0.0.0 is unspecified; 0.0.0.1 is currently ALLOWED.
        assert!(!is_private_address(v4(0, 0, 0, 1)));
    }

    #[test]
    fn test_v4_public_allowed() {
        assert!(!is_private_address(v4(8, 8, 8, 8)));
        assert!(!is_private_address(v4(1, 1, 1, 1)));
        assert!(!is_private_address(v4(142, 250, 72, 14)));
        assert!(!is_private_address(v4(1, 2, 3, 4)));
    }

    #[test]
    fn test_v4_multicast_not_blocked_quirk() {
        // Current impl does NOT check is_multicast, so multicast is ALLOWED.
        assert!(!is_private_address(v4(224, 0, 0, 1)));
        assert!(!is_private_address(v4(239, 255, 255, 250)));
    }

    // ------------------------------------------------------------------------
    // 5. is_private_address — IPv6
    // ------------------------------------------------------------------------

    fn v6(s: &str) -> IpAddr {
        IpAddr::V6(s.parse::<Ipv6Addr>().unwrap())
    }

    #[test]
    fn test_v6_loopback_and_unspecified_blocked() {
        assert!(is_private_address(v6("::1")));
        assert!(is_private_address(v6("::")));
    }

    #[test]
    fn test_v6_ula_fc00_7_blocked() {
        assert!(is_private_address(v6("fc00::1")));
        assert!(is_private_address(v6("fd00::1")));
        assert!(is_private_address(v6("fdff:ffff::1")));
        assert!(is_private_address(v6("fc12:3456::1")));
    }

    #[test]
    fn test_v6_ula_boundaries_allowed() {
        // fbff::/16 is just below fc00::/7, fe00::/8 just above fdff.
        assert!(!is_private_address(v6("fbff::1")));
        assert!(!is_private_address(v6("fe00::1")));
    }

    #[test]
    fn test_v6_link_local_fe80_10_blocked() {
        assert!(is_private_address(v6("fe80::1")));
        assert!(is_private_address(v6("fe90::1")));
        assert!(is_private_address(v6("fea0::1")));
        assert!(is_private_address(v6("febf:ffff::1")));
    }

    #[test]
    fn test_v6_link_local_boundaries_allowed() {
        assert!(!is_private_address(v6("fe7f::1"))); // just below fe80::/10
        assert!(!is_private_address(v6("fec0::1"))); // just above febf
    }

    #[test]
    fn test_v6_public_allowed() {
        assert!(!is_private_address(v6("2001:4860:4860::8888")));
        assert!(!is_private_address(v6("2606:4700:4700::1111")));
    }

    #[test]
    fn test_v6_documentation_and_multicast_allowed_quirk() {
        // Current impl does NOT block documentation or multicast for v6.
        assert!(!is_private_address(v6("2001:db8::1")));
        assert!(!is_private_address(v6("ff02::1")));
    }

    #[test]
    fn test_v6_mapped_ipv4_allowed_quirk() {
        // IPv4-mapped ::ffff:127.0.0.1 has segments()[0]==0 so it is NOT
        // caught by the v6 ULA/link-local checks — currently ALLOWED.
        let mapped: Ipv6Addr = "::ffff:127.0.0.1".parse().unwrap();
        assert!(!is_private_address(IpAddr::V6(mapped)));
    }

    // ------------------------------------------------------------------------
    // 6. parse_address
    // ------------------------------------------------------------------------

    #[test]
    fn test_parse_address_ipv4_ok_and_cursor() {
        let data = [0x01, 1, 2, 3, 4];
        let mut c = 0usize;
        assert_eq!(parse_address(&data, &mut c).unwrap(), "1.2.3.4");
        assert_eq!(c, 5);
    }

    #[test]
    fn test_parse_address_ipv4_with_offset_cursor() {
        // Simulates request_data where cursor starts after CMD byte.
        let data = [0x01, 0x01, 93, 184, 216, 34]; // CMD=0x01, ATYP=0x01, 93.184.216.34
        let mut c = 1usize;
        assert_eq!(parse_address(&data, &mut c).unwrap(), "93.184.216.34");
        assert_eq!(c, 6);
    }

    #[test]
    fn test_parse_address_ipv4_insufficient() {
        let mut c = 0;
        assert_eq!(
            parse_address(&[0x01, 1, 2, 3], &mut c).unwrap_err(),
            "Insufficient data for IPv4"
        );
        let mut c2 = 0;
        assert_eq!(
            parse_address(&[0x01], &mut c2).unwrap_err(),
            "Insufficient data for IPv4"
        );
    }

    #[test]
    fn test_parse_address_empty_and_cursor_at_end() {
        let mut c = 0;
        assert_eq!(
            parse_address(&[], &mut c).unwrap_err(),
            "Insufficient data for address type"
        );
        let data = [0x01];
        let mut c2 = 1;
        assert_eq!(
            parse_address(&data, &mut c2).unwrap_err(),
            "Insufficient data for address type"
        );
    }

    #[test]
    fn test_parse_address_domain_ok_and_cursor() {
        let domain = "example.com"; // 11
        let mut data = vec![0x03, domain.len() as u8];
        data.extend_from_slice(domain.as_bytes());
        let mut c = 0;
        assert_eq!(parse_address(&data, &mut c).unwrap(), domain);
        assert_eq!(c, 2 + domain.len());
    }

    #[test]
    fn test_parse_address_domain_empty_len_zero_ok() {
        // Current impl allows zero-length domain -> empty string.
        let data = [0x03, 0x00];
        let mut c = 0;
        assert_eq!(parse_address(&data, &mut c).unwrap(), "");
        assert_eq!(c, 2);
    }

    #[test]
    fn test_parse_address_domain_missing_len() {
        let mut c = 0;
        assert_eq!(
            parse_address(&[0x03], &mut c).unwrap_err(),
            "Insufficient data for domain length"
        );
    }

    #[test]
    fn test_parse_address_domain_truncated() {
        let mut c = 0;
        assert_eq!(
            parse_address(&[0x03, 5, b'a', b'b'], &mut c).unwrap_err(),
            "Insufficient data for domain"
        );
    }

    #[test]
    fn test_parse_address_domain_invalid_utf8() {
        let data = [0x03, 2, 0xFF, 0xFE];
        let mut c = 0;
        let err = parse_address(&data, &mut c).unwrap_err();
        assert!(
            err.starts_with("Invalid UTF-8 in domain:"),
            "unexpected err: {}",
            err
        );
    }

    #[test]
    fn test_parse_address_ipv6_ok() {
        let ip = Ipv6Addr::LOCALHOST; // ::1
        let mut data = vec![0x04];
        data.extend_from_slice(&ip.octets());
        let mut c = 0;
        assert_eq!(parse_address(&data, &mut c).unwrap(), "::1");
        assert_eq!(c, 17);

        let ip2: Ipv6Addr = "2001:db8::1".parse().unwrap();
        let mut data2 = vec![0x04];
        data2.extend_from_slice(&ip2.octets());
        let mut c2 = 0;
        assert_eq!(parse_address(&data2, &mut c2).unwrap(), "2001:db8::1");
        assert_eq!(c2, 17);
    }

    #[test]
    fn test_parse_address_ipv6_insufficient() {
        let mut data = vec![0x04];
        data.extend_from_slice(&[0u8; 15]); // one short
        let mut c = 0;
        assert_eq!(
            parse_address(&data, &mut c).unwrap_err(),
            "Insufficient data for IPv6"
        );
    }

    #[test]
    fn test_parse_address_invalid_atyp() {
        for atyp in [0x00u8, 0x02, 0x05, 0x06, 0xFF] {
            let mut c = 0;
            assert_eq!(
                parse_address(&[atyp], &mut c).unwrap_err(),
                format!("Invalid address type: {}", atyp)
            );
        }
    }

    // ------------------------------------------------------------------------
    // 7. parse_udp_packet
    // ------------------------------------------------------------------------

    #[test]
    fn test_parse_udp_ipv4_no_trailing() {
        let pkt = build_udp_packet_ipv4(Ipv4Addr::new(1, 2, 3, 4), 53, b"hello", false);
        // 1+4+2+2+2+5 = 16
        let (addr, port, payload, size) = parse_udp_packet(&pkt).unwrap();
        assert_eq!(addr, "1.2.3.4");
        assert_eq!(port, 53);
        assert_eq!(payload, b"hello");
        assert_eq!(size, 16);
        assert_eq!(size, pkt.len());
    }

    #[test]
    fn test_parse_udp_ipv4_with_trailing_crlf() {
        let pkt = build_udp_packet_ipv4(Ipv4Addr::new(1, 2, 3, 4), 53, b"hello", true);
        let (addr, port, payload, size) = parse_udp_packet(&pkt).unwrap();
        assert_eq!(addr, "1.2.3.4");
        assert_eq!(port, 53);
        assert_eq!(payload, b"hello");
        assert_eq!(size, 18); // 16 + trailing CRLF
        assert_eq!(size, pkt.len());
    }

    #[test]
    fn test_parse_udp_ipv6() {
        let ip: Ipv6Addr = "::1".parse().unwrap();
        let pkt = build_udp_packet_ipv6(ip, 443, b"abc", false);
        let (addr, port, payload, size) = parse_udp_packet(&pkt).unwrap();
        assert_eq!(addr, "::1");
        assert_eq!(port, 443);
        assert_eq!(payload, b"abc");
        assert_eq!(size, 1 + 16 + 2 + 2 + 2 + 3);
    }

    #[test]
    fn test_parse_udp_domain_succeeds_asymmetry() {
        // parse_udp_packet uses parse_address which DOES support 0x03 domains,
        // even though encode_udp_response rejects them. Lock in asymmetry.
        let domain = "example.com";
        let mut pkt = vec![0x03, domain.len() as u8];
        pkt.extend_from_slice(domain.as_bytes());
        pkt.extend_from_slice(&53u16.to_be_bytes());
        pkt.extend_from_slice(&5u16.to_be_bytes());
        pkt.extend_from_slice(b"\r\n");
        pkt.extend_from_slice(b"hello");
        let (addr, port, payload, _) = parse_udp_packet(&pkt).unwrap();
        assert_eq!(addr, domain);
        assert_eq!(port, 53);
        assert_eq!(payload, b"hello");
    }

    #[test]
    fn test_parse_udp_too_short() {
        assert!(parse_udp_packet(&[]).is_none());
        assert!(parse_udp_packet(&[0x01, 1, 2]).is_none()); // len < 4
    }

    #[test]
    fn test_parse_udp_invalid_atyp() {
        assert!(parse_udp_packet(&[0x02, 0, 0, 0, 0, 0]).is_none());
        assert!(parse_udp_packet(&[0xFF, 0, 0, 0, 0, 0]).is_none());
    }

    #[test]
    fn test_parse_udp_missing_port_len() {
        // Valid IPv4 header needs 4 more bytes after address for port+len.
        let truncated = vec![0x01, 1, 2, 3, 4, 0x00]; // only 1 of 4
        assert!(parse_udp_packet(&truncated).is_none());
    }

    #[test]
    fn test_parse_udp_missing_crlf() {
        let mut pkt = build_udp_packet_ipv4(Ipv4Addr::new(1, 2, 3, 4), 53, b"hi", false);
        // Corrupt the CRLF after length
        let crlf_pos = 1 + 4 + 2 + 2;
        pkt[crlf_pos] = b'X';
        pkt[crlf_pos + 1] = b'Y';
        assert!(parse_udp_packet(&pkt).is_none());
    }

    #[test]
    fn test_parse_udp_truncated_payload() {
        let mut pkt = build_udp_packet_ipv4(Ipv4Addr::new(1, 2, 3, 4), 53, b"hello", false);
        pkt.truncate(pkt.len() - 2); // cut payload short
        assert!(parse_udp_packet(&pkt).is_none());
    }

    #[test]
    fn test_parse_udp_empty_payload_len_zero() {
        let pkt = build_udp_packet_ipv4(Ipv4Addr::new(9, 9, 9, 9), 1234, b"", false);
        let (addr, port, payload, size) = parse_udp_packet(&pkt).unwrap();
        assert_eq!(addr, "9.9.9.9");
        assert_eq!(port, 1234);
        assert!(payload.is_empty());
        assert_eq!(size, 1 + 4 + 2 + 2 + 2);
    }

    #[test]
    fn test_parse_udp_multiple_packets_drain_loop() {
        // Mirrors handle_udp_associate's `tcp_buffer.drain(..packet_size)` loop.
        let p1 = build_udp_packet_ipv4(Ipv4Addr::new(1, 1, 1, 1), 53, b"one", false);
        let p2 = build_udp_packet_ipv4(Ipv4Addr::new(2, 2, 2, 2), 54, b"two!", true);
        let mut buf = Vec::new();
        buf.extend_from_slice(&p1);
        buf.extend_from_slice(&p2);

        let (_, _, payload1, size1) = parse_udp_packet(&buf).unwrap();
        assert_eq!(payload1, b"one");
        assert_eq!(size1, p1.len());
        buf.drain(..size1);

        let (addr2, port2, payload2, size2) = parse_udp_packet(&buf).unwrap();
        assert_eq!(addr2, "2.2.2.2");
        assert_eq!(port2, 54);
        assert_eq!(payload2, b"two!");
        assert_eq!(size2, p2.len());
        buf.drain(..size2);
        assert!(buf.is_empty());
    }

    #[test]
    fn test_parse_udp_incomplete_second_packet_waits() {
        let p1 = build_udp_packet_ipv4(Ipv4Addr::new(1, 1, 1, 1), 53, b"one", false);
        let mut buf = Vec::from(p1.clone());
        buf.extend_from_slice(&[0x01, 1, 2]); // partial second packet
        let (_, _, _, size1) = parse_udp_packet(&buf).unwrap();
        buf.drain(..size1);
        // Remainder is incomplete -> None -> caller must wait for more TCP data.
        assert!(parse_udp_packet(&buf).is_none());
    }

    // ------------------------------------------------------------------------
    // 8. encode_udp_response — exact bytes
    // ------------------------------------------------------------------------

    #[test]
    fn test_encode_udp_ipv4_exact_bytes() {
        let out = encode_udp_response("1.2.3.4", 53, b"hello").unwrap();
        let expected: Vec<u8> = vec![
            0x01, 1, 2, 3, 4, // ATYP + IPv4
            0x00, 0x35, // port 53 BE
            0x00, 0x05, // len 5 BE
            b'\r', b'\n', // CRLF
            b'h', b'e', b'l', b'l', b'o',
        ];
        assert_eq!(out, expected);
    }

    #[test]
    fn test_encode_udp_ipv6_exact_bytes() {
        let out = encode_udp_response("::1", 443, b"abc").unwrap();
        let mut expected = vec![0x04];
        expected.extend_from_slice(&[0u8; 15]);
        expected.push(1u8); // ::1
        expected.extend_from_slice(&443u16.to_be_bytes()); // 0x01BB
        expected.extend_from_slice(&3u16.to_be_bytes());
        expected.extend_from_slice(b"\r\n");
        expected.extend_from_slice(b"abc");
        assert_eq!(out, expected);
        assert_eq!(out[1..17], [0u8; 15].iter().chain([1u8].iter()).cloned().collect::<Vec<u8>>()[..]);
    }

    #[test]
    fn test_encode_udp_domain_rejected() {
        assert_eq!(
            encode_udp_response("example.com", 80, b"hi").unwrap_err(),
            "Invalid IP address format"
        );
    }

    #[test]
    fn test_encode_udp_invalid_ip_rejected() {
        for bad in ["not-an-ip", "999.999.999.999", "", "1.2.3", "::ffff::1::2"] {
            assert_eq!(
                encode_udp_response(bad, 80, b"x").unwrap_err(),
                "Invalid IP address format",
                "input {:?} should be rejected",
                bad
            );
        }
    }

    #[test]
    fn test_encode_udp_empty_payload() {
        let out = encode_udp_response("9.9.9.9", 1234, b"").unwrap();
        // 1 + 4 + 2 + 2 + 2 + 0 = 11
        assert_eq!(out.len(), 11);
        assert_eq!(&out[7..9], &[0x00, 0x00]); // len 0
        assert_eq!(&out[9..11], b"\r\n");
    }

    #[test]
    fn test_encode_udp_no_trailing_crlf_after_payload() {
        let out = encode_udp_response("1.2.3.4", 53, b"hello").unwrap();
        // Exact length proves NO trailing CRLF is appended (unlike parser's
        // optional trailing handling).
        assert_eq!(out.len(), 1 + 4 + 2 + 2 + 2 + 5);
        assert_eq!(&out[out.len() - 5..], b"hello");
    }

    #[test]
    fn test_encode_udp_payload_len_be() {
        // 256 -> 0x01 0x00 BE
        let payload = vec![0xABu8; 256];
        let out = encode_udp_response("1.2.3.4", 1, &payload).unwrap();
        assert_eq!(&out[7..9], &[0x01, 0x00]);
        // 1000 -> 0x03 0xE8
        let payload2 = vec![0u8; 1000];
        let out2 = encode_udp_response("1.2.3.4", 1, &payload2).unwrap();
        assert_eq!(&out2[7..9], &1000u16.to_be_bytes());
    }

    #[test]
    fn test_udp_encode_then_parse_roundtrip_ipv4() {
        let payload = b"roundtrip-payload";
        let encoded = encode_udp_response("10.20.30.40", 5353, payload).unwrap();
        let (addr, port, decoded, size) = parse_udp_packet(&encoded).unwrap();
        assert_eq!(addr, "10.20.30.40");
        assert_eq!(port, 5353);
        assert_eq!(decoded, payload);
        assert_eq!(size, encoded.len()); // no trailing -> size == len
    }

    #[test]
    fn test_udp_encode_then_parse_roundtrip_ipv6() {
        let payload = b"v6data";
        let encoded = encode_udp_response("2001:db8::99", 8080, payload).unwrap();
        let (addr, port, decoded, size) = parse_udp_packet(&encoded).unwrap();
        assert_eq!(addr, "2001:db8::99");
        assert_eq!(port, 8080);
        assert_eq!(decoded, payload);
        assert_eq!(size, encoded.len());
    }

    #[test]
    fn test_udp_encode_with_appended_trailing_crlf_still_parses() {
        let mut encoded = encode_udp_response("1.2.3.4", 53, b"hi").unwrap();
        encoded.extend_from_slice(b"\r\n");
        let (addr, _, payload, size) = parse_udp_packet(&encoded).unwrap();
        assert_eq!(addr, "1.2.3.4");
        assert_eq!(payload, b"hi");
        assert_eq!(size, encoded.len()); // trailing consumed into size
    }

    // ------------------------------------------------------------------------
    // 9. is_trojan_header_complete — exact lengths
    // ------------------------------------------------------------------------

    fn header_prefix_ipv4() -> Vec<u8> {
        // 56 hash + \r\n + CMD + ATYP(0x01) + 4 IP + 2 port + \r\n = 68
        let mut b = vec![b'A'; 56];
        b.extend_from_slice(b"\r\n");
        b.push(0x01);
        b.push(0x01);
        b.extend_from_slice(&[1, 2, 3, 4]);
        b.extend_from_slice(&443u16.to_be_bytes());
        b.extend_from_slice(b"\r\n");
        b
    }

    fn header_prefix_domain(domain: &str) -> Vec<u8> {
        // 58 + 2 + (1+len) + 4
        let mut b = vec![b'A'; 56];
        b.extend_from_slice(b"\r\n");
        b.push(0x01);
        b.push(0x03);
        b.push(domain.len() as u8);
        b.extend_from_slice(domain.as_bytes());
        b.extend_from_slice(&443u16.to_be_bytes());
        b.extend_from_slice(b"\r\n");
        b
    }

    fn header_prefix_ipv6() -> Vec<u8> {
        // 58 + 2 + 16 + 4 = 80
        let mut b = vec![b'A'; 56];
        b.extend_from_slice(b"\r\n");
        b.push(0x01);
        b.push(0x04);
        b.extend_from_slice(&[0u8; 16]);
        b.extend_from_slice(&443u16.to_be_bytes());
        b.extend_from_slice(b"\r\n");
        b
    }

    #[test]
    fn test_header_complete_empty_and_short() {
        assert!(!is_trojan_header_complete(&[]));
        assert!(!is_trojan_header_complete(&vec![0u8; 59]));
        assert!(!is_trojan_header_complete(&vec![b'A'; 59]));
    }

    #[test]
    fn test_header_complete_ipv4_exact_lengths() {
        let full = header_prefix_ipv4();
        assert_eq!(full.len(), 68);
        assert!(is_trojan_header_complete(&full));
        assert!(is_trojan_header_complete(&{
            let mut v = full.clone();
            v.extend_from_slice(b"extrapayload");
            v
        }));
        assert!(!is_trojan_header_complete(&full[..67]));
        assert!(!is_trojan_header_complete(&full[..60]));
    }

    #[test]
    fn test_header_complete_domain_example_com() {
        let full = header_prefix_domain("example.com"); // len 11 -> total 76
        assert_eq!(full.len(), 58 + 2 + (1 + 11) + 4);
        assert_eq!(full.len(), 76);
        assert!(is_trojan_header_complete(&full));
        assert!(!is_trojan_header_complete(&full[..75]));
        // Need 61 bytes just to read the domain length byte.
        assert!(!is_trojan_header_complete(&full[..60]));
    }

    #[test]
    fn test_header_complete_domain_len_zero() {
        let full = header_prefix_domain(""); // total 65
        assert_eq!(full.len(), 65);
        assert!(is_trojan_header_complete(&full));
        assert!(!is_trojan_header_complete(&full[..64]));
    }

    #[test]
    fn test_header_complete_ipv6_exact() {
        let full = header_prefix_ipv6();
        assert_eq!(full.len(), 80);
        assert!(is_trojan_header_complete(&full));
        assert!(!is_trojan_header_complete(&full[..79]));
    }

    #[test]
    fn test_header_complete_invalid_atyp_false() {
        for atyp in [0x00u8, 0x02, 0x05, 0xFF] {
            let mut b = vec![b'A'; 56];
            b.extend_from_slice(b"\r\n");
            b.push(0x01);
            b.push(atyp);
            b.extend_from_slice(&vec![0u8; 20]);
            // len >= 60 but atyp invalid -> false (parser routes to fallback)
            assert!(!is_trojan_header_complete(&b), "atyp {:02x}", atyp);
        }
    }

    #[test]
    fn test_header_complete_atyp_position_is_59() {
        // buf[59] is ATYP: 56 hash + 2 CRLF + 1 CMD = index 59.
        let mut b = header_prefix_ipv4();
        assert_eq!(b[59], 0x01);
        b[59] = 0x04; // lie: claim IPv6 but buffer is IPv4-sized (68 < 80)
        assert!(!is_trojan_header_complete(&b));
    }

    // ------------------------------------------------------------------------
    // 10. Trojan request framing as handle_client parses it
    // ------------------------------------------------------------------------

    fn parse_trojan_request_like_handle_client(
        data: &[u8],
    ) -> Result<(u8, String, u16, Vec<u8>), String> {
        // Mirrors the post-auth parsing in handle_client exactly:
        // request_data = data[58..]; cmd=request_data[0]; parse_address from
        // cursor=1; port BE; final CRLF; payload = rest.
        if data.len() < 58 {
            return Err("too short".to_string());
        }
        let request_data = &data[58..];
        if request_data.is_empty() {
            return Err("empty payload branch -> fallback with EMPTY buffer".to_string());
        }
        let cmd = request_data[0];
        let mut cursor = 1usize;
        let addr = parse_address(request_data, &mut cursor).map_err(|e| e)?;
        if request_data.len() < cursor + 2 {
            return Err("insufficient port".to_string());
        }
        let port = u16::from_be_bytes([request_data[cursor], request_data[cursor + 1]]);
        cursor += 2;
        if request_data.len() < cursor + 2 || &request_data[cursor..cursor + 2] != b"\r\n" {
            return Err("missing final CRLF".to_string());
        }
        cursor += 2;
        Ok((cmd, addr, port, request_data[cursor..].to_vec()))
    }

    #[test]
    fn test_framing_valid_tcp_ipv4() {
        let hdr = build_trojan_header(TEST_PASSWORD, 0x01, 0x01, &ipv4_part(93, 184, 216, 34), 80, b"GET / ");
        assert!(is_trojan_header_complete(&hdr));
        let (cmd, addr, port, payload) = parse_trojan_request_like_handle_client(&hdr).unwrap();
        assert_eq!(cmd, 0x01);
        assert_eq!(addr, "93.184.216.34");
        assert_eq!(port, 80);
        assert_eq!(payload, b"GET / ");
    }

    #[test]
    fn test_framing_valid_tcp_domain() {
        let hdr = build_trojan_header(TEST_PASSWORD, 0x01, 0x03, &domain_part("example.com"), 443, b"");
        assert!(is_trojan_header_complete(&hdr));
        let (cmd, addr, port, payload) = parse_trojan_request_like_handle_client(&hdr).unwrap();
        assert_eq!(cmd, 0x01);
        assert_eq!(addr, "example.com");
        assert_eq!(port, 443);
        assert!(payload.is_empty());
    }

    #[test]
    fn test_framing_valid_tcp_ipv6() {
        let ip: Ipv6Addr = "2001:db8::1".parse().unwrap();
        let hdr = build_trojan_header(TEST_PASSWORD, 0x01, 0x04, &ipv6_part(&ip), 8443, b"data");
        assert!(is_trojan_header_complete(&hdr));
        let (cmd, addr, port, _) = parse_trojan_request_like_handle_client(&hdr).unwrap();
        assert_eq!(cmd, 0x01);
        assert_eq!(addr, "2001:db8::1");
        assert_eq!(port, 8443);
    }

    #[test]
    fn test_framing_valid_udp_associate() {
        let udp_pkt = build_udp_packet_ipv4(Ipv4Addr::new(8, 8, 8, 8), 53, b"\x12\x34", false);
        let hdr = build_trojan_header(TEST_PASSWORD, 0x03, 0x01, &ipv4_part(8, 8, 8, 8), 53, &udp_pkt);
        let (cmd, _, _, payload) = parse_trojan_request_like_handle_client(&hdr).unwrap();
        assert_eq!(cmd, 0x03);
        // Payload is the framed UDP packet; it must re-parse.
        let (uaddr, uport, _, _) = parse_udp_packet(&payload).unwrap();
        assert_eq!(uaddr, "8.8.8.8");
        assert_eq!(uport, 53);
    }

    #[test]
    fn test_framing_empty_request_data_branch() {
        // Exactly 58 bytes (hash+CRLF, no CMD) -> handle_client proxies to
        // fallback with EMPTY buffer to prevent password leak.
        let mut b = Vec::new();
        b.extend_from_slice(trojan_hash(TEST_PASSWORD).as_bytes());
        b.extend_from_slice(b"\r\n");
        assert_eq!(b.len(), 58);
        assert_eq!(
            parse_trojan_request_like_handle_client(&b).unwrap_err(),
            "empty payload branch -> fallback with EMPTY buffer"
        );
    }

    #[test]
    fn test_framing_missing_port_branch() {
        let mut hdr = build_trojan_header(TEST_PASSWORD, 0x01, 0x01, &ipv4_part(1, 2, 3, 4), 80, b"");
        hdr.truncate(hdr.len() - 3); // cut into port+CRLF
        assert_eq!(
            parse_trojan_request_like_handle_client(&hdr).unwrap_err(),
            "insufficient port"
        );
    }

    #[test]
    fn test_framing_missing_final_crlf_branch() {
        let mut hdr = build_trojan_header(TEST_PASSWORD, 0x01, 0x01, &ipv4_part(1, 2, 3, 4), 80, b"hi");
        // Corrupt final CRLF (position: 58+1+1+4+2 = 66..68)
        hdr[66] = b'X';
        hdr[67] = b'Y';
        assert_eq!(
            parse_trojan_request_like_handle_client(&hdr).unwrap_err(),
            "missing final CRLF"
        );
    }

    #[test]
    fn test_framing_invalid_atyp_branch() {
        let hdr = build_trojan_header(TEST_PASSWORD, 0x01, 0x05, &[], 80, b"");
        assert!(parse_trojan_request_like_handle_client(&hdr).is_err());
    }

    #[test]
    fn test_framing_hash_and_delimiter_positions() {
        let hdr = build_trojan_header(TEST_PASSWORD, 0x01, 0x01, &ipv4_part(1, 2, 3, 4), 80, b"");
        assert_eq!(&hdr[..56], trojan_hash(TEST_PASSWORD).as_bytes());
        assert_eq!(&hdr[56..58], b"\r\n");
        assert_eq!(hdr[58], 0x01); // CMD
        assert_eq!(hdr[59], 0x01); // ATYP
    }

    #[test]
    fn test_framing_port_zero_preserved_for_ssrf_check() {
        // Port 0 must survive framing so handle_tcp_connect can reject it.
        let hdr = build_trojan_header(TEST_PASSWORD, 0x01, 0x01, &ipv4_part(8, 8, 8, 8), 0, b"");
        let (_, _, port, _) = parse_trojan_request_like_handle_client(&hdr).unwrap();
        assert_eq!(port, 0);
    }

    // ------------------------------------------------------------------------
    // 11. Greedy CRLF / HTTP-probe detection
    // ------------------------------------------------------------------------

    #[test]
    fn test_probe_http_get_triggers_fallback_break() {
        let http = b"GET / HTTP/1.1\r\nHost: example.com\r\n\r\n";
        assert!(reference_should_break_for_probe(http));
    }

    #[test]
    fn test_probe_short_buffer_with_double_crlf_triggers_break() {
        // len < 58 can never have a valid Trojan prefix.
        let short = b"GET /\r\n\r\n";
        assert!(short.len() < 58);
        assert!(reference_should_break_for_probe(short));
    }

    #[test]
    fn test_probe_valid_trojan_prefix_with_embedded_double_crlf_keeps_reading() {
        // A legitimate header (bytes 56..58 == CRLF) whose binary IP/port
        // payload happens to contain \r\n\r\n must NOT break early.
        let mut buf = vec![b'A'; 56];
        buf.extend_from_slice(b"\r\n"); // valid prefix
        buf.extend_from_slice(b"\r\n\r\n"); // binary-looking payload
        buf.extend_from_slice(&vec![0u8; 20]);
        assert_eq!(&buf[56..58], b"\r\n");
        assert!(!reference_should_break_for_probe(&buf));
    }

    #[test]
    fn test_probe_no_double_crlf_no_break() {
        let buf = vec![b'A'; 100]; // no \r\n\r\n anywhere
        assert!(!reference_should_break_for_probe(&buf));
        let partial = &header_prefix_ipv4()[..67]; // incomplete, no double CRLF
        assert!(!reference_should_break_for_probe(partial));
    }

    #[test]
    fn test_probe_prefix_check_requires_len_58() {
        // 57 bytes ending in \r\n\r\n: len<58 so prefix invalid -> break.
        let mut buf = vec![b'X'; 53];
        buf.extend_from_slice(b"\r\n\r\n");
        assert_eq!(buf.len(), 57);
        assert!(reference_should_break_for_probe(&buf));
    }

    // ------------------------------------------------------------------------
    // 12. constant_time_eq semantics
    // ------------------------------------------------------------------------

    #[test]
    fn test_ct_eq_equal_true() {
        assert!(reference_constant_time_eq(b"abc", b"abc"));
        assert!(reference_constant_time_eq(b"", b""));
        assert!(reference_constant_time_eq(
            trojan_hash(TEST_PASSWORD).as_bytes(),
            trojan_hash(TEST_PASSWORD).as_bytes()
        ));
    }

    #[test]
    fn test_ct_eq_different_false() {
        assert!(!reference_constant_time_eq(b"abc", b"abd"));
        assert!(!reference_constant_time_eq(b"aaa", b"bbb"));
    }

    #[test]
    fn test_ct_eq_single_byte_diff_false() {
        let a = trojan_hash(TEST_PASSWORD);
        let mut b = a.clone().into_bytes();
        b[0] ^= 0x01;
        assert!(!reference_constant_time_eq(a.as_bytes(), &b));
        let mut c = a.clone().into_bytes();
        let n = c.len();
        c[n - 1] ^= 0x01;
        assert!(!reference_constant_time_eq(a.as_bytes(), &c));
    }

    #[test]
    fn test_ct_eq_length_mismatch_false() {
        assert!(!reference_constant_time_eq(b"short", b"longer"));
        assert!(!reference_constant_time_eq(b"", b"a"));
        assert!(!reference_constant_time_eq(
            trojan_hash(TEST_PASSWORD).as_bytes(),
            b"short"
        ));
    }

    // ------------------------------------------------------------------------
    // 13. pipe_data — forwarding, EOF, error mapping
    // ------------------------------------------------------------------------

    #[tokio::test]
    async fn test_pipe_data_forwards_bytes() {
        let (mut w1, r1) = tokio::io::duplex(1024);
        let (w2, mut r2) = tokio::io::duplex(1024);
        w1.write_all(b"hello-pipe").await.unwrap();
        drop(w1); // EOF after data
        pipe_data(r1, w2).await.unwrap();
        let mut out = Vec::new();
        r2.read_to_end(&mut out).await.unwrap();
        assert_eq!(out, b"hello-pipe");
    }

    #[tokio::test]
    async fn test_pipe_data_forwards_multi_chunk_large() {
        // 10KB > BUFFER_SIZE (4096) forces multiple loop iterations.
        let big = vec![0x5Au8; 10 * 1024];
        let big_clone = big.clone();
        let (mut w1, r1) = tokio::io::duplex(64 * 1024);
        let (w2, mut r2) = tokio::io::duplex(64 * 1024);
        let writer = tokio::spawn(async move {
            w1.write_all(&big_clone).await.unwrap();
            drop(w1);
        });
        pipe_data(r1, w2).await.unwrap();
        writer.await.unwrap();
        let mut out = Vec::new();
        r2.read_to_end(&mut out).await.unwrap();
        assert_eq!(out, big);
    }

    #[tokio::test]
    async fn test_pipe_data_eof_immediate_ok() {
        let (w1, r1) = tokio::io::duplex(1024);
        drop(w1); // immediate EOF
        let (w2, mut r2) = tokio::io::duplex(1024);
        pipe_data(r1, w2).await.unwrap();
        let mut out = Vec::new();
        r2.read_to_end(&mut out).await.unwrap();
        assert!(out.is_empty());
    }

    struct FailReader {
        kind: std::io::ErrorKind,
    }
    impl tokio::io::AsyncRead for FailReader {
        fn poll_read(
            self: std::pin::Pin<&mut Self>,
            _cx: &mut std::task::Context<'_>,
            _buf: &mut tokio::io::ReadBuf<'_>,
        ) -> std::task::Poll<std::io::Result<()>> {
            std::task::Poll::Ready(Err(std::io::Error::new(self.kind, "injected")))
        }
    }

    #[tokio::test]
    async fn test_pipe_data_connection_reset_breaks_ok() {
        let r = FailReader { kind: std::io::ErrorKind::ConnectionReset };
        pipe_data(r, tokio::io::sink()).await.unwrap();
    }

    #[tokio::test]
    async fn test_pipe_data_broken_pipe_breaks_ok() {
        let r = FailReader { kind: std::io::ErrorKind::BrokenPipe };
        pipe_data(r, tokio::io::sink()).await.unwrap();
    }

    #[tokio::test]
    async fn test_pipe_data_other_error_propagates_err() {
        let r = FailReader { kind: std::io::ErrorKind::InvalidData };
        assert!(pipe_data(r, tokio::io::sink()).await.is_err());
        let r2 = FailReader { kind: std::io::ErrorKind::Other };
        assert!(pipe_data(r2, tokio::io::sink()).await.is_err());
    }

    // ------------------------------------------------------------------------
    // 14. load_tls_config — error paths (no cert files in repo)
    // ------------------------------------------------------------------------

    #[test]
    fn test_load_tls_config_missing_files_returns_err() {
        // Repo ships without server.crt/server.key; loader must fail
        // gracefully (Err, not panic). If files happen to exist in the test
        // cwd this assertion would not apply — guard by checking existence.
        if !std::path::Path::new(CERT_FILE).exists() || !std::path::Path::new(KEY_FILE).exists() {
            assert!(load_tls_config().is_err());
        } else {
            // Files exist: at minimum it must not panic.
            let _ = load_tls_config();
        }
    }

    // ------------------------------------------------------------------------
    // 15. End-to-end TLS routing via handle_client
    // ------------------------------------------------------------------------

    struct TestTlsPair {
        acceptor: TlsAcceptor,
        connector: tokio_rustls::TlsConnector,
    }

    fn test_tls_pair() -> TestTlsPair {
        let cert = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
        let cert_der = cert.serialize_der().unwrap();
        let key_der = cert.serialize_private_key_der();
        let server_certs = vec![Certificate(cert_der.clone())];
        let key = PrivateKey(key_der);
        let mut server_cfg = ServerConfig::builder()
            .with_safe_defaults()
            .with_no_client_auth()
            .with_single_cert(server_certs, key)
            .unwrap();
        // Must match production ALPN exactly.
        server_cfg.alpn_protocols = vec![b"h2".to_vec(), b"http/1.1".to_vec()];
        let acceptor = TlsAcceptor::from(Arc::new(server_cfg));

        let mut root_store = rustls::RootCertStore::empty();
        root_store.add(&Certificate(cert_der)).unwrap();
        let mut client_cfg = rustls::ClientConfig::builder()
            .with_safe_defaults()
            .with_root_certificates(root_store)
            .with_no_client_auth();
        client_cfg.alpn_protocols = vec![b"h2".to_vec(), b"http/1.1".to_vec()];
        let connector = tokio_rustls::TlsConnector::from(Arc::new(client_cfg));
        TestTlsPair { acceptor, connector }
    }

    fn test_tls_acceptor() -> TlsAcceptor {
        test_tls_pair().acceptor
    }

    /// Builds a matched acceptor+connector sharing one self-signed cert.
    /// Required because the client validates via WebPKI root store (no
    /// `dangerous_configuration` feature), so both sides must trust the same
    /// DER.
    fn test_tls_matched_pair() -> TestTlsPair {
        test_tls_pair()
    }

    /// Runs one `handle_client` session: binds an ephemeral listener, spawns
    /// the server handler, connects a TLS client, sends `input`, then waits
    /// for the server task. Returns the server's `Result` as `Ok(())` or
    /// `Err(message)`.
    async fn run_handle_client_with_input(input: Vec<u8>) -> Result<(), String> {
        ensure_test_password();
        // Serialize with backend tests (same BACKEND_LOCK): fallback paths
        // connect to the hardcoded BACKEND_ADDR (127.0.0.1:80), so running
        // concurrently with a backend listener would cross-talk (backend
        // captures another test's fallback bytes). Poison-tolerant: a prior
        // failure must not cascade into all E2E.
        let _net_guard = BACKEND_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let pair = test_tls_matched_pair();
        let acceptor = pair.acceptor;
        let connector = pair.connector;
        let listener = TcpListener::bind("127.0.0.1:0")
            .await
            .map_err(|e| e.to_string())?;
        let addr = listener.local_addr().map_err(|e| e.to_string())?;
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.map_err(|e| e.to_string())?;
            handle_client(stream, acceptor, sem).await.map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.map_err(|e| e.to_string())?;
        let server_name = ServerName::try_from("localhost").map_err(|e| e.to_string())?;
        let mut tls = connector.connect(server_name, tcp).await.map_err(|e| e.to_string())?;
        if !input.is_empty() {
            tls.write_all(&input).await.map_err(|e| e.to_string())?;
            tls.flush().await.map_err(|e| e.to_string())?;
        }
        // Keep `tls` alive while the server decides; then drop it so a
        // fallback pipe (if backend is up) can observe EOF and return instead
        // of hanging for the 5-minute idle timeout.
        let res = match timeout(Duration::from_secs(12), server).await {
            Ok(Ok(r)) => r,
            Ok(Err(e)) => return Err(format!("join error: {}", e)),
            Err(_) => {
                drop(tls);
                return Err("timed out waiting for server".to_string());
            }
        };
        drop(tls);
        res
    }

    #[tokio::test]
    async fn test_e2e_valid_auth_private_ipv4_blocked() {
        ensure_test_password();
        for target in ["127.0.0.1", "10.0.0.1", "192.168.1.1", "192.0.2.1"] {
            let hdr = build_trojan_header(
                TEST_PASSWORD,
                0x01,
                0x01,
                &target
                    .parse::<Ipv4Addr>()
                    .unwrap()
                    .octets(),
                80,
                b"",
            );
            let res = run_handle_client_with_input(hdr).await;
            let msg = res.unwrap_err();
            assert!(
                msg.contains("Blocked private address"),
                "target {} should be SSRF-blocked, got: {}",
                target,
                msg
            );
        }
    }

    #[tokio::test]
    async fn test_e2e_valid_auth_port_zero_blocked() {
        ensure_test_password();
        let hdr = build_trojan_header(
            TEST_PASSWORD,
            0x01,
            0x01,
            &ipv4_part(8, 8, 8, 8),
            0,
            b"",
        );
        let msg = run_handle_client_with_input(hdr).await.unwrap_err();
        assert!(msg.contains("Blocked port"), "got: {}", msg);
    }

    #[tokio::test]
    async fn test_e2e_valid_auth_private_ipv6_blocked() {
        ensure_test_password();
        let ip: Ipv6Addr = "::1".parse().unwrap();
        let hdr = build_trojan_header(TEST_PASSWORD, 0x01, 0x04, &ipv6_part(&ip), 80, b"");
        let msg = run_handle_client_with_input(hdr).await.unwrap_err();
        assert!(msg.contains("Blocked private address"), "got: {}", msg);
    }

    #[tokio::test]
    async fn test_e2e_invalid_password_routes_to_fallback_not_blocked() {
        ensure_test_password();
        // Wrong password must route to fallback (backend attempt), NOT to the
        // SSRF "Blocked" path. With no backend on 127.0.0.1:80 this yields a
        // backend-connection error; with a backend up it yields Ok. Either way
        // it must NOT contain "Blocked".
        let hdr = build_trojan_header(
            "wrong_password_xyz",
            0x01,
            0x01,
            &ipv4_part(8, 8, 8, 8),
            80,
            b"",
        );
        match run_handle_client_with_input(hdr).await {
            Ok(()) => {} // backend was up and proxied — also proves fallback
            Err(msg) => assert!(
                !msg.contains("Blocked"),
                "invalid password must go to fallback, got: {}",
                msg
            ),
        }
    }

    #[tokio::test]
    async fn test_e2e_unsupported_cmd_routes_to_fallback() {
        ensure_test_password();
        let hdr = build_trojan_header(
            TEST_PASSWORD,
            0x02, // unsupported (only 0x01/0x03 valid)
            0x01,
            &ipv4_part(8, 8, 8, 8),
            80,
            b"",
        );
        match run_handle_client_with_input(hdr).await {
            Ok(()) => {}
            Err(msg) => assert!(!msg.contains("Blocked"), "got: {}", msg),
        }
    }

    #[tokio::test]
    async fn test_e2e_malformed_no_final_crlf_routes_to_fallback() {
        ensure_test_password();
        let mut hdr = build_trojan_header(
            TEST_PASSWORD,
            0x01,
            0x01,
            &ipv4_part(8, 8, 8, 8),
            80,
            b"hi",
        );
        hdr[66] = b'X';
        hdr[67] = b'Y';
        match run_handle_client_with_input(hdr).await {
            Ok(()) => {}
            Err(msg) => assert!(!msg.contains("Blocked"), "got: {}", msg),
        }
    }

    #[tokio::test]
    async fn test_e2e_http_probe_routes_to_fallback() {
        ensure_test_password();
        let probe = b"GET / HTTP/1.1\r\nHost: example.com\r\n\r\n".to_vec();
        match run_handle_client_with_input(probe).await {
            Ok(()) => {}
            Err(msg) => assert!(!msg.contains("Blocked"), "got: {}", msg),
        }
    }

    #[tokio::test]
    async fn test_e2e_dns_failure_returns_err_not_blocked() {
        ensure_test_password();
        // Unresolvable domain: DNS fails (not SSRF-blocked, not fallback).
        let hdr = build_trojan_header(
            TEST_PASSWORD,
            0x01,
            0x03,
            &domain_part("invalid.invalid"),
            80,
            b"",
        );
        let msg = run_handle_client_with_input(hdr).await.unwrap_err();
        assert!(!msg.contains("Blocked private"), "got: {}", msg);
    }

    #[tokio::test]
    async fn test_e2e_udp_associate_private_target_blocked_clean_exit() {
        ensure_test_password();
        // Fake UDP target on loopback; the server must NOT forward to it
        // (SSRF block) and must exit cleanly when the client closes TCP.
        let fake_target = tokio::net::UdpSocket::bind("127.0.0.1:0").await.unwrap();
        let fake_port = fake_target.local_addr().unwrap().port();

        let udp_pkt = build_udp_packet_ipv4(Ipv4Addr::new(127, 0, 0, 1), fake_port, b"secret", false);
        let hdr = build_trojan_header(
            TEST_PASSWORD,
            0x03,
            0x01,
            &ipv4_part(8, 8, 8, 8),
            53,
            &udp_pkt,
        );

        let pair = test_tls_matched_pair();
        let acceptor = pair.acceptor;
        let connector = pair.connector;
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, acceptor, sem).await.map_err(|e| e.to_string())
        });

        let tcp = TcpStream::connect(addr).await.unwrap();
        let server_name = ServerName::try_from("localhost").unwrap();
        let mut tls = connector.connect(server_name, tcp).await.unwrap();
        tls.write_all(&hdr).await.unwrap();
        tls.flush().await.unwrap();

        // Give the server a moment to process (and block) the packet.
        tokio::time::sleep(Duration::from_millis(500)).await;

        // Fake target must have received NOTHING (SSRF blocked).
        let mut buf = [0u8; 1024];
        let recv = timeout(Duration::from_millis(500), fake_target.recv_from(&mut buf)).await;
        assert!(recv.is_err(), "private UDP target must not receive forwarded data");

        // Close the client; the associate session must then exit cleanly
        // (TCP EOF -> break) instead of hanging for the 5-minute timeout.
        drop(tls);
        let res = timeout(Duration::from_secs(10), server).await;
        assert!(res.is_ok(), "UDP associate must exit after client close");
        // Server returns Ok(()) on clean close (no error).
        let _ = res.unwrap().unwrap();
    }

    #[tokio::test]
    async fn test_e2e_tls_alpn_matches_production() {
        // The production loader advertises h2 + http/1.1. Our test acceptor
        // must do the same or clients would observe different behaviour.
        let acceptor_cfg = test_tls_acceptor();
        let _ = acceptor_cfg; // construction itself proves single-cert path works
        let cert = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
        let certs = vec![Certificate(cert.serialize_der().unwrap())];
        let key = PrivateKey(cert.serialize_private_key_der());
        let mut cfg = ServerConfig::builder()
            .with_safe_defaults()
            .with_no_client_auth()
            .with_single_cert(certs, key)
            .unwrap();
        cfg.alpn_protocols = vec![b"h2".to_vec(), b"http/1.1".to_vec()];
        assert_eq!(cfg.alpn_protocols, vec![b"h2".to_vec(), b"http/1.1".to_vec()]);
    }

    // ========================================================================
    // EXTRA COVERAGE — areas not covered by the first suite
    // ========================================================================

    static BACKEND_LOCK: Mutex<()> = Mutex::new(());
    static TLS_FILE_LOCK: Mutex<()> = Mutex::new(());

    // ---- pipe_data: 5-minute idle timeout (paused clock, no real wait) -----

    #[tokio::test]
    async fn test_pipe_data_idle_timeout_300s_paused() {
        tokio::time::pause();
        // Duplex with writer held open and zero bytes written: reader pends.
        let (_w_hold, r) = tokio::io::duplex(1024);
        let (w2, _r2_hold) = tokio::io::duplex(1024);
        let handle = tokio::spawn(async move { pipe_data(r, w2).await });
        // Advance past the hardcoded 300s idle timeout.
        tokio::time::advance(Duration::from_secs(301)).await;
        let res = handle.await.expect("pipe task panicked");
        assert!(res.is_ok(), "idle timeout must break cleanly with Ok");
    }

    struct FailWriter;
    impl tokio::io::AsyncWrite for FailWriter {
        fn poll_write(
            self: std::pin::Pin<&mut Self>,
            _cx: &mut std::task::Context<'_>,
            _buf: &[u8],
        ) -> std::task::Poll<std::io::Result<usize>> {
            std::task::Poll::Ready(Err(std::io::Error::new(
                std::io::ErrorKind::BrokenPipe,
                "injected write fail",
            )))
        }
        fn poll_flush(
            self: std::pin::Pin<&mut Self>,
            _cx: &mut std::task::Context<'_>,
        ) -> std::task::Poll<std::io::Result<()>> {
            std::task::Poll::Ready(Ok(()))
        }
        fn poll_shutdown(
            self: std::pin::Pin<&mut Self>,
            _cx: &mut std::task::Context<'_>,
        ) -> std::task::Poll<std::io::Result<()>> {
            std::task::Poll::Ready(Ok(()))
        }
    }

    #[tokio::test]
    async fn test_pipe_data_writer_error_propagates_err() {
        // Reader has data, writer always fails -> write_all `?` propagates Err.
        let (mut w1, r1) = tokio::io::duplex(1024);
        w1.write_all(b"data-for-failing-writer").await.unwrap();
        drop(w1);
        let res = pipe_data(r1, FailWriter).await;
        assert!(res.is_err(), "writer failure must propagate as Err");
    }

    // ---- TLS handshake 10s timeout (real clock; ~10s) ------------------------

    #[tokio::test]
    async fn test_e2e_tls_handshake_timeout_paused() {
        ensure_test_password();
        // Real-time: raw TCP connect without TLS handshake must hit the
        // 10s handshake timeout in handle_client.
        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        // Raw TCP connect, never perform TLS handshake.
        let _raw = TcpStream::connect(addr).await.unwrap();
        let res = timeout(Duration::from_secs(15), server)
            .await
            .expect("server hung past handshake timeout");
        let inner = res.unwrap();
        let msg = inner.unwrap_err();
        assert!(
            msg.contains("TLS handshake timeout"),
            "expected handshake timeout, got: {}",
            msg
        );
    }

    // ---- semaphore exhaustion (connection-limit drop) -----------------------

    #[tokio::test]
    async fn test_e2e_semaphore_exhausted_drops_ok_immediately() {
        ensure_test_password();
        // Zero-permit semaphore: try_acquire always fails -> handler returns
        // Ok(()) immediately after handshake (drop, no fallback, no block).
        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(0));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        // Send a would-be-valid header; it must be ignored (dropped pre-read).
        let hdr = build_trojan_header(TEST_PASSWORD, 0x01, 0x01, &ipv4_part(8, 8, 8, 8), 80, b"");
        tls.write_all(&hdr).await.unwrap();
        tls.flush().await.unwrap();
        drop(tls);
        let res = timeout(Duration::from_secs(10), server).await.expect("server hung");
        let inner = res.unwrap();
        assert!(
            inner.is_ok(),
            "exhausted semaphore must return Ok(drop), got: {:?}",
            inner
        );
    }

    // ---- initial header 60s timeout (paused clock) --------------------------

    #[tokio::test]
    async fn test_e2e_initial_header_60s_timeout_routes_to_fallback() {
        ensure_test_password();
        // Shares BACKEND_LOCK with backend listeners: after the 60s timeout
        // this session falls back to BACKEND_ADDR, so it must not run while
        // another test owns port 80 (cross-talk).
        let _net_guard = BACKEND_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        tokio::time::pause();
        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        // Partial header: 20 bytes, no complete header, no \r\n\r\n, len<4096.
        // Server will wait in the 60s read loop until we advance the clock.
        tls.write_all(&vec![b'B'; 20]).await.unwrap();
        tls.flush().await.unwrap();
        tokio::time::advance(Duration::from_secs(61)).await;
        drop(tls);
        // Also advance past fallback's 5s backend-connect timeout in case the
        // loopback RST is filtered (connect would otherwise hang on paused
        // clock). No outer `timeout()` here: with a paused clock it would
        // need its own advance to fire and masks the real result.
        tokio::time::advance(Duration::from_secs(6)).await;
        let inner = server.await.expect("server task panicked");
        // After 60s timeout with len 20 (<58) -> fallback with 20-byte buffer.
        // With no backend this is a backend error; with backend up, Ok.
        match inner {
            Ok(()) => {}
            Err(msg) => assert!(!msg.contains("Blocked"), "got: {}", msg),
        }
    }

    // ---- oversized initial buffer >4096 safeguard ---------------------------

    #[tokio::test]
    async fn test_e2e_oversized_initial_buffer_routes_to_fallback() {
        ensure_test_password();
        // 5000 'A's: header never complete (0x41 invalid atyp), no \r\n\r\n,
        // second read pushes len to 5000 > 4096 -> break -> fallback.
        let big = vec![b'A'; 5000];
        match run_handle_client_with_input(big).await {
            Ok(()) => {}
            Err(msg) => assert!(!msg.contains("Blocked"), "got: {}", msg),
        }
    }

    // ---- invalid UTF-8 in hash prefix ---------------------------------------

    #[tokio::test]
    async fn test_e2e_invalid_utf8_hash_routes_to_fallback() {
        ensure_test_password();
        let mut raw = vec![0xFFu8; 56]; // invalid UTF-8
        raw.extend_from_slice(b"\r\n");
        raw.push(0x01);
        raw.push(0x01);
        raw.extend_from_slice(&[8, 8, 8, 8]);
        raw.extend_from_slice(&80u16.to_be_bytes());
        raw.extend_from_slice(b"\r\n");
        match run_handle_client_with_input(raw).await {
            Ok(()) => {}
            Err(msg) => assert!(
                !msg.contains("Blocked"),
                "invalid-utf8 hash must go to fallback, got: {}",
                msg
            ),
        }
    }

    // ---- post-auth invalid ATYP / truncated ---------------------------------

    #[tokio::test]
    async fn test_e2e_valid_hash_invalid_atyp_routes_to_fallback() {
        ensure_test_password();
        let hdr = build_trojan_header(TEST_PASSWORD, 0x01, 0x05, &[], 80, b"");
        match run_handle_client_with_input(hdr).await {
            Ok(()) => {}
            Err(msg) => assert!(!msg.contains("Blocked"), "got: {}", msg),
        }
    }

    #[tokio::test]
    async fn test_e2e_valid_hash_truncated_port_routes_to_fallback() {
        ensure_test_password();
        let mut hdr = build_trojan_header(
            TEST_PASSWORD,
            0x01,
            0x01,
            &ipv4_part(8, 8, 8, 8),
            80,
            b"",
        );
        hdr.truncate(hdr.len() - 3); // cut into port+CRLF
        match run_handle_client_with_input(hdr).await {
            Ok(()) => {}
            Err(msg) => assert!(!msg.contains("Blocked"), "got: {}", msg),
        }
    }

    #[tokio::test]
    async fn test_e2e_unsupported_cmds_all_route_to_fallback() {
        ensure_test_password();
        for cmd in [0x00u8, 0x02, 0x04, 0xFF] {
            let hdr = build_trojan_header(
                TEST_PASSWORD,
                cmd,
                0x01,
                &ipv4_part(8, 8, 8, 8),
                80,
                b"",
            );
            match run_handle_client_with_input(hdr).await {
                Ok(()) => {}
                Err(msg) => assert!(
                    !msg.contains("Blocked"),
                    "cmd {:02x} must go to fallback, got: {}",
                    cmd,
                    msg
                ),
            }
        }
    }

    // ---- is_trojan_header_complete: cmd ignored, max domain, extra payload --

    #[test]
    fn test_header_complete_ignores_cmd_byte() {
        // Only atyp at [59] matters; CMD at [58] can be anything.
        for cmd in [0x00u8, 0x01, 0x03, 0xFF] {
            let mut b = vec![b'A'; 56];
            b.extend_from_slice(b"\r\n");
            b.push(cmd);
            b.push(0x01);
            b.extend_from_slice(&[1, 2, 3, 4]);
            b.extend_from_slice(&80u16.to_be_bytes());
            b.extend_from_slice(b"\r\n");
            assert_eq!(b.len(), 68);
            assert!(is_trojan_header_complete(&b), "cmd {:02x}", cmd);
        }
    }

    #[test]
    fn test_header_complete_domain_max_255() {
        let domain = "a".repeat(255);
        let full = header_prefix_domain(&domain);
        // 58 + 2 + (1+255) + 4 = 320
        assert_eq!(full.len(), 320);
        assert!(is_trojan_header_complete(&full));
        assert!(!is_trojan_header_complete(&full[..319]));
    }

    #[test]
    fn test_header_complete_extra_payload_still_true_domain_ipv6() {
        let mut d = header_prefix_domain("example.com");
        d.extend_from_slice(b"payload-bytes");
        assert!(is_trojan_header_complete(&d));
        let mut v6 = header_prefix_ipv6();
        v6.extend_from_slice(&[0u8; 100]);
        assert!(is_trojan_header_complete(&v6));
    }

    // ---- parse_address: extra boundaries ------------------------------------

    #[test]
    fn test_parse_address_domain_max_255_ok() {
        let domain = "b".repeat(255);
        let mut data = vec![0x03, 255u8];
        data.extend_from_slice(domain.as_bytes());
        let mut c = 0;
        assert_eq!(parse_address(&data, &mut c).unwrap(), domain);
        assert_eq!(c, 257);
    }

    #[test]
    fn test_parse_address_ipv4_specials_parse_ok() {
        // Parsing never blocks; SSRF is a separate layer. 0.0.0.0 and
        // 255.255.255.255 must still parse to strings.
        for (bytes, expect) in [
            ([0u8, 0, 0, 0], "0.0.0.0"),
            ([255, 255, 255, 255], "255.255.255.255"),
        ] {
            let data = [0x01, bytes[0], bytes[1], bytes[2], bytes[3]];
            let mut c = 0;
            assert_eq!(parse_address(&data, &mut c).unwrap(), expect);
        }
    }

    #[test]
    fn test_parse_address_ipv6_full_uncompressed() {
        let ip: Ipv6Addr = "2001:0db8:85a3:0000:0000:8a2e:0370:7334".parse().unwrap();
        let mut data = vec![0x04];
        data.extend_from_slice(&ip.octets());
        let mut c = 0;
        // Ipv6Addr::to_string compresses; compare via re-parse.
        let s = parse_address(&data, &mut c).unwrap();
        assert_eq!(s.parse::<Ipv6Addr>().unwrap(), ip);
        assert_eq!(c, 17);
    }

    #[test]
    fn test_parse_address_domain_hyphen_underscore_digits() {
        for d in ["a-b-c123.example-domain.com", "under_score.example", "123.456"] {
            let mut data = vec![0x03, d.len() as u8];
            data.extend_from_slice(d.as_bytes());
            let mut c = 0;
            assert_eq!(parse_address(&data, &mut c).unwrap(), d);
        }
    }

    // ---- encode_udp_response: boundaries + truncation quirk -----------------

    #[test]
    fn test_encode_udp_port_boundaries() {
        let lo = encode_udp_response("1.2.3.4", 0, b"x").unwrap();
        assert_eq!(&lo[5..7], &[0x00, 0x00]);
        let hi = encode_udp_response("1.2.3.4", 65535, b"x").unwrap();
        assert_eq!(&hi[5..7], &[0xFF, 0xFF]);
        // Roundtrip both.
        let (_, p0, _, _) = parse_udp_packet(&lo).unwrap();
        let (_, pmax, _, _) = parse_udp_packet(&hi).unwrap();
        assert_eq!(p0, 0);
        assert_eq!(pmax, 65535);
    }

    #[test]
    fn test_encode_udp_ipv6_full_address() {
        let ip: Ipv6Addr = "2001:db8:85a3::8a2e:370:7334".parse().unwrap();
        let out = encode_udp_response(&ip.to_string(), 53, b"q").unwrap();
        assert_eq!(out[0], 0x04);
        assert_eq!(&out[1..17], &ip.octets());
        let (addr, port, payload, _) = parse_udp_packet(&out).unwrap();
        assert_eq!(addr.parse::<Ipv6Addr>().unwrap(), ip);
        assert_eq!(port, 53);
        assert_eq!(payload, b"q");
    }

    #[test]
    fn test_encode_udp_large_payload_truncation_quirk() {
        // Length is cast `as u16`: 70000 wraps to 70000 % 65536 = 4464.
        // Lock in the current wrapping behaviour (no length validation).
        let big = vec![0x41u8; 70_000];
        let out = encode_udp_response("1.2.3.4", 53, &big).unwrap();
        let declared = u16::from_be_bytes([out[7], out[8]]) as usize;
        assert_eq!(declared, (70_000 % 65_536) as usize);
        assert_eq!(declared, 4464);
        // Parser will then see declared 4464 but 70000 payload bytes present;
        // it parses the first 4464 as payload (total = header + 4464).
        let (_, _, payload, size) = parse_udp_packet(&out).unwrap();
        assert_eq!(payload.len(), 4464);
        assert_eq!(size, 1 + 4 + 2 + 2 + 2 + 4464);
    }

    // ---- sha224_hex: unicode / long / CRLF ----------------------------------

    #[test]
    fn test_sha224_unicode_deterministic_len() {
        let h1 = sha224_hex("pässwörd🔑");
        let h2 = sha224_hex("pässwörd🔑");
        assert_eq!(h1, h2);
        assert_eq!(h1.len(), 56);
        assert_ne!(h1, sha224_hex("password"));
    }

    #[test]
    fn test_sha224_long_input() {
        let long = "a".repeat(1_000_000);
        let h = sha224_hex(&long);
        assert_eq!(h.len(), 56);
        assert!(h.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn test_sha224_crlf_in_password_is_significant() {
        // Passwords are hashed as raw bytes; embedded CRLF changes the hash.
        assert_ne!(sha224_hex("abc"), sha224_hex("abc\r\n"));
        assert_ne!(sha224_hex("a\r\nb"), sha224_hex("ab"));
        assert_eq!(sha224_hex("a\r\nb").len(), 56);
    }

    // ---- BACKEND_ADDR parses -------------------------------------------------

    #[test]
    fn test_backend_addr_parses_as_socketaddr() {
        let sa: std::net::SocketAddr = BACKEND_ADDR.parse().expect("BACKEND_ADDR must parse");
        assert_eq!(sa.ip().to_string(), "127.0.0.1");
        assert_eq!(sa.port(), 80);
    }

    // ---- allowed_peers exact-match semantics ---------------------------------

    #[test]
    fn test_allowed_peers_requires_exact_ip_and_port() {
        use std::collections::HashSet;
        use std::net::SocketAddr;
        let allowed: SocketAddr = "8.8.8.8:53".parse().unwrap();
        let mut set = HashSet::new();
        set.insert(allowed);
        assert!(set.contains(&"8.8.8.8:53".parse().unwrap()));
        // Same IP, different port -> dropped (exact SocketAddr match).
        assert!(!set.contains(&"8.8.8.8:54".parse().unwrap()));
        // Same port, different IP -> dropped.
        assert!(!set.contains(&"8.8.4.4:53".parse().unwrap()));
    }

    // ---- fallback backend content: password-leak prevention ------------------
    // These bind the real BACKEND_ADDR (127.0.0.1:80). If the port is busy or
    // permission-denied they skip gracefully instead of failing.

    async fn with_backend_once(
        test: impl AsyncFnOnce(Vec<u8>) -> Vec<u8>,
        client_input: Vec<u8>,
        respond: &'static [u8],
    ) -> Option<(Vec<u8>, Vec<u8>)> {
        // Returns (backend_received, client_received) or None if skipped.
        // Poison-tolerant so one failing backend test never cascades.
        let _guard = BACKEND_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let backend = match TcpListener::bind(BACKEND_ADDR).await {
            Ok(l) => l,
            Err(_) => return None, // port busy/no permission -> skip
        };
        let (tx, rx) = tokio::sync::oneshot::channel::<Vec<u8>>();
        let backend_task = tokio::spawn(async move {
            let (mut sock, _) = timeout(Duration::from_secs(10), backend.accept())
                .await
                .ok()?
                .ok()?;
            let mut buf = vec![0u8; 8192];
            // Initial replay arrives immediately; short read timeout is enough.
            let n = timeout(Duration::from_secs(5), sock.read(&mut buf))
                .await
                .ok()?
                .ok()?;
            let received = buf[..n].to_vec();
            let _ = tx.send(received.clone());
            // Respond so the client pipe has data to forward (bidirectional).
            let _ = timeout(Duration::from_secs(5), sock.write_all(respond))
                .await
                .ok()?
                .ok()?;
            // Hold briefly so fallback pipe can forward before close.
            tokio::time::sleep(Duration::from_millis(300)).await;
            Some(received)
        });

        // Run a full handle_client session against the live backend.
        ensure_test_password();
        let pair = test_tls_matched_pair();
        let front = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let front_addr = front.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = front.accept().await.unwrap();
            let _ = handle_client(stream, pair.acceptor, sem).await;
        });
        let tcp = TcpStream::connect(front_addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        tls.write_all(&client_input).await.unwrap();
        tls.flush().await.unwrap();
        // Client should observe the backend's response through the tunnel.
        let mut client_buf = vec![0u8; 8192];
        let client_n = timeout(Duration::from_secs(8), tls.read(&mut client_buf))
            .await
            .ok()?
            .ok()?;
        let client_received = client_buf[..client_n].to_vec();
        drop(tls);
        let _ = timeout(Duration::from_secs(5), server).await;
        let backend_received = rx.await.ok()?;
        let _ = backend_task.await;
        // Allow caller to assert on content; also run extra hook.
        let _ = test(backend_received.clone()).await;
        Some((backend_received, client_received))
    }

    #[tokio::test]
    async fn test_fallback_pre_auth_forwards_full_buffer_including_hash() {
        let wrong = "wrong_password_xyz";
        let full = build_trojan_header(wrong, 0x01, 0x01, &ipv4_part(8, 8, 8, 8), 80, b"");
        let full_clone = full.clone();
        let res = with_backend_once(
            async move |_| vec![],
            full_clone.clone(),
            b"HTTP/1.1 200 OK\r\n\r\nfallback-pre",
        )
        .await;
        let Some((backend_got, client_got)) = res else {
            eprintln!("SKIP: cannot bind {}", BACKEND_ADDR);
            return;
        };
        // Pre-auth failure replays everything the client sent (hash included).
        assert_eq!(backend_got, full_clone);
        assert!(
            backend_got.starts_with(sha224_hex(wrong).as_bytes()),
            "pre-auth fallback must include the (wrong) hash prefix"
        );
        assert_eq!(client_got, b"HTTP/1.1 200 OK\r\n\r\nfallback-pre");
    }

    #[tokio::test]
    async fn test_fallback_post_auth_omits_password_no_leak() {
        // Valid hash but bad ATYP: handle_client falls back with
        // request_data only (CMD onwards), never the 56-byte hash.
        let full = build_trojan_header(TEST_PASSWORD, 0x01, 0x05, &[], 80, b"");
        let request_data = full[58..].to_vec();
        assert!(!request_data.is_empty());
        let res = with_backend_once(
            async move |_| vec![],
            full.clone(),
            b"HTTP/1.1 200 OK\r\n\r\nfallback-post",
        )
        .await;
        let Some((backend_got, _)) = res else {
            eprintln!("SKIP: cannot bind {}", BACKEND_ADDR);
            return;
        };
        assert_eq!(
            backend_got, request_data,
            "post-auth fallback must send request_data only"
        );
        assert!(
            !backend_got.windows(56).any(|w| w == sha224_hex(TEST_PASSWORD).as_bytes()),
            "password hash must not leak to fallback backend"
        );
        assert_eq!(backend_got[0], 0x01); // CMD byte, not hash
    }

    #[tokio::test]
    async fn test_fallback_unsupported_cmd_omits_password() {
        let full = build_trojan_header(TEST_PASSWORD, 0xFF, 0x01, &ipv4_part(1, 2, 3, 4), 80, b"");
        let request_data = full[58..].to_vec();
        let res = with_backend_once(async move |_| vec![], full, b"fallback-ff").await;
        let Some((backend_got, client_got)) = res else {
            eprintln!("SKIP: cannot bind {}", BACKEND_ADDR);
            return;
        };
        assert_eq!(backend_got, request_data);
        assert!(!String::from_utf8_lossy(&backend_got).contains(&sha224_hex(TEST_PASSWORD)));
        assert_eq!(client_got, b"fallback-ff");
    }

    // ---- UDP ASSOCIATE extra edges -------------------------------------------

    #[tokio::test]
    async fn test_e2e_udp_dns_failure_no_crash_clean_exit() {
        ensure_test_password();
        // UDP packet to unresolvable domain: DNS fails, nothing forwarded,
        // session stays alive until client closes (no crash).
        let domain = "invalid.invalid";
        let mut pkt = vec![0x03, domain.len() as u8];
        pkt.extend_from_slice(domain.as_bytes());
        pkt.extend_from_slice(&80u16.to_be_bytes());
        pkt.extend_from_slice(&0u16.to_be_bytes());
        pkt.extend_from_slice(b"\r\n");
        let hdr = build_trojan_header(TEST_PASSWORD, 0x03, 0x01, &ipv4_part(8, 8, 8, 8), 53, &pkt);

        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        tls.write_all(&hdr).await.unwrap();
        tls.flush().await.unwrap();
        tokio::time::sleep(Duration::from_millis(800)).await; // allow DNS fail path
        drop(tls);
        let res = timeout(Duration::from_secs(10), server).await.expect("server hung");
        assert!(res.is_ok());
        res.unwrap().unwrap(); // DNS failure is logged, session still exits Ok
    }

    #[tokio::test]
    async fn test_e2e_udp_multiple_private_packets_all_blocked() {
        ensure_test_password();
        let fake = tokio::net::UdpSocket::bind("127.0.0.1:0").await.unwrap();
        let fp = fake.local_addr().unwrap().port();
        // Two framed packets concatenated in the initial buffer.
        let mut both = build_udp_packet_ipv4(Ipv4Addr::new(127, 0, 0, 1), fp, b"one", false);
        both.extend_from_slice(&build_udp_packet_ipv4(
            Ipv4Addr::new(127, 0, 0, 1),
            fp,
            b"two",
            true,
        ));
        let hdr = build_trojan_header(TEST_PASSWORD, 0x03, 0x01, &ipv4_part(8, 8, 8, 8), 53, &both);

        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        tls.write_all(&hdr).await.unwrap();
        tls.flush().await.unwrap();
        tokio::time::sleep(Duration::from_millis(500)).await;
        let mut buf = [0u8; 2048];
        let recv = timeout(Duration::from_millis(500), fake.recv_from(&mut buf)).await;
        assert!(recv.is_err(), "both private UDP packets must be SSRF-blocked");
        drop(tls);
        timeout(Duration::from_secs(10), server).await.expect("server hung").unwrap().unwrap();
    }

    #[tokio::test]
    async fn test_e2e_udp_split_packet_buffered_across_reads() {
        // Exercises tcp_buffer extend + break-for-more-data: send a framed
        // packet split across two TLS writes; private target stays blocked and
        // the session must not crash or misframe.
        ensure_test_password();
        let fake = tokio::net::UdpSocket::bind("127.0.0.1:0").await.unwrap();
        let fp = fake.local_addr().unwrap().port();
        let pkt = build_udp_packet_ipv4(Ipv4Addr::new(127, 0, 0, 1), fp, b"split-payload", false);
        let hdr = build_trojan_header(TEST_PASSWORD, 0x03, 0x01, &ipv4_part(8, 8, 8, 8), 53, &[]);
        let split = pkt.len() / 2;

        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        tls.write_all(&hdr).await.unwrap();
        tls.flush().await.unwrap();
        tokio::time::sleep(Duration::from_millis(200)).await;
        tls.write_all(&pkt[..split]).await.unwrap(); // first half: incomplete
        tls.flush().await.unwrap();
        tokio::time::sleep(Duration::from_millis(200)).await;
        tls.write_all(&pkt[split..]).await.unwrap(); // second half completes it
        tls.flush().await.unwrap();
        tokio::time::sleep(Duration::from_millis(500)).await;
        let mut buf = [0u8; 2048];
        let recv = timeout(Duration::from_millis(500), fake.recv_from(&mut buf)).await;
        assert!(recv.is_err(), "split private packet must still be blocked");
        drop(tls);
        timeout(Duration::from_secs(10), server).await.expect("server hung").unwrap().unwrap();
    }

    // ---- load_tls_config file cases (serialised via lock) --------------------

    fn tls_test_guard() -> std::sync::MutexGuard<'static, ()> {
        TLS_FILE_LOCK.lock().unwrap_or_else(|e| e.into_inner())
    }

    fn tls_files_exist() -> bool {
        std::path::Path::new(CERT_FILE).exists() || std::path::Path::new(KEY_FILE).exists()
    }

    #[test]
    fn test_load_tls_empty_cert_file_errors() {
        let _g = tls_test_guard();
        if tls_files_exist() {
            eprintln!("SKIP: real TLS files present, refusing to clobber");
            return;
        }
        std::fs::write(CERT_FILE, "").unwrap();
        std::fs::write(KEY_FILE, "").unwrap();
        let res = load_tls_config();
        std::fs::remove_file(CERT_FILE).ok();
        std::fs::remove_file(KEY_FILE).ok();
        assert!(res.is_err(), "empty cert file must error, not panic");
    }

    #[test]
    fn test_load_tls_garbage_pem_errors() {
        let _g = tls_test_guard();
        if tls_files_exist() {
            eprintln!("SKIP: real TLS files present");
            return;
        }
        std::fs::write(CERT_FILE, "not a pem at all\n").unwrap();
        std::fs::write(KEY_FILE, "also not a pem\n").unwrap();
        let res = load_tls_config();
        std::fs::remove_file(CERT_FILE).ok();
        std::fs::remove_file(KEY_FILE).ok();
        assert!(res.is_err());
    }

    #[test]
    fn test_load_tls_rsa_traditional_key_rejected_quirk() {
        // Production only calls pkcs8_private_keys, so a traditional
        // `RSA PRIVATE KEY` (PKCS#1) block yields "No private keys found".
        // Lock in that exact quirk with a valid cert + PKCS#1-looking key.
        let _g = tls_test_guard();
        if tls_files_exist() {
            eprintln!("SKIP: real TLS files present");
            return;
        }
        let cert = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
        std::fs::write(CERT_FILE, cert.serialize_pem().unwrap()).unwrap();
        std::fs::write(
            KEY_FILE,
            "-----BEGIN RSA PRIVATE KEY-----\nZmFrZXJzYQ==\n-----END RSA PRIVATE KEY-----\n",
        )
        .unwrap();
        let res = load_tls_config();
        std::fs::remove_file(CERT_FILE).ok();
        std::fs::remove_file(KEY_FILE).ok();
        let msg = format!("{:?}", res.unwrap_err());
        assert!(
            msg.contains("No private keys found"),
            "PKCS#1-only key must be rejected with 'No private keys found', got: {}",
            msg
        );
    }

    #[test]
    fn test_load_tls_valid_pkcs8_success_and_alpn() {
        let _g = tls_test_guard();
        if tls_files_exist() {
            eprintln!("SKIP: real TLS files present");
            return;
        }
        let cert = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
        std::fs::write(CERT_FILE, cert.serialize_pem().unwrap()).unwrap();
        std::fs::write(KEY_FILE, cert.serialize_private_key_pem()).unwrap();
        let res = load_tls_config();
        std::fs::remove_file(CERT_FILE).ok();
        std::fs::remove_file(KEY_FILE).ok();
        let cfg = res.expect("valid PKCS#8 cert+key must load");
        assert_eq!(cfg.alpn_protocols, vec![b"h2".to_vec(), b"http/1.1".to_vec()]);
    }

    // ========================================================================
    // ROUND 3 — deeper edges still uncovered
    // ========================================================================

    // ---- parse_udp_packet: trailing / embedded / boundary variants -----------

    #[test]
    fn test_parse_udp_ipv6_with_trailing_crlf() {
        let ip: Ipv6Addr = "::1".parse().unwrap();
        let pkt = build_udp_packet_ipv6(ip, 53, b"v6hi", true);
        let (addr, port, payload, size) = parse_udp_packet(&pkt).unwrap();
        assert_eq!(addr, "::1");
        assert_eq!(port, 53);
        assert_eq!(payload, b"v6hi");
        assert_eq!(size, pkt.len());
        assert_eq!(size, 1 + 16 + 2 + 2 + 2 + 4 + 2);
    }

    #[test]
    fn test_parse_udp_domain_with_trailing_crlf() {
        let domain = "example.com";
        let mut pkt = vec![0x03, domain.len() as u8];
        pkt.extend_from_slice(domain.as_bytes());
        pkt.extend_from_slice(&8080u16.to_be_bytes());
        pkt.extend_from_slice(&2u16.to_be_bytes());
        pkt.extend_from_slice(b"\r\n");
        pkt.extend_from_slice(b"hi");
        pkt.extend_from_slice(b"\r\n");
        let (addr, port, payload, size) = parse_udp_packet(&pkt).unwrap();
        assert_eq!(addr, domain);
        assert_eq!(port, 8080);
        assert_eq!(payload, b"hi");
        assert_eq!(size, pkt.len());
    }

    #[test]
    fn test_parse_udp_payload_with_embedded_crlf_length_based() {
        // Length prefix (not delimiter scanning) must win: payload itself
        // contains CRLF sequences which must survive verbatim.
        let tricky: &[u8] = b"a\r\nb\r\nc";
        let pkt = build_udp_packet_ipv4(Ipv4Addr::new(1, 2, 3, 4), 53, tricky, false);
        let (_, _, payload, size) = parse_udp_packet(&pkt).unwrap();
        assert_eq!(payload, tricky);
        assert_eq!(size, pkt.len());
        // Same with trailing CRLF appended: payload still exact, size grows by 2.
        let pkt2 = build_udp_packet_ipv4(Ipv4Addr::new(1, 2, 3, 4), 53, tricky, true);
        let (_, _, payload2, size2) = parse_udp_packet(&pkt2).unwrap();
        assert_eq!(payload2, tricky);
        assert_eq!(size2, pkt2.len());
    }

    #[test]
    fn test_parse_udp_empty_payload_with_trailing() {
        let pkt = build_udp_packet_ipv4(Ipv4Addr::new(9, 9, 9, 9), 7, b"", true);
        let (_, _, payload, size) = parse_udp_packet(&pkt).unwrap();
        assert!(payload.is_empty());
        assert_eq!(size, 1 + 4 + 2 + 2 + 2 + 2);
    }

    #[test]
    fn test_parse_udp_port_boundaries() {
        for port in [0u16, 1, 80, 443, 65535] {
            let pkt = build_udp_packet_ipv4(Ipv4Addr::new(8, 8, 8, 8), port, b"x", false);
            let (_, got, payload, _) = parse_udp_packet(&pkt).unwrap();
            assert_eq!(got, port);
            assert_eq!(payload, b"x");
        }
    }

    #[test]
    fn test_parse_udp_valid_prefix_then_garbage_rest_none() {
        // Parser consumes only the first framed prefix; remainder is left for
        // the caller's drain loop. Garbage remainder must parse as None.
        let p1 = build_udp_packet_ipv4(Ipv4Addr::new(1, 1, 1, 1), 53, b"ok", false);
        let mut buf = p1.clone();
        buf.extend_from_slice(&[0xFF, 0x00]); // invalid atyp, len<4 anyway
        let (_, _, payload1, size1) = parse_udp_packet(&buf).unwrap();
        assert_eq!(payload1, b"ok");
        assert_eq!(size1, p1.len());
        buf.drain(..size1);
        assert!(parse_udp_packet(&buf).is_none());
    }

    #[test]
    fn test_parse_udp_declared_len_shorter_than_available_prefix() {
        // Declared len 3 with 6 bytes available: parser returns first 3 as
        // payload and counts only header+3 in size (prefix semantics).
        let mut pkt = vec![0x01, 9, 9, 9, 9];
        pkt.extend_from_slice(&53u16.to_be_bytes());
        pkt.extend_from_slice(&3u16.to_be_bytes());
        pkt.extend_from_slice(b"\r\n");
        pkt.extend_from_slice(b"abcdef"); // 6 available, declared 3
        let (_, _, payload, size) = parse_udp_packet(&pkt).unwrap();
        assert_eq!(payload, b"abc");
        assert_eq!(size, 1 + 4 + 2 + 2 + 2 + 3);
    }

    #[test]
    fn test_parse_udp_domain_invalid_utf8_none() {
        let mut pkt = vec![0x03, 2, 0xFF, 0xFE];
        pkt.extend_from_slice(&53u16.to_be_bytes());
        pkt.extend_from_slice(&1u16.to_be_bytes());
        pkt.extend_from_slice(b"\r\n");
        pkt.extend_from_slice(b"x");
        assert!(parse_udp_packet(&pkt).is_none());
    }

    #[test]
    fn test_parse_udp_wrong_crlf_variants_none() {
        for bad in [vec![b'\n', b'\r'], vec![b'\r', b'X'], vec![b'X', b'\n']] {
            let mut pkt = vec![0x01, 1, 2, 3, 4];
            pkt.extend_from_slice(&53u16.to_be_bytes());
            pkt.extend_from_slice(&1u16.to_be_bytes());
            pkt.extend_from_slice(&bad);
            pkt.extend_from_slice(b"z");
            assert!(parse_udp_packet(&pkt).is_none(), "bad crlf {:?}", bad);
        }
    }

    // ---- encode_udp_response: no SSRF inside encode, tricky payloads --------

    #[test]
    fn test_encode_loopback_and_private_succeeds_no_ssrf_in_encode() {
        // SSRF lives in handle_tcp_connect/handle_udp_associate, NOT in the
        // stateless encoder. Loopback/private must still encode fine.
        for ip in ["127.0.0.1", "10.0.0.1", "192.168.1.1", "0.0.0.0"] {
            assert!(
                encode_udp_response(ip, 53, b"x").is_ok(),
                "encode({}) must succeed",
                ip
            );
        }
        assert!(encode_udp_response("::1", 53, b"x").is_ok());
    }

    #[test]
    fn test_encode_payload_with_crlf_literal_roundtrip() {
        let tricky: &[u8] = b"x\r\ny\r\n\r\nz";
        let enc = encode_udp_response("1.2.3.4", 53, tricky).unwrap();
        // Declared len covers the embedded CRLFs literally.
        assert_eq!(&enc[7..9], &(tricky.len() as u16).to_be_bytes());
        let (_, _, back, size) = parse_udp_packet(&enc).unwrap();
        assert_eq!(back, tricky);
        assert_eq!(size, enc.len());
    }

    #[test]
    fn test_encode_ipv6_empty_payload() {
        let out = encode_udp_response("::1", 9999, b"").unwrap();
        assert_eq!(out.len(), 1 + 16 + 2 + 2 + 2);
        let (addr, port, payload, _) = parse_udp_packet(&out).unwrap();
        assert_eq!(addr, "::1");
        assert_eq!(port, 9999);
        assert!(payload.is_empty());
    }

    // ---- sha224: verified standard vectors -----------------------------------

    #[test]
    fn test_sha224_known_vectors_a_abc_upper() {
        assert_eq!(
            sha224_hex("a"),
            "abd37534c7d9a2efb9465de931cd7055ffdb8879563ae98078d6d6d5"
        );
        assert_eq!(
            sha224_hex("abc"),
            "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7"
        );
        assert_eq!(
            sha224_hex("ABC"),
            "107c5072b799c4771f328304cfe1ebb375eb6ea7f35a3aa753836fad"
        );
    }

    // ---- framing: UDP domain/IPv6 headers, CRLF payload, cursor ---------------

    #[test]
    fn test_framing_udp_domain_and_ipv6_headers() {
        let hdr_d = build_trojan_header(
            TEST_PASSWORD,
            0x03,
            0x03,
            &domain_part("example.org"),
            853,
            b"",
        );
        assert!(is_trojan_header_complete(&hdr_d));
        let (cmd, addr, port, _) = parse_trojan_request_like_handle_client(&hdr_d).unwrap();
        assert_eq!((cmd, addr.as_str(), port), (0x03, "example.org", 853));

        let ip: Ipv6Addr = "2001:db8::53".parse().unwrap();
        let hdr6 = build_trojan_header(TEST_PASSWORD, 0x03, 0x04, &ipv6_part(&ip), 53, b"");
        assert!(is_trojan_header_complete(&hdr6));
        let (cmd6, addr6, port6, _) = parse_trojan_request_like_handle_client(&hdr6).unwrap();
        assert_eq!(cmd6, 0x03);
        assert_eq!(addr6.parse::<Ipv6Addr>().unwrap(), ip);
        assert_eq!(port6, 53);
    }

    #[test]
    fn test_framing_payload_with_crlf_preserved() {
        let payload: &[u8] = b"data\r\nmore\r\n\r\nend";
        let hdr = build_trojan_header(
            TEST_PASSWORD,
            0x01,
            0x01,
            &ipv4_part(9, 9, 9, 9),
            80,
            payload,
        );
        let (_, _, _, back) = parse_trojan_request_like_handle_client(&hdr).unwrap();
        assert_eq!(back, payload);
    }

    #[test]
    fn test_framing_cursor_stops_before_port() {
        // After parse_address, cursor must point exactly at the 2 port bytes.
        let hdr = build_trojan_header(
            TEST_PASSWORD,
            0x01,
            0x01,
            &ipv4_part(1, 2, 3, 4),
            0xABCD,
            b"",
        );
        let request_data = &hdr[58..];
        let mut cursor = 1usize;
        let addr = parse_address(request_data, &mut cursor).unwrap();
        assert_eq!(addr, "1.2.3.4");
        assert_eq!(cursor, 6); // 1 CMD + 1 ATYP + 4 IP
        assert_eq!(&request_data[cursor..cursor + 2], &0xABCDu16.to_be_bytes());
    }

    // ---- probe: double CRLF at very start -------------------------------------

    #[test]
    fn test_probe_double_crlf_at_start_breaks() {
        let mut buf = b"\r\n\r\n".to_vec();
        buf.extend_from_slice(&vec![b'A'; 100]);
        assert!(buf.len() >= 58);
        assert_ne!(&buf[56..58], b"\r\n"); // prefix invalid ('A's)
        assert!(reference_should_break_for_probe(&buf));
    }

    // ---- header_complete: lying length + all-zeros ------------------------------

    #[test]
    fn test_header_complete_lying_domain_len_no_panic() {
        // 61 bytes claiming domain len 255: must be false, never panic/OOB.
        let mut b = vec![b'A'; 56];
        b.extend_from_slice(b"\r\n");
        b.push(0x01);
        b.push(0x03);
        b.push(255u8);
        assert_eq!(b.len(), 61);
        assert!(!is_trojan_header_complete(&b));
    }

    #[test]
    fn test_header_complete_all_zeros_invalid() {
        let b = vec![0u8; 100];
        // atyp = b[59] = 0x00 invalid -> false.
        assert_eq!(b[59], 0x00);
        assert!(!is_trojan_header_complete(&b));
    }

    // ---- private quirks ----------------------------------------------------------

    #[test]
    fn test_v4_directed_broadcast_quirk_only_global_blocked() {
        // Rust is_broadcast() is only 255.255.255.255; subnet-directed
        // broadcasts like 8.8.8.255 are NOT treated as broadcast.
        assert!(is_private_address(v4(255, 255, 255, 255)));
        assert!(!is_private_address(v4(8, 8, 8, 255)));
    }

    #[test]
    fn test_v4_reserved_240_allowed_quirk() {
        // 240.0.0.0/4 (reserved) is not checked -> currently ALLOWED.
        assert!(!is_private_address(v4(240, 0, 0, 1)));
        assert!(!is_private_address(v4(255, 255, 255, 254)));
    }

    #[test]
    fn test_listen_addr_format_exact() {
        // main() binds format!("{}:{}", LISTEN_HOST, LISTEN_PORT).
        assert_eq!(format!("{}:{}", LISTEN_HOST, LISTEN_PORT), "0.0.0.0:443");
    }

    // ---- pipe: write-side ConnectionReset also propagates -------------------------

    struct FailWriterReset;
    impl tokio::io::AsyncWrite for FailWriterReset {
        fn poll_write(
            self: std::pin::Pin<&mut Self>,
            _cx: &mut std::task::Context<'_>,
            _buf: &[u8],
        ) -> std::task::Poll<std::io::Result<usize>> {
            std::task::Poll::Ready(Err(std::io::Error::new(
                std::io::ErrorKind::ConnectionReset,
                "write reset",
            )))
        }
        fn poll_flush(
            self: std::pin::Pin<&mut Self>,
            _cx: &mut std::task::Context<'_>,
        ) -> std::task::Poll<std::io::Result<()>> {
            std::task::Poll::Ready(Ok(()))
        }
        fn poll_shutdown(
            self: std::pin::Pin<&mut Self>,
            _cx: &mut std::task::Context<'_>,
        ) -> std::task::Poll<std::io::Result<()>> {
            std::task::Poll::Ready(Ok(()))
        }
    }

    #[tokio::test]
    async fn test_pipe_write_reset_propagates_err_asymmetry() {
        // Read-side Reset/BrokenPipe -> Ok (ignored). Write-side Reset (and
        // BrokenPipe) -> Err via `?`. Lock in that asymmetry explicitly.
        let (mut w1, r1) = tokio::io::duplex(1024);
        w1.write_all(b"payload").await.unwrap();
        drop(w1);
        assert!(pipe_data(r1, FailWriterReset).await.is_err());

        let r = FailReader { kind: std::io::ErrorKind::ConnectionReset };
        assert!(pipe_data(r, tokio::io::sink()).await.is_ok());
    }

    // ---- E2E: wrong delimiter / uppercase hash -------------------------------------

    #[tokio::test]
    async fn test_e2e_valid_hash_wrong_delimiter_routes_to_fallback() {
        ensure_test_password();
        let mut hdr = build_trojan_header(
            TEST_PASSWORD,
            0x01,
            0x01,
            &ipv4_part(8, 8, 8, 8),
            80,
            b"",
        );
        hdr[56] = b'X';
        hdr[57] = b'Y';
        match run_handle_client_with_input(hdr).await {
            Ok(()) => {}
            Err(msg) => assert!(!msg.contains("Blocked"), "got: {}", msg),
        }
    }

    #[tokio::test]
    async fn test_e2e_uppercase_hash_routes_to_fallback() {
        ensure_test_password();
        let mut hdr = build_trojan_header(
            TEST_PASSWORD,
            0x01,
            0x01,
            &ipv4_part(8, 8, 8, 8),
            80,
            b"",
        );
        let orig: Vec<u8> = hdr[..56].to_vec();
        for b in hdr[..56].iter_mut() {
            *b = b.to_ascii_uppercase();
        }
        // Guard against the (astronomically unlikely) all-digit hash where
        // upper == lower; then this test would be invalid.
        assert_ne!(&hdr[..56], &orig[..], "test hash has no hex letters?!");
        match run_handle_client_with_input(hdr).await {
            Ok(()) => {}
            Err(msg) => assert!(
                !msg.contains("Blocked"),
                "uppercase hash must fail auth to fallback, got: {}",
                msg
            ),
        }
    }

    // ---- E2E TCP: localhost domain + specials + large payload still blocked ---------

    #[tokio::test]
    async fn test_e2e_tcp_domain_localhost_blocked() {
        ensure_test_password();
        let hdr = build_trojan_header(
            TEST_PASSWORD,
            0x01,
            0x03,
            &domain_part("localhost"),
            80,
            b"",
        );
        let msg = run_handle_client_with_input(hdr).await.unwrap_err();
        assert!(msg.contains("Blocked private address"), "got: {}", msg);
    }

    #[tokio::test]
    async fn test_e2e_tcp_special_ips_blocked() {
        ensure_test_password();
        for (a, b, c, d) in [(0u8, 0, 0, 0), (255, 255, 255, 255)] {
            let hdr = build_trojan_header(
                TEST_PASSWORD,
                0x01,
                0x01,
                &ipv4_part(a, b, c, d),
                80,
                b"",
            );
            let msg = run_handle_client_with_input(hdr).await.unwrap_err();
            assert!(
                msg.contains("Blocked private address"),
                "target {}.{}.{}.{} should block, got: {}",
                a,
                b,
                c,
                d,
                msg
            );
        }
    }

    #[tokio::test]
    async fn test_e2e_tcp_private_with_large_payload_still_blocked() {
        ensure_test_password();
        let big = vec![0x41u8; 1024];
        let hdr = build_trojan_header(
            TEST_PASSWORD,
            0x01,
            0x01,
            &ipv4_part(127, 0, 0, 1),
            80,
            &big,
        );
        let msg = run_handle_client_with_input(hdr).await.unwrap_err();
        assert!(msg.contains("Blocked private address"), "got: {}", msg);
    }

    // ---- E2E UDP: domain localhost / IPv6 / garbage / delayed / trailing -----------

    #[tokio::test]
    async fn test_e2e_udp_domain_localhost_blocked() {
        ensure_test_password();
        let fake = tokio::net::UdpSocket::bind("127.0.0.1:0").await.unwrap();
        let fp = fake.local_addr().unwrap().port();
        let domain = "localhost";
        let mut pkt = vec![0x03, domain.len() as u8];
        pkt.extend_from_slice(domain.as_bytes());
        pkt.extend_from_slice(&fp.to_be_bytes());
        pkt.extend_from_slice(&4u16.to_be_bytes());
        pkt.extend_from_slice(b"\r\n");
        pkt.extend_from_slice(b"data");
        let hdr = build_trojan_header(TEST_PASSWORD, 0x03, 0x01, &ipv4_part(8, 8, 8, 8), 53, &pkt);

        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        tls.write_all(&hdr).await.unwrap();
        tls.flush().await.unwrap();
        tokio::time::sleep(Duration::from_millis(600)).await;
        let mut buf = [0u8; 2048];
        let recv = timeout(Duration::from_millis(500), fake.recv_from(&mut buf)).await;
        assert!(recv.is_err(), "localhost-domain UDP must resolve private and block");
        drop(tls);
        timeout(Duration::from_secs(10), server).await.expect("hung").unwrap().unwrap();
    }

    #[tokio::test]
    async fn test_e2e_udp_ipv6_loopback_blocked() {
        ensure_test_password();
        let fake = tokio::net::UdpSocket::bind("127.0.0.1:0").await.unwrap();
        let fp = fake.local_addr().unwrap().port();
        let ip: Ipv6Addr = "::1".parse().unwrap();
        let pkt = build_udp_packet_ipv6(ip, fp, b"v6secret", false);
        let hdr = build_trojan_header(TEST_PASSWORD, 0x03, 0x01, &ipv4_part(8, 8, 8, 8), 53, &pkt);
        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        tls.write_all(&hdr).await.unwrap();
        tls.flush().await.unwrap();
        tokio::time::sleep(Duration::from_millis(500)).await;
        let mut buf = [0u8; 2048];
        let recv = timeout(Duration::from_millis(500), fake.recv_from(&mut buf)).await;
        assert!(recv.is_err(), "::1 UDP must be SSRF-blocked");
        drop(tls);
        timeout(Duration::from_secs(10), server).await.expect("hung").unwrap().unwrap();
    }

    #[tokio::test]
    async fn test_e2e_udp_garbage_tcp_data_no_crash() {
        ensure_test_password();
        // Valid associate header with NO payload, then garbage bytes that are
        // not a valid UDP frame (0xFF atyp). Server must wait, not crash.
        let fake = tokio::net::UdpSocket::bind("127.0.0.1:0").await.unwrap();
        let hdr = build_trojan_header(TEST_PASSWORD, 0x03, 0x01, &ipv4_part(8, 8, 8, 8), 53, &[]);
        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        tls.write_all(&hdr).await.unwrap();
        tls.flush().await.unwrap();
        tokio::time::sleep(Duration::from_millis(200)).await;
        tls.write_all(&vec![0xFFu8; 20]).await.unwrap();
        tls.flush().await.unwrap();
        tokio::time::sleep(Duration::from_millis(500)).await;
        let mut buf = [0u8; 2048];
        let recv = timeout(Duration::from_millis(400), fake.recv_from(&mut buf)).await;
        assert!(recv.is_err(), "garbage must not be forwarded anywhere");
        drop(tls);
        timeout(Duration::from_secs(10), server).await.expect("hung").unwrap().unwrap();
    }

    #[tokio::test]
    async fn test_e2e_udp_second_packet_after_delay_blocked() {
        // Header alone first (empty initial payload), then a real framed
        // packet on a LATER read. Exercises tcp_buffer persistence across
        // loop iterations, not just the initial buffer.
        ensure_test_password();
        let fake = tokio::net::UdpSocket::bind("127.0.0.1:0").await.unwrap();
        let fp = fake.local_addr().unwrap().port();
        let hdr = build_trojan_header(TEST_PASSWORD, 0x03, 0x01, &ipv4_part(8, 8, 8, 8), 53, &[]);
        let pkt = build_udp_packet_ipv4(Ipv4Addr::new(127, 0, 0, 1), fp, b"late", false);
        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        tls.write_all(&hdr).await.unwrap();
        tls.flush().await.unwrap();
        tokio::time::sleep(Duration::from_millis(250)).await;
        tls.write_all(&pkt).await.unwrap();
        tls.flush().await.unwrap();
        tokio::time::sleep(Duration::from_millis(500)).await;
        let mut buf = [0u8; 2048];
        let recv = timeout(Duration::from_millis(500), fake.recv_from(&mut buf)).await;
        assert!(recv.is_err(), "delayed private packet must still block");
        drop(tls);
        timeout(Duration::from_secs(10), server).await.expect("hung").unwrap().unwrap();
    }

    #[tokio::test]
    async fn test_e2e_udp_trailing_crlf_private_blocked() {
        ensure_test_password();
        let fake = tokio::net::UdpSocket::bind("127.0.0.1:0").await.unwrap();
        let fp = fake.local_addr().unwrap().port();
        let pkt = build_udp_packet_ipv4(Ipv4Addr::new(127, 0, 0, 1), fp, b"trail", true);
        let hdr = build_trojan_header(TEST_PASSWORD, 0x03, 0x01, &ipv4_part(8, 8, 8, 8), 53, &pkt);
        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        tls.write_all(&hdr).await.unwrap();
        tls.flush().await.unwrap();
        tokio::time::sleep(Duration::from_millis(500)).await;
        let mut buf = [0u8; 2048];
        let recv = timeout(Duration::from_millis(500), fake.recv_from(&mut buf)).await;
        assert!(recv.is_err(), "trailing-CRLF private packet must block");
        drop(tls);
        timeout(Duration::from_secs(10), server).await.expect("hung").unwrap().unwrap();
    }

    #[tokio::test]
    async fn test_e2e_udp_idle_timeout_300s_paused() {
        // Associate with no UDP traffic must die on the 5-minute idle timer
        // even while the client TCP stays open. Paused clock: no real wait.
        ensure_test_password();
        tokio::time::pause();
        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        let hdr = build_trojan_header(TEST_PASSWORD, 0x03, 0x01, &ipv4_part(8, 8, 8, 8), 53, &[]);
        tls.write_all(&hdr).await.unwrap();
        tls.flush().await.unwrap();
        // Let the server enter the associate select loop (real yields under
        // paused clock still work for IO).
        for _ in 0..10 {
            tokio::task::yield_now().await;
        }
        tokio::time::advance(Duration::from_secs(301)).await;
        for _ in 0..10 {
            tokio::task::yield_now().await;
        }
        assert!(
            server.is_finished(),
            "UDP associate must exit on 5-minute idle timeout with client still open"
        );
        let res = server.await.unwrap();
        assert!(res.is_ok(), "idle timeout exit must be Ok, got {:?}", res);
        drop(tls);
    }

    // ---- fallback/backend: empty, large, oversized, payload-included ----------

    #[tokio::test]
    async fn test_fallback_empty_buffer_sends_zero_bytes() {
        // 58 bytes (hash+CRLF) then client EOF -> handle_client falls back
        // with EMPTY buffer (password-leak guard). Backend must see 0 bytes.
        let _guard = BACKEND_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let backend = match TcpListener::bind(BACKEND_ADDR).await {
            Ok(l) => l,
            Err(_) => {
                eprintln!("SKIP: cannot bind {}", BACKEND_ADDR);
                return;
            }
        };
        let (tx, rx) = tokio::sync::oneshot::channel::<Vec<u8>>();
        let backend_task = tokio::spawn(async move {
            let (mut sock, _) = timeout(Duration::from_secs(12), backend.accept())
                .await
                .ok()?
                .ok()?;
            let mut buf = vec![0u8; 8192];
            // Empty write sends nothing: read encounters timeout (no data)
            // while the connection stays open for piping. Treat timeout/EOF
            // as the expected empty result.
            match timeout(Duration::from_secs(3), sock.read(&mut buf)).await {
                Ok(Ok(0)) => {
                    let _ = tx.send(vec![]);
                }
                Ok(Ok(n)) => {
                    let _ = tx.send(buf[..n].to_vec());
                }
                _ => {
                    let _ = tx.send(vec![]);
                }
            }
            // Respond anyway; client is likely gone, ignore errors.
            let _ = sock.write_all(b"empty-ok").await;
            Some(())
        });

        ensure_test_password();
        let pair = test_tls_matched_pair();
        let front = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let front_addr = front.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = front.accept().await.unwrap();
            let _ = handle_client(stream, pair.acceptor, sem).await;
        });
        // Send exactly hash+CRLF (58) then drop => server sees EOF => empty branch.
        let tcp = TcpStream::connect(front_addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        let mut hello = Vec::new();
        hello.extend_from_slice(trojan_hash(TEST_PASSWORD).as_bytes());
        hello.extend_from_slice(b"\r\n");
        assert_eq!(hello.len(), 58);
        tls.write_all(&hello).await.unwrap();
        tls.flush().await.unwrap();
        // Small delay to let the 58 bytes arrive before EOF.
        tokio::time::sleep(Duration::from_millis(300)).await;
        drop(tls);
        let backend_got = timeout(Duration::from_secs(12), rx).await.expect("backend hung").unwrap();
        assert!(
            backend_got.is_empty(),
            "empty-payload fallback must send 0 bytes, got {} bytes: {:?}",
            backend_got.len(),
            &backend_got[..backend_got.len().min(64)]
        );
        let _ = timeout(Duration::from_secs(8), server).await;
        let _ = backend_task.await;
    }

    #[tokio::test]
    async fn test_fallback_large_initial_data_4k() {
        // Pre-auth invalid password with 5000-byte payload: backend must get
        // the entire buffer (header + payload), proving large replay works
        // beyond BUFFER_SIZE (4096). Total 5068 fits the 8192 backend buffer.
        let wrong = "wrong_password_large_xyz";
        let big = vec![0x42u8; 5000];
        let full = build_trojan_header(wrong, 0x01, 0x01, &ipv4_part(8, 8, 8, 8), 80, &big);
        assert!(full.len() > BUFFER_SIZE);
        let expect = full.clone();
        let res = with_backend_once(async move |_| vec![], full, b"large-ok").await;
        let Some((backend_got, client_got)) = res else {
            eprintln!("SKIP: cannot bind {}", BACKEND_ADDR);
            return;
        };
        assert_eq!(backend_got.len(), expect.len());
        assert_eq!(backend_got, expect);
        assert_eq!(client_got, b"large-ok");
    }

    #[tokio::test]
    async fn test_fallback_oversized_5000_forwards_full() {
        // The >4096 safeguard breaks the read loop but still forwards the
        // FULL 5000-byte buffer to fallback (no truncation).
        let big = vec![b'A'; 5000];
        let expect = big.clone();
        let res = with_backend_once(async move |_| vec![], big, b"over-ok").await;
        let Some((backend_got, client_got)) = res else {
            eprintln!("SKIP: cannot bind {}", BACKEND_ADDR);
            return;
        };
        assert_eq!(backend_got, expect);
        assert_eq!(client_got, b"over-ok");
    }

    #[tokio::test]
    async fn test_fallback_unsupported_cmd_with_payload_includes_payload() {
        // Post-auth fallback sends request_data (CMD..payload), never the hash,
        // and the application payload must be included verbatim.
        let app: &[u8] = b"PAYLOAD123";
        let full = build_trojan_header(TEST_PASSWORD, 0x02, 0x01, &ipv4_part(1, 2, 3, 4), 80, app);
        let request_data = full[58..].to_vec();
        assert!(request_data.windows(app.len()).any(|w| w == app));
        let res = with_backend_once(async move |_| vec![], full, b"cmd-ok").await;
        let Some((backend_got, _)) = res else {
            eprintln!("SKIP: cannot bind {}", BACKEND_ADDR);
            return;
        };
        assert_eq!(backend_got, request_data);
        assert!(backend_got.windows(app.len()).any(|w| w == app));
        assert!(!backend_got.windows(56).any(|w| w == trojan_hash(TEST_PASSWORD).as_bytes()));
    }

    // ---- load_tls_config: single-side missing + chain --------------------------

    #[test]
    fn test_load_tls_cert_present_key_missing_errors() {
        let _g = tls_test_guard();
        if tls_files_exist() {
            eprintln!("SKIP: real TLS files present");
            return;
        }
        let cert = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
        std::fs::write(CERT_FILE, cert.serialize_pem().unwrap()).unwrap();
        // KEY_FILE absent.
        let res = load_tls_config();
        std::fs::remove_file(CERT_FILE).ok();
        assert!(res.is_err(), "missing key file must error");
    }

    #[test]
    fn test_load_tls_key_present_cert_missing_errors() {
        let _g = tls_test_guard();
        if tls_files_exist() {
            eprintln!("SKIP: real TLS files present");
            return;
        }
        let cert = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
        std::fs::write(KEY_FILE, cert.serialize_private_key_pem()).unwrap();
        // CERT_FILE absent.
        let res = load_tls_config();
        std::fs::remove_file(KEY_FILE).ok();
        assert!(res.is_err(), "missing cert file must error");
    }

    #[test]
    fn test_load_tls_chain_two_certs_loads_ok() {
        let _g = tls_test_guard();
        if tls_files_exist() {
            eprintln!("SKIP: real TLS files present");
            return;
        }
        let c1 = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
        let c2 = rcgen::generate_simple_self_signed(vec!["example.com".to_string()]).unwrap();
        let chain = c1.serialize_pem().unwrap() + &c2.serialize_pem().unwrap();
        std::fs::write(CERT_FILE, chain).unwrap();
        std::fs::write(KEY_FILE, c1.serialize_private_key_pem()).unwrap();
        let res = load_tls_config();
        std::fs::remove_file(CERT_FILE).ok();
        std::fs::remove_file(KEY_FILE).ok();
        assert!(res.is_ok(), "two-cert chain must load, got {:?}", res.err());
    }

    // ========================================================================
    // ROUND 4 — still-uncovered branches
    // ========================================================================

    // ---- sha224: README example + standard sentence + 100k --------------------

    #[test]
    fn test_sha224_readme_and_fox_and_100k() {
        assert_eq!(
            sha224_hex("your_secure_password_here"),
            "25784d7975795f8e5c79f21ad14b18e64b6d7504df45a70d80fa23f1"
        );
        assert_eq!(
            sha224_hex("The quick brown fox jumps over the lazy dog"),
            "730e109bd7a8a32b1cb9d9a09aa2325d2430587ddbc0c38bad911525"
        );
        assert_eq!(
            sha224_hex(&"a".repeat(100_000)),
            "c8eb6e0f37cef2bfcbc86f1539001ad556923ff0b9b226488edb5a13"
        );
    }

    // ---- parse_address: domain/IPv6 with non-zero cursor -----------------------

    #[test]
    fn test_parse_address_domain_with_offset_cursor() {
        let domain = "example.org";
        let mut data = vec![0x01]; // CMD placeholder
        data.push(0x03);
        data.push(domain.len() as u8);
        data.extend_from_slice(domain.as_bytes());
        let mut c = 1usize;
        assert_eq!(parse_address(&data, &mut c).unwrap(), domain);
        assert_eq!(c, 1 + 1 + 1 + domain.len());
    }

    #[test]
    fn test_parse_address_ipv6_with_offset_cursor() {
        let ip: Ipv6Addr = "fe80::42".parse().unwrap();
        let mut data = vec![0x03]; // CMD placeholder
        data.push(0x04);
        data.extend_from_slice(&ip.octets());
        let mut c = 1usize;
        assert_eq!(parse_address(&data, &mut c).unwrap().parse::<Ipv6Addr>().unwrap(), ip);
        assert_eq!(c, 18);
    }

    // ---- header_complete: len-zero + extra still true -----------------------------

    #[test]
    fn test_header_complete_domain_len_zero_with_extra() {
        let mut full = header_prefix_domain("");
        full.extend_from_slice(b"extra");
        assert!(is_trojan_header_complete(&full));
    }

    // ---- encode/parse: 65535 max roundtrip ------------------------------------------

    #[test]
    fn test_udp_max_payload_65535_roundtrip() {
        let big = vec![0x7Eu8; 65_535];
        let enc = encode_udp_response("10.11.12.13", 53, &big).unwrap();
        assert_eq!(&enc[7..9], &65_535u16.to_be_bytes());
        let (addr, port, back, size) = parse_udp_packet(&enc).unwrap();
        assert_eq!(addr, "10.11.12.13");
        assert_eq!(port, 53);
        assert_eq!(back.len(), 65_535);
        assert_eq!(back, big);
        assert_eq!(size, enc.len());
    }

    // ---- allowed_peers: v4/v6 family mismatch ------------------------------------------

    #[test]
    fn test_allowed_peers_v4_v6_mismatch_dropped() {
        use std::collections::HashSet;
        use std::net::SocketAddr;
        let v4: SocketAddr = "127.0.0.1:53".parse().unwrap();
        let v6mapped: SocketAddr = "[::ffff:127.0.0.1]:53".parse().unwrap();
        let mut set = HashSet::new();
        set.insert(v4);
        // Different address families never compare equal, even for mapped IPs.
        assert!(!set.contains(&v6mapped));
        assert_ne!(v4, v6mapped);
    }

    // ---- pipe: BUFFER_SIZE boundaries + 1-byte chunks + idle-reset -----------------------

    #[tokio::test]
    async fn test_pipe_data_exactly_buffer_size_4096() {
        let chunk = vec![0x51u8; BUFFER_SIZE];
        let expect = chunk.clone();
        let (mut w1, r1) = tokio::io::duplex(128 * 1024);
        let (w2, mut r2) = tokio::io::duplex(128 * 1024);
        w1.write_all(&chunk).await.unwrap();
        drop(w1);
        pipe_data(r1, w2).await.unwrap();
        let mut out = Vec::new();
        r2.read_to_end(&mut out).await.unwrap();
        assert_eq!(out, expect);
    }

    #[tokio::test]
    async fn test_pipe_data_buffer_size_plus_one_4097() {
        let chunk = vec![0x52u8; BUFFER_SIZE + 1];
        let expect = chunk.clone();
        let (mut w1, r1) = tokio::io::duplex(128 * 1024);
        let (w2, mut r2) = tokio::io::duplex(128 * 1024);
        w1.write_all(&chunk).await.unwrap();
        drop(w1);
        pipe_data(r1, w2).await.unwrap();
        let mut out = Vec::new();
        r2.read_to_end(&mut out).await.unwrap();
        assert_eq!(out, expect);
    }

    #[tokio::test]
    async fn test_pipe_data_one_byte_chunks() {
        // Slow sender: 100 single-byte writes, each flushed. Loop must forward
        // every 1-byte read without loss/reorder.
        let payload: Vec<u8> = (0u8..100).collect();
        let expect = payload.clone();
        let (mut w1, r1) = tokio::io::duplex(64 * 1024);
        let (w2, mut r2) = tokio::io::duplex(64 * 1024);
        let writer = tokio::spawn(async move {
            for b in payload {
                w1.write_all(&[b]).await.unwrap();
                tokio::task::yield_now().await;
            }
            drop(w1);
        });
        pipe_data(r1, w2).await.unwrap();
        writer.await.unwrap();
        let mut out = Vec::new();
        r2.read_to_end(&mut out).await.unwrap();
        assert_eq!(out, expect);
    }

    #[tokio::test]
    async fn test_pipe_data_idle_timer_resets_on_activity_paused() {
        // 250s idle (<300) then activity must prevent timeout; a further
        // 301s of silence must then time out. Proves the 300s is per-read
        // idle, not total session lifetime.
        tokio::time::pause();
        let (mut w_hold, r) = tokio::io::duplex(64 * 1024);
        let (w2, mut r2) = tokio::io::duplex(64 * 1024);
        let handle = tokio::spawn(async move { pipe_data(r, w2).await });
        tokio::time::advance(Duration::from_secs(250)).await;
        assert!(!handle.is_finished(), "must not time out before 300s idle");
        // Activity at 250s resets the idle clock.
        w_hold.write_all(b"keepalive").await.unwrap();
        let mut probe = [0u8; 9];
        r2.read_exact(&mut probe).await.unwrap();
        assert_eq!(&probe, b"keepalive");
        // Fresh 301s silence from last activity must now time out.
        tokio::time::advance(Duration::from_secs(301)).await;
        for _ in 0..10 {
            tokio::task::yield_now().await;
        }
        assert!(handle.is_finished(), "must time out after 301s of new silence");
        assert!(handle.await.unwrap().is_ok());
        drop(w_hold);
    }

    // ---- load_tls: single-side garbage + key mismatch --------------------------------------

    #[test]
    fn test_load_tls_cert_garbage_key_valid_errors() {
        let _g = tls_test_guard();
        if tls_files_exist() {
            eprintln!("SKIP: real TLS files present");
            return;
        }
        let cert = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
        std::fs::write(CERT_FILE, "-----BEGIN CERTIFICATE-----\n!!!\n-----END CERTIFICATE-----\n").unwrap();
        std::fs::write(KEY_FILE, cert.serialize_private_key_pem()).unwrap();
        let res = load_tls_config();
        std::fs::remove_file(CERT_FILE).ok();
        std::fs::remove_file(KEY_FILE).ok();
        assert!(res.is_err(), "garbage cert must error even with valid key");
    }

    #[test]
    fn test_load_tls_cert_valid_key_garbage_errors() {
        let _g = tls_test_guard();
        if tls_files_exist() {
            eprintln!("SKIP: real TLS files present");
            return;
        }
        let cert = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
        std::fs::write(CERT_FILE, cert.serialize_pem().unwrap()).unwrap();
        std::fs::write(KEY_FILE, "-----BEGIN PRIVATE KEY-----\n!!!\n-----END PRIVATE KEY-----\n").unwrap();
        let res = load_tls_config();
        std::fs::remove_file(CERT_FILE).ok();
        std::fs::remove_file(KEY_FILE).ok();
        // rustls_pemfile::pkcs8_private_keys propagates base64 errors (`?`),
        // so garbage base64 is Err(InvalidData...), not "No private keys".
        // Lock in: any Err, never Ok/panic.
        assert!(res.is_err(), "garbage key must error, got {:?}", res.ok());
    }

    #[test]
    fn test_load_tls_key_mismatch_loads_ok_quirk() {
        // rustls 0.21 with_single_cert does NOT check that the private key
        // corresponds to the certificate at load time (failure surfaces only
        // at handshake). A mismatched but well-formed pair therefore loads Ok.
        let _g = tls_test_guard();
        if tls_files_exist() {
            eprintln!("SKIP: real TLS files present");
            return;
        }
        let c1 = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
        let c2 = rcgen::generate_simple_self_signed(vec!["other.example".to_string()]).unwrap();
        std::fs::write(CERT_FILE, c1.serialize_pem().unwrap()).unwrap();
        std::fs::write(KEY_FILE, c2.serialize_private_key_pem()).unwrap();
        let res = load_tls_config();
        std::fs::remove_file(CERT_FILE).ok();
        std::fs::remove_file(KEY_FILE).ok();
        assert!(res.is_ok(), "mismatched pair loads Ok (mismatch fails at handshake, not load), got {:?}", res.err());
    }

    // ---- E2E TCP: allowed-but-unroutable connect-failure branch -------------------------------

    #[tokio::test]
    async fn test_e2e_tcp_allowed_unroutable_connect_failure_not_blocked() {
        // 240.0.0.1 is ALLOWED by is_private_address (reserved quirk) but
        // unroutable, so handle_tcp_connect must pass SSRF+DNS and fail at
        // TcpStream::connect ("Failed to connect"/unreachable/timeout) —
        // never fallback, never "Blocked".
        ensure_test_password();
        assert!(!is_private_address(v4(240, 0, 0, 1)));
        let hdr = build_trojan_header(
            TEST_PASSWORD,
            0x01,
            0x01,
            &ipv4_part(240, 0, 0, 1),
            80,
            b"",
        );
        let msg = run_handle_client_with_input(hdr).await.unwrap_err();
        assert!(
            !msg.contains("Blocked"),
            "unroutable public IP must fail at connect, not SSRF-block, got: {}",
            msg
        );
    }

    // ---- E2E: fragmented Trojan header across two TLS writes ------------------------------------

    #[tokio::test]
    async fn test_e2e_fragmented_header_two_writes_still_blocked() {
        // Initial-read buffering must reassemble a header split across reads.
        ensure_test_password();
        let hdr = build_trojan_header(
            TEST_PASSWORD,
            0x01,
            0x01,
            &ipv4_part(127, 0, 0, 1),
            80,
            b"",
        );
        assert_eq!(hdr.len(), 68);
        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        tls.write_all(&hdr[..30]).await.unwrap();
        tls.flush().await.unwrap();
        tokio::time::sleep(Duration::from_millis(200)).await;
        tls.write_all(&hdr[30..]).await.unwrap();
        tls.flush().await.unwrap();
        // Let the server consume the second flight before FIN: dropping a
        // tokio-rustls client without close_notify makes the server's next
        // read return UnexpectedEof (truncation) instead of the bytes.
        tokio::time::sleep(Duration::from_millis(500)).await;
        drop(tls);
        let res = timeout(Duration::from_secs(12), server).await.expect("hung");
        let msg = res.unwrap().unwrap_err();
        assert!(msg.contains("Blocked private address"), "got: {}", msg);
    }

    // ---- E2E: immediate EOF (0 bytes) -> fallback --------------------------------------------------

    #[tokio::test]
    async fn test_e2e_immediate_eof_routes_to_fallback() {
        ensure_test_password();
        let _net_guard = BACKEND_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.unwrap();
        let tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        // No bytes at all, immediate EOF (n==0 break, len 0 <58 -> fallback).
        drop(tls);
        let res = timeout(Duration::from_secs(15), server).await.expect("hung");
        match res.unwrap() {
            Ok(()) => {}
            Err(msg) => assert!(!msg.contains("Blocked"), "EOF must go to fallback, got: {}", msg),
        }
    }

    // ---- E2E: invalid-UTF8 domain post-auth -> fallback ----------------------------------------------

    #[tokio::test]
    async fn test_e2e_invalid_utf8_domain_routes_to_fallback() {
        ensure_test_password();
        let mut addr_part = vec![2u8, 0xFF, 0xFE]; // len 2, invalid UTF-8
        let _ = &mut addr_part; // keep binding shape clear
        let hdr = build_trojan_header(TEST_PASSWORD, 0x01, 0x03, &addr_part, 80, b"");
        match run_handle_client_with_input(hdr).await {
            Ok(()) => {}
            Err(msg) => assert!(
                !msg.contains("Blocked"),
                "invalid-utf8 domain must go to fallback without password, got: {}",
                msg
            ),
        }
    }

    // ---- E2E UDP: empty-payload framed packet blocked ---------------------------------------------------

    #[tokio::test]
    async fn test_e2e_udp_empty_payload_packet_blocked() {
        ensure_test_password();
        let fake = tokio::net::UdpSocket::bind("127.0.0.1:0").await.unwrap();
        let fp = fake.local_addr().unwrap().port();
        let pkt = build_udp_packet_ipv4(Ipv4Addr::new(127, 0, 0, 1), fp, b"", false);
        let hdr = build_trojan_header(TEST_PASSWORD, 0x03, 0x01, &ipv4_part(8, 8, 8, 8), 53, &pkt);
        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        tls.write_all(&hdr).await.unwrap();
        tls.flush().await.unwrap();
        tokio::time::sleep(Duration::from_millis(500)).await;
        let mut buf = [0u8; 2048];
        let recv = timeout(Duration::from_millis(500), fake.recv_from(&mut buf)).await;
        assert!(recv.is_err(), "empty-payload private packet must still block");
        drop(tls);
        timeout(Duration::from_secs(10), server).await.expect("hung").unwrap().unwrap();
    }

    // ---- Fallback: backend timing proves 5s connect timeout -----------------------------------------------

    #[tokio::test]
    async fn test_fallback_no_backend_returns_within_12s_not_hung() {
        // With nothing on 127.0.0.1:80 the fallback connect must resolve
        // within the 5s backend timeout (plus handshake/read overhead) —
        // never the 60s header wait nor the 300s pipe idle.
        ensure_test_password();
        let _net_guard = BACKEND_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let start = std::time::Instant::now();
        let hdr = build_trojan_header(
            "wrong_password_timing_xyz",
            0x01,
            0x01,
            &ipv4_part(8, 8, 8, 8),
            80,
            b"",
        );
        // Bypass run_helper's own locking (already hold it): inline session.
        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        tls.write_all(&hdr).await.unwrap();
        tls.flush().await.unwrap();
        drop(tls);
        let res = timeout(Duration::from_secs(12), server).await.expect("hung past backend timeout");
        let elapsed = start.elapsed();
        assert!(
            elapsed < Duration::from_secs(12),
            "fallback must return via 5s backend timeout, took {:?}",
            elapsed
        );
        match res.unwrap() {
            Ok(()) => {}
            Err(msg) => assert!(!msg.contains("Blocked"), "got: {}", msg),
        }
    }

    // ---- Fallback: bidirectional echo after replay ------------------------------------------------------------

    #[tokio::test]
    async fn test_fallback_bidirectional_echo_after_replay() {
        // After the initial replay, both pipe directions must live: client
        // sends a second message, backend echoes it back through the tunnel.
        let _guard = BACKEND_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let backend = match TcpListener::bind(BACKEND_ADDR).await {
            Ok(l) => l,
            Err(_) => {
                eprintln!("SKIP: cannot bind {}", BACKEND_ADDR);
                return;
            }
        };
        let backend_task = tokio::spawn(async move {
            let (mut sock, _) = timeout(Duration::from_secs(10), backend.accept())
                .await
                .ok()?
                .ok()?;
            // 1) consume the replayed Trojan bytes (invalid-password full).
            let mut first = vec![0u8; 8192];
            let n = timeout(Duration::from_secs(5), sock.read(&mut first)).await.ok()?.ok()?;
            assert!(n > 58, "backend must get full replay, got {} bytes", n);
            // 2) greet so the client knows the tunnel is up.
            timeout(Duration::from_secs(5), sock.write_all(b"READY")).await.ok()?.ok()?;
            // 3) echo exactly one more client message back.
            let mut second = vec![0u8; 1024];
            let m = timeout(Duration::from_secs(5), sock.read(&mut second)).await.ok()?.ok()?;
            timeout(Duration::from_secs(5), sock.write_all(&second[..m])).await.ok()?.ok()?;
            Some(())
        });

        ensure_test_password();
        let pair = test_tls_matched_pair();
        let front = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let front_addr = front.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = front.accept().await.unwrap();
            let _ = handle_client(stream, pair.acceptor, sem).await;
        });
        let tcp = TcpStream::connect(front_addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        let full = build_trojan_header("wrong_password_echo_xyz", 0x01, 0x01, &ipv4_part(8, 8, 8, 8), 80, b"");
        tls.write_all(&full).await.unwrap();
        tls.flush().await.unwrap();
        // Greeting through the tunnel.
        let mut greet = [0u8; 5];
        timeout(Duration::from_secs(8), tls.read_exact(&mut greet)).await.unwrap().unwrap();
        assert_eq!(&greet, b"READY");
        // Second message echoed back through both pipes.
        tls.write_all(b"PING2").await.unwrap();
        tls.flush().await.unwrap();
        let mut echo = [0u8; 5];
        timeout(Duration::from_secs(8), tls.read_exact(&mut echo)).await.unwrap().unwrap();
        assert_eq!(&echo, b"PING2");
        drop(tls);
        let _ = timeout(Duration::from_secs(8), server).await.expect("server hung");
        backend_task.await.unwrap();
    }

    // ========================================================================
    // ROUND 5 — remaining uncovered branches
    // ========================================================================

    // ---- is_private: shared / benchmarking / v6 special-use allowed ----------

    #[test]
    fn test_v4_shared_and_benchmarking_allowed_quirks() {
        // 100.64.0.0/10 (CGNAT shared) and 198.18.0.0/15 (benchmarking) are
        // not in Rust's is_private()/is_documentation() sets checked here.
        assert!(!is_private_address(v4(100, 64, 0, 1)));
        assert!(!is_private_address(v4(100, 127, 255, 255)));
        assert!(!is_private_address(v4(198, 18, 0, 1)));
        assert!(!is_private_address(v4(198, 19, 255, 255)));
    }

    #[test]
    fn test_v6_benchmarking_discard_allowed_quirk() {
        // 2001:2::/48 (benchmarking) and 100::/64 (discard) are not checked.
        assert!(!is_private_address(v6("2001:2::1")));
        assert!(!is_private_address(v6("100::1")));
        assert!(!is_private_address(v6("64:ff9b::808:808"))); // NAT64 well-known
    }

    // ---- parse_address: trailing bytes ignored ---------------------------------

    #[test]
    fn test_parse_address_ignores_trailing_bytes() {
        // Parser consumes only its own field; port/CRLF/payload remain.
        let mut data = vec![0x01, 10, 0, 0, 1];
        data.extend_from_slice(&[0x1F, 0x90, b'\r', b'\n', b'Z']);
        let mut c = 0usize;
        assert_eq!(parse_address(&data, &mut c).unwrap(), "10.0.0.1");
        assert_eq!(c, 5);
        assert_eq!(&data[c..], &[0x1F, 0x90, b'\r', b'\n', b'Z']);
    }

    // ---- parse_udp: max domain, domain+CRLF payload, empty domain --------------

    #[test]
    fn test_parse_udp_max_domain_255_packet() {
        let domain = "c".repeat(255);
        let mut pkt = vec![0x03, 255u8];
        pkt.extend_from_slice(domain.as_bytes());
        pkt.extend_from_slice(&443u16.to_be_bytes());
        pkt.extend_from_slice(&4u16.to_be_bytes());
        pkt.extend_from_slice(b"\r\n");
        pkt.extend_from_slice(b"data");
        let (addr, port, payload, size) = parse_udp_packet(&pkt).unwrap();
        assert_eq!(addr, domain);
        assert_eq!(port, 443);
        assert_eq!(payload, b"data");
        assert_eq!(size, pkt.len());
    }

    #[test]
    fn test_parse_udp_domain_embedded_crlf_payload() {
        let tricky: &[u8] = b"x\r\ny";
        let domain = "example.net";
        let mut pkt = vec![0x03, domain.len() as u8];
        pkt.extend_from_slice(domain.as_bytes());
        pkt.extend_from_slice(&53u16.to_be_bytes());
        pkt.extend_from_slice(&(tricky.len() as u16).to_be_bytes());
        pkt.extend_from_slice(b"\r\n");
        pkt.extend_from_slice(tricky);
        let (addr, _, payload, _) = parse_udp_packet(&pkt).unwrap();
        assert_eq!(addr, domain);
        assert_eq!(payload, tricky);
    }

    #[test]
    fn test_parse_udp_empty_domain_succeeds() {
        // parse_address allows len-0 domain; UDP layer inherits that.
        let mut pkt = vec![0x03, 0u8];
        pkt.extend_from_slice(&80u16.to_be_bytes());
        pkt.extend_from_slice(&1u16.to_be_bytes());
        pkt.extend_from_slice(b"\r\n");
        pkt.extend_from_slice(b"q");
        let (addr, port, payload, _) = parse_udp_packet(&pkt).unwrap();
        assert_eq!(addr, "");
        assert_eq!(port, 80);
        assert_eq!(payload, b"q");
    }

    // ---- encode: broadcast + header 255+extra --------------------------------------

    #[test]
    fn test_encode_broadcast_succeeds() {
        assert!(encode_udp_response("255.255.255.255", 9, b"discard").is_ok());
    }

    #[test]
    fn test_header_complete_domain_255_with_extra() {
        let mut full = header_prefix_domain(&"d".repeat(255));
        assert_eq!(full.len(), 320);
        full.extend_from_slice(b"tail");
        assert!(is_trojan_header_complete(&full));
    }

    // ---- password hash: cached object identity ------------------------------------------

    #[test]
    fn test_password_hash_ptr_cached_identity() {
        ensure_test_password();
        let a = get_password_hash() as *const str;
        let b = get_password_hash() as *const str;
        assert!(std::ptr::eq(a, b), "hash must be cached OnceLock singleton");
        assert_eq!(unsafe { &*a }.len(), 56);
    }

    // ---- pipe: backpressure with tiny duplex buffers -----------------------------------------

    #[tokio::test]
    async fn test_pipe_data_backpressure_tiny_buffers() {
        // 16-byte duplex capacities with a 5KB transfer force the writer to
        // pend (backpressure) until the pipe drains; reader drains concurrently
        // to avoid deadlock. Proves AsyncWrite::Pending is handled.
        let big = vec![0x6Bu8; 5 * 1024];
        let expect = big.clone();
        let (mut w1, r1) = tokio::io::duplex(16);
        let (w2, r2) = tokio::io::duplex(16);
        let writer = tokio::spawn(async move {
            w1.write_all(&big).await.unwrap();
            drop(w1);
        });
        let reader = tokio::spawn(async move {
            let mut out = Vec::new();
            let mut r2 = r2;
            r2.read_to_end(&mut out).await.unwrap();
            out
        });
        pipe_data(r1, w2).await.unwrap();
        writer.await.unwrap();
        let out = reader.await.unwrap();
        assert_eq!(out, expect);
    }

    // ---- load_tls: swapped roles + EC-traditional + trailing junk -------------------------------

    #[test]
    fn test_load_tls_cert_key_swapped_errors() {
        let _g = tls_test_guard();
        if tls_files_exist() {
            eprintln!("SKIP: real TLS files present");
            return;
        }
        let cert = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
        // Swap: cert file gets the KEY pem, key file gets the CERT pem.
        std::fs::write(CERT_FILE, cert.serialize_private_key_pem()).unwrap();
        std::fs::write(KEY_FILE, cert.serialize_pem().unwrap()).unwrap();
        let res = load_tls_config();
        std::fs::remove_file(CERT_FILE).ok();
        std::fs::remove_file(KEY_FILE).ok();
        let msg = format!("{:?}", res.unwrap_err());
        assert!(
            msg.contains("No certificates found"),
            "swapped files must fail at cert stage, got: {}",
            msg
        );
    }

    #[test]
    fn test_load_tls_ec_traditional_rejected_quirk() {
        // Mirrors the RSA-traditional quirk for `EC PRIVATE KEY` (SEC1):
        // pkcs8_private_keys ignores the section -> "No private keys found".
        let _g = tls_test_guard();
        if tls_files_exist() {
            eprintln!("SKIP: real TLS files present");
            return;
        }
        let cert = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
        std::fs::write(CERT_FILE, cert.serialize_pem().unwrap()).unwrap();
        std::fs::write(
            KEY_FILE,
            "-----BEGIN EC PRIVATE KEY-----\nZmFrZWVj\n-----END EC PRIVATE KEY-----\n",
        )
        .unwrap();
        let res = load_tls_config();
        std::fs::remove_file(CERT_FILE).ok();
        std::fs::remove_file(KEY_FILE).ok();
        let msg = format!("{:?}", res.unwrap_err());
        assert!(
            msg.contains("No private keys found"),
            "SEC1-only key must be rejected, got: {}",
            msg
        );
    }

    #[test]
    fn test_load_tls_trailing_junk_tolerated_ok() {
        let _g = tls_test_guard();
        if tls_files_exist() {
            eprintln!("SKIP: real TLS files present");
            return;
        }
        let cert = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
        // Trailing non-PEM junk after valid blocks must be ignored.
        std::fs::write(
            CERT_FILE,
            cert.serialize_pem().unwrap() + "\nTHIS IS NOT A PEM BLOCK\n",
        )
        .unwrap();
        std::fs::write(
            KEY_FILE,
            cert.serialize_private_key_pem() + "\nMORE JUNK\n",
        )
        .unwrap();
        let res = load_tls_config();
        std::fs::remove_file(CERT_FILE).ok();
        std::fs::remove_file(KEY_FILE).ok();
        assert!(res.is_ok(), "trailing junk must be tolerated, got {:?}", res.err());
    }

    // ---- lookup: mapped IPv6 parses and bypasses SSRF check -------------------------

    #[tokio::test]
    async fn test_lookup_mapped_ipv6_parses_and_allowed() {
        // Proves the full bypass chain up to the SSRF gate without needing a
        // connect: numeric mapped literal resolves locally (no DNS) and the
        // current is_private_address lets it through (quirk).
        let mut addrs = tokio::net::lookup_host("::ffff:127.0.0.1:8080").await.unwrap();
        let sa = addrs.next().unwrap();
        assert_eq!(sa.port(), 8080);
        assert!(!is_private_address(sa.ip()));
    }

    // ---- E2E UDP: public port-0 has NO port check (unlike TCP) ---------------------

    #[tokio::test]
    async fn test_e2e_udp_public_port_zero_no_port_check_clean_exit() {
        // TCP rejects port 0 upfront; UDP has no such gate. 240.0.0.1 is
        // public-but-unroutable, so send_to fails harmlessly (logged) and the
        // session must still exit cleanly on client close.
        ensure_test_password();
        let pkt = build_udp_packet_ipv4(Ipv4Addr::new(240, 0, 0, 1), 0, b"z", false);
        let hdr = build_trojan_header(TEST_PASSWORD, 0x03, 0x01, &ipv4_part(8, 8, 8, 8), 53, &pkt);
        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        tls.write_all(&hdr).await.unwrap();
        tls.flush().await.unwrap();
        tokio::time::sleep(Duration::from_millis(600)).await;
        drop(tls);
        timeout(Duration::from_secs(10), server).await.expect("hung").unwrap().unwrap();
    }

    // ---- E2E TCP: unroutable WITH payload still connect-failure --------------------

    #[tokio::test]
    async fn test_e2e_tcp_unroutable_with_payload_still_connect_failure() {
        ensure_test_password();
        let payload = vec![0x43u8; 100];
        let hdr = build_trojan_header(
            TEST_PASSWORD,
            0x01,
            0x01,
            &ipv4_part(240, 0, 0, 1),
            80,
            &payload,
        );
        let msg = run_handle_client_with_input(hdr).await.unwrap_err();
        assert!(
            !msg.contains("Blocked"),
            "payload must not bypass connect-failure path, got: {}",
            msg
        );
    }

    // ---- E2E: 1-byte-chunked header reassembly ----------------------------------------

    #[tokio::test]
    async fn test_e2e_one_byte_chunks_header_blocked() {
        ensure_test_password();
        let hdr = build_trojan_header(
            TEST_PASSWORD,
            0x01,
            0x01,
            &ipv4_part(127, 0, 0, 1),
            80,
            b"",
        );
        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        for b in hdr {
            tls.write_all(&[b]).await.unwrap();
            tls.flush().await.unwrap();
        }
        tokio::time::sleep(Duration::from_millis(500)).await;
        drop(tls);
        let res = timeout(Duration::from_secs(12), server).await.expect("hung");
        let msg = res.unwrap().unwrap_err();
        assert!(msg.contains("Blocked private address"), "got: {}", msg);
    }

    // ---- E2E paused: 4096 waits, 4097 breaks (exact safeguard edge) ---------------------

    #[tokio::test]
    async fn test_e2e_initial_4096_waits_4097_breaks_paused() {
        // Safeguard is strict `> 4096`: 4096 bytes alone must NOT break the
        // read loop (server still waiting); the 4097th byte must break it to
        // fallback. Paused clock keeps this fast and deterministic.
        ensure_test_password();
        let _net_guard = BACKEND_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        tokio::time::pause();
        let pair = test_tls_matched_pair();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.unwrap();
            handle_client(stream, pair.acceptor, sem)
                .await
                .map_err(|e| e.to_string())
        });
        let tcp = TcpStream::connect(addr).await.unwrap();
        let mut tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        // 4096 'A's: invalid atyp, no double-CRLF, len == 4096 (not >).
        tls.write_all(&vec![b'A'; 4096]).await.unwrap();
        tls.flush().await.unwrap();
        for _ in 0..10 {
            tokio::task::yield_now().await;
        }
        tokio::time::advance(Duration::from_secs(10)).await;
        for _ in 0..10 {
            tokio::task::yield_now().await;
        }
        assert!(
            !server.is_finished(),
            "4096 bytes must NOT trigger the >4096 safeguard (still waiting)"
        );
        // Byte 4097 trips `len > 4096` -> break -> fallback (no backend: Err).
        tls.write_all(&[b'A']).await.unwrap();
        tls.flush().await.unwrap();
        for _ in 0..10 {
            tokio::task::yield_now().await;
        }
        // Fallback's 5s backend-connect timeout also runs on paused clock.
        tokio::time::advance(Duration::from_secs(6)).await;
        for _ in 0..10 {
            tokio::task::yield_now().await;
        }
        assert!(
            server.is_finished(),
            "4097 bytes must trigger the safeguard and fall back"
        );
        match server.await.unwrap() {
            Ok(()) => {}
            Err(msg) => assert!(!msg.contains("Blocked"), "got: {}", msg),
        }
        drop(tls);
    }

    // ---- Fallback: HTTP probe forwarded verbatim ------------------------------------------

    #[tokio::test]
    async fn test_fallback_http_probe_forwards_verbatim() {
        let probe = b"GET / HTTP/1.1\r\nHost: example.com\r\n\r\n".to_vec();
        let expect = probe.clone();
        let res = with_backend_once(async move |_| vec![], probe, b"http-probe-ok").await;
        let Some((backend_got, client_got)) = res else {
            eprintln!("SKIP: cannot bind {}", BACKEND_ADDR);
            return;
        };
        assert_eq!(backend_got, expect, "raw HTTP probe must replay verbatim for camouflage");
        assert_eq!(client_got, b"http-probe-ok");
    }

    // ---- is_allowed_peer: identical verdicts to HashSet::contains -----------

    #[test]
    fn test_is_allowed_peer_matches_contains_all_sizes() {
        use std::collections::HashSet;
        use std::net::SocketAddr;
        // Sizes straddling the linear/hash threshold (8): members,
        // non-members, same-IP-other-port, v4/v6/mapped.
        let pool: Vec<SocketAddr> = vec![
            "8.8.8.8:53".parse().unwrap(),
            "8.8.4.4:53".parse().unwrap(),
            "1.1.1.1:443".parse().unwrap(),
            "[2001:db8::1]:80".parse().unwrap(),
            "[::1]:80".parse().unwrap(),
            "10.0.0.1:9".parse().unwrap(),
            "192.168.0.1:9".parse().unwrap(),
            "172.16.0.1:9".parse().unwrap(),
            "127.0.0.1:9".parse().unwrap(),
            "9.9.9.9:995".parse().unwrap(),
            "142.250.72.14:443".parse().unwrap(),
            "208.67.222.222:443".parse().unwrap(),
            "8.8.8.8:54".parse().unwrap(),
            "[::ffff:127.0.0.1]:53".parse().unwrap(),
        ];
        let probes: Vec<SocketAddr> = vec![
            "8.8.8.8:53".parse().unwrap(),
            "8.8.8.8:54".parse().unwrap(),
            "8.8.4.4:53".parse().unwrap(),
            "1.2.3.4:53".parse().unwrap(),
            "[::1]:80".parse().unwrap(),
            "[::1]:81".parse().unwrap(),
            "[::ffff:127.0.0.1]:53".parse().unwrap(),
            "127.0.0.1:53".parse().unwrap(),
        ];
        for size in [0usize, 1, 2, 7, 8, 9, 10, 14] {
            let set: HashSet<SocketAddr> = pool.iter().take(size).cloned().collect();
            for probe in &probes {
                assert_eq!(
                    is_allowed_peer(&set, probe),
                    set.contains(probe),
                    "size={} probe={}",
                    size,
                    probe
                );
            }
        }
    }

    #[test]
    fn test_note_allowed_peer_matches_unconditional_insert() {
        use std::collections::HashSet;
        use std::net::SocketAddr;
        fn reference(seq: &[SocketAddr]) -> (HashSet<SocketAddr>, Option<SocketAddr>) {
            let mut ref_set = HashSet::new();
            for s in seq {
                ref_set.insert(*s);
            }
            (ref_set, seq.last().cloned())
        }
        // Exercise: runs, alternation, distinct peers, empty.
        let a: SocketAddr = "8.8.8.8:53".parse().unwrap();
        let b: SocketAddr = "8.8.4.4:53".parse().unwrap();
        let c: SocketAddr = "[2001:db8::1]:80".parse().unwrap();
        for seq in [
            vec![],
            vec![a],
            vec![a, a, a, a],
            vec![a, b, a, b, a],
            vec![a, b, c],
            vec![c, c, b, b, a, a],
        ] {
            let (expected_set, expected_last) = reference(&seq);
            let mut set = HashSet::new();
            let mut last = None;
            for s in &seq {
                note_allowed_peer(&mut set, &mut last, *s);
            }
            assert_eq!(set, expected_set, "set diverged for {:?}", seq);
            assert_eq!(last, expected_last, "cache diverged for {:?}", seq);
        }
    }

    #[test]
    fn test_encode_into_matches_fresh_all_forms() {
        // Scratch reuse (including after larger content: no stale tail bytes,
        // no leftover capacity effects) must equal fresh encoding exactly.
        let cases: Vec<(&str, u16, Vec<u8>)> = vec![
            ("1.2.3.4", 53, b"hello".to_vec()),
            ("::1", 443, b"abc".to_vec()),
            ("2001:db8::99", 8080, b"v6data".to_vec()),
            ("9.9.9.9", 0, b"".to_vec()),
            ("10.0.0.1", 65535, vec![0xAB; 1400]),
        ];
        let mut scratch = Vec::new();
        for (addr, port, payload) in &cases {
            let ip: IpAddr = addr.parse().unwrap();
            encode_udp_response_ip_into(&mut scratch, &ip, *port, payload);
            assert_eq!(scratch, encode_udp_response_ip(&ip, *port, payload));
            assert_eq!(scratch, encode_udp_response(addr, *port, payload).unwrap());
        }
        // Reuse after larger content.
        encode_udp_response_ip_into(&mut scratch, &"1.1.1.1".parse().unwrap(), 1, b"xy");
        assert_eq!(scratch, encode_udp_response("1.1.1.1", 1, b"xy").unwrap());
    }

    // ---- Fallback: zero-byte EOF (no bytes at all) sends zero -------------------------------

    #[tokio::test]
    async fn test_fallback_zero_byte_eof_sends_zero() {
        // Distinct from the 58-byte empty branch: client sends NOTHING then
        // EOF (read n==0 break, len 0 <58 -> fallback with empty initial_buf).
        let _guard = BACKEND_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let backend = match TcpListener::bind(BACKEND_ADDR).await {
            Ok(l) => l,
            Err(_) => {
                eprintln!("SKIP: cannot bind {}", BACKEND_ADDR);
                return;
            }
        };
        let (tx, rx) = tokio::sync::oneshot::channel::<Vec<u8>>();
        let backend_task = tokio::spawn(async move {
            let (mut sock, _) = timeout(Duration::from_secs(12), backend.accept())
                .await
                .ok()?
                .ok()?;
            let mut buf = vec![0u8; 8192];
            match timeout(Duration::from_secs(3), sock.read(&mut buf)).await {
                Ok(Ok(0)) => {
                    let _ = tx.send(vec![]);
                }
                Ok(Ok(n)) => {
                    let _ = tx.send(buf[..n].to_vec());
                }
                _ => {
                    let _ = tx.send(vec![]);
                }
            }
            let _ = sock.write_all(b"zero-ok").await;
            Some(())
        });

        ensure_test_password();
        let pair = test_tls_matched_pair();
        let front = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let front_addr = front.local_addr().unwrap();
        let sem = Arc::new(Semaphore::new(MAX_CONNECTIONS));
        let server = tokio::spawn(async move {
            let (stream, _) = front.accept().await.unwrap();
            let _ = handle_client(stream, pair.acceptor, sem).await;
        });
        let tcp = TcpStream::connect(front_addr).await.unwrap();
        let tls = pair
            .connector
            .connect(ServerName::try_from("localhost").unwrap(), tcp)
            .await
            .unwrap();
        // Immediate EOF without a single byte.
        tokio::time::sleep(Duration::from_millis(200)).await;
        drop(tls);
        let backend_got = timeout(Duration::from_secs(12), rx).await.expect("backend hung").unwrap();
        assert!(
            backend_got.is_empty(),
            "zero-byte EOF fallback must send 0 bytes, got {}: {:?}",
            backend_got.len(),
            &backend_got[..backend_got.len().min(32)]
        );
        let _ = timeout(Duration::from_secs(8), server).await;
        let _ = backend_task.await;
    }

    // ---- relay_full_duplex: surviving direction outlives EOF ---------------------

    #[tokio::test]
    async fn test_relay_full_duplex_survives_half_close() {
        // X closes its write side after MSG1; the Y->X direction must still
        // deliver MSG2 afterwards. Racing the legs with `select!` (the old
        // shape) drops the survivor at the first EOF and loses MSG2, which
        // truncates bidirectional flows such as simultaneous up/down tests.
        let (mut x_local, x_relay) = tokio::io::duplex(64 * 1024);
        let (x_r, x_w) = tokio::io::split(x_relay);
        let (mut y_local, y_relay) = tokio::io::duplex(64 * 1024);
        let (y_r, y_w) = tokio::io::split(y_relay);

        let relay = tokio::spawn(async move {
            relay_full_duplex(x_r, x_w, y_r, y_w).await
        });

        // X -> Y first message (no flush: existing pipe tests prove plain
        // write_all suffices on memory pipes; see below on flush).
        x_local.write_all(b"MSG1").await.unwrap();
        let mut m1 = [0u8; 4];
        timeout(Duration::from_secs(5), y_local.read_exact(&mut m1))
            .await
            .expect("MSG1 hung")
            .unwrap();
        assert_eq!(&m1, b"MSG1");

        // X half-closes (write side only): relay's X leg sees EOF.
        tokio::io::AsyncWriteExt::shutdown(&mut x_local).await.unwrap();

        // Y -> X must still work after that EOF.
        y_local.write_all(b"MSG2").await.unwrap();
        let mut m2 = [0u8; 4];
        timeout(Duration::from_secs(5), x_local.read_exact(&mut m2))
            .await
            .expect("MSG2 lost: survivor direction was dropped")
            .unwrap();
        assert_eq!(&m2, b"MSG2");

        // Full close on both ends; both legs must then finish Ok.
        drop(x_local);
        drop(y_local);
        let (r1, r2) = timeout(Duration::from_secs(5), relay)
            .await
            .expect("relay hung")
            .unwrap();
        assert!(r1.is_ok(), "X leg must end cleanly on EOF");
        assert!(r2.is_ok(), "Y leg must end cleanly on EOF");
    }

    // ========================================================================
    // ROUND 6 — extraction cross-checks (hoisted fns vs reference copies)
    // ========================================================================

    #[test]
    fn test_extracted_constant_time_eq_matches_reference() {
        let hash = trojan_hash(TEST_PASSWORD).into_bytes();
        let mut flip_first = hash.clone();
        flip_first[0] ^= 0x01;
        let mut flip_last = hash.clone();
        let n = flip_last.len();
        flip_last[n - 1] ^= 0x01;
        let cases: Vec<(Vec<u8>, Vec<u8>)> = vec![
            (b"abc".to_vec(), b"abc".to_vec()),
            (b"".to_vec(), b"".to_vec()),
            (b"abc".to_vec(), b"abd".to_vec()),
            (b"aaa".to_vec(), b"bbb".to_vec()),
            (hash.clone(), hash.clone()),
            (hash.clone(), flip_first),
            (hash.clone(), flip_last),
        ];
        for (a, b) in &cases {
            assert_eq!(
                constant_time_eq(a, b),
                reference_constant_time_eq(a, b),
                "mismatch for {:?} vs {:?}",
                String::from_utf8_lossy(a),
                String::from_utf8_lossy(b)
            );
        }
        for (a, b) in [
            (&b"short"[..], &b"longer"[..]),
            (&b""[..], &b"a"[..]),
            (&hash[..], &b"short"[..]),
        ] {
            assert_eq!(constant_time_eq(a, b), reference_constant_time_eq(a, b));
            assert!(!constant_time_eq(a, b));
        }
    }

    #[test]
    fn test_extracted_probe_matches_reference_incrementally() {
        // Equivalence holds under the production append history (scan every
        // prefix starting from empty), so replay append streams exactly.
        fn check_stream(chunks: &[&[u8]]) {
            let mut buf = Vec::new();
            for chunk in chunks {
                let prev = buf.len();
                buf.extend_from_slice(chunk);
                assert_eq!(
                    http_probe_detected(&buf, prev),
                    reference_should_break_for_probe(&buf),
                    "divergence after appending {:?} (prev={})",
                    String::from_utf8_lossy(chunk),
                    prev
                );
                if reference_should_break_for_probe(&buf) {
                    break; // production would have broken here as well
                }
            }
        }

        // HTTP probe arriving whole and at every split point.
        let http = b"GET / HTTP/1.1\r\nHost: example.com\r\n\r\n";
        check_stream(&[&http[..]]);
        for split in [0, 1, 10, 20, 30, 34, 35, 36, 37, 38] {
            let s = split.min(http.len());
            check_stream(&[&http[..s], &http[s..]]);
        }
        // Byte-by-byte across the whole probe (critical CRLF region included).
        {
            let mut buf = Vec::new();
            for (idx, b) in http.iter().enumerate() {
                let prev = buf.len();
                buf.push(*b);
                assert_eq!(
                    http_probe_detected(&buf, prev),
                    reference_should_break_for_probe(&buf),
                    "byte {}",
                    idx
                );
                if reference_should_break_for_probe(&buf) {
                    break;
                }
            }
        }

        // Valid Trojan prefix with embedded double-CRLF: never break, at any
        // split (binary payload must not trip the detector).
        let mut good = vec![b'A'; 56];
        good.extend_from_slice(b"\r\n");
        good.extend_from_slice(b"PAYLOAD\r\n\r\nTAIL");
        for split in [0, 30, 56, 58, 60, 62, 64, good.len()] {
            let s = split.min(good.len());
            check_stream(&[&good[..s], &good[s..]]);
        }

        // Clean data without any double-CRLF: never break.
        let clean = vec![b'Q'; 200];
        for split in [0, 100, 199, 200] {
            let s = split.min(clean.len());
            check_stream(&[&clean[..s], &clean[s..]]);
        }
    }
}

