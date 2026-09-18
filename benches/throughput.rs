//! Throughput benchmarks for the Trojan proxy hot paths.
//!
//! * No new dependencies, no `unsafe`: only `std` + the crate's existing
//!   `tokio` runtime for the async pipe benchmark.
//! * Measures the *real* server code: `src/main.rs` is textually included, so
//!   there is zero drift between benchmarked and shipped logic.
//! * Run with `cargo bench`. Output is a plain table (ops/s, ns/op, MB/s).
//!
//! NOTE: all paths below are fully qualified on purpose — `mod server`
//! already contains every `use` from `src/main.rs`, so local `use` items
//! would collide with (and even rebind) the server's names.

mod server {
    #![allow(dead_code)]
    include!("../src/main.rs");

    fn report(name: &str, iters: u64, elapsed: std::time::Duration) {
        let ns = elapsed.as_nanos() as f64 / iters as f64;
        println!("{:<38} {:>14.1} op/s  {:>10.1} ns/op", name, 1e9 / ns, ns);
    }

    fn bench<F: FnMut()>(name: &str, iters: u64, mut f: F) {
        for _ in 0..iters.min(1_000) {
            f();
        }
        let start = std::time::Instant::now();
        for _ in 0..iters {
            f();
        }
        report(name, iters, start.elapsed());
    }

    fn bench_bytes<F: FnMut()>(name: &str, iters: u64, bytes_per_iter: u64, mut f: F) {
        for _ in 0..iters.min(200) {
            f();
        }
        let start = std::time::Instant::now();
        for _ in 0..iters {
            f();
        }
        let dt = start.elapsed();
        let total = bytes_per_iter as f64 * iters as f64;
        let mb_s = total / dt.as_secs_f64() / 1_000_000.0;
        let ns = dt.as_nanos() as f64 / iters as f64;
        println!(
            "{:<38} {:>14.1} op/s  {:>10.1} ns/op  {:>9.1} MB/s",
            name,
            1e9 / ns,
            ns,
            mb_s
        );
    }

    pub fn run() {
        println!("=== trojan-proxy throughput (more is better) ===");

        // 1) Password hashing (per-connection auth setup cost).
        bench("sha224_hex(password)", 20_000, || {
            std::hint::black_box(sha224_hex(std::hint::black_box(
                "correct_test_password_12345",
            )));
        });

        // 2) SSRF gate: every TCP connection + every UDP packet pays this.
        let ips: [std::net::IpAddr; 6] = [
            "8.8.8.8".parse().unwrap(),
            "1.1.1.1".parse().unwrap(),
            "127.0.0.1".parse().unwrap(),
            "192.168.1.1".parse().unwrap(),
            "2001:4860:4860::8888".parse().unwrap(),
            "::1".parse().unwrap(),
        ];
        let mut i = 0usize;
        bench("is_private_address(mixed)", 1_000_000, || {
            i = i.wrapping_add(1);
            std::hint::black_box(is_private_address(std::hint::black_box(
                ips[i % ips.len()],
            )));
        });

        // 3) Address parsing per request.
        bench("parse_address/ipv4", 200_000, || {
            let data = [0x01, 93, 184, 216, 34];
            let mut c = 0usize;
            std::hint::black_box(parse_address(std::hint::black_box(&data), &mut c).unwrap());
        });
        bench("parse_address/domain", 200_000, || {
            let mut data = vec![0x03, 11u8];
            data.extend_from_slice(b"example.com");
            let mut c = 0usize;
            std::hint::black_box(parse_address(std::hint::black_box(&data), &mut c).unwrap());
        });
        bench("parse_address/ipv6", 200_000, || {
            let ip: std::net::Ipv6Addr = "2001:db8::1".parse().unwrap();
            let mut data = vec![0x04];
            data.extend_from_slice(&ip.octets());
            let mut c = 0usize;
            std::hint::black_box(parse_address(std::hint::black_box(&data), &mut c).unwrap());
        });

        // 4) Header-completeness gate on every initial-read chunk.
        let mut hdr = vec![b'A'; 56];
        hdr.extend_from_slice(b"\r\n");
        hdr.push(0x01);
        hdr.push(0x01);
        hdr.extend_from_slice(&[1, 2, 3, 4]);
        hdr.extend_from_slice(&443u16.to_be_bytes());
        hdr.extend_from_slice(b"\r\n");
        bench("is_trojan_header_complete/ipv4", 500_000, || {
            std::hint::black_box(is_trojan_header_complete(std::hint::black_box(&hdr)));
        });

        // 5) UDP data path: parse + encode roundtrip, 100-byte payloads.
        let payload = vec![0x55u8; 100];
        let ip4 = std::net::Ipv4Addr::new(8, 8, 8, 8);
        let mut pkt = vec![0x01];
        pkt.extend_from_slice(&ip4.octets());
        pkt.extend_from_slice(&53u16.to_be_bytes());
        pkt.extend_from_slice(&100u16.to_be_bytes());
        pkt.extend_from_slice(b"\r\n");
        pkt.extend_from_slice(&payload);
        bench_bytes("parse_udp_packet/100B", 200_000, pkt.len() as u64, || {
            let (a, p, pl, _) = parse_udp_packet(std::hint::black_box(&pkt)).unwrap();
            std::hint::black_box(a);
            std::hint::black_box(p);
            std::hint::black_box(pl);
        });
        bench_bytes(
            "encode_udp_response/100B",
            200_000,
            pkt.len() as u64,
            || {
                std::hint::black_box(
                    encode_udp_response(
                        std::hint::black_box("8.8.8.8"),
                        std::hint::black_box(53),
                        std::hint::black_box(&payload),
                    )
                    .unwrap(),
                );
            },
        );

        // 6) Full Trojan request build + parse (per-connection setup).
        bench("trojan_request/build+parse/ipv4", 100_000, || {
            let mut v = Vec::new();
            v.extend_from_slice(sha224_hex("correct_test_password_12345").as_bytes());
            v.extend_from_slice(b"\r\n");
            v.push(0x01);
            v.push(0x01);
            v.extend_from_slice(&[93, 184, 216, 34]);
            v.extend_from_slice(&80u16.to_be_bytes());
            v.extend_from_slice(b"\r\n");
            std::hint::black_box(is_trojan_header_complete(std::hint::black_box(&v)));
            let req = &v[58..];
            let mut c = 1usize;
            std::hint::black_box(parse_address(std::hint::black_box(req), &mut c).unwrap());
        });

        // 7) Bulk TCP throughput through the real pipe_data loop (8 MiB).
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        rt.block_on(async {
            let total: usize = 8 * 1024 * 1024;
            let chunk = vec![0x5Au8; 64 * 1024];
            let (mut w1, r1) = tokio::io::duplex(256 * 1024);
            let (w2, mut r2) = tokio::io::duplex(256 * 1024);
            let writer = tokio::spawn(async move {
                let mut left = total;
                while left > 0 {
                    let n = left.min(chunk.len());
                    tokio::io::AsyncWriteExt::write_all(&mut w1, &chunk[..n])
                        .await
                        .unwrap();
                    left -= n;
                }
                drop(w1);
            });
            let reader = tokio::spawn(async move {
                let mut out = 0usize;
                let mut buf = [0u8; 32 * 1024];
                loop {
                    let n = tokio::io::AsyncReadExt::read(&mut r2, &mut buf)
                        .await
                        .unwrap();
                    if n == 0 {
                        break;
                    }
                    out += n;
                }
                out
            });
            let start = std::time::Instant::now();
            pipe_data(r1, w2).await.unwrap();
            writer.await.unwrap();
            let got = reader.await.unwrap();
            let dt = start.elapsed();
            assert_eq!(got, total);
            let mb_s = total as f64 / dt.as_secs_f64() / 1_000_000.0;
            println!(
                "{:<38} {:>24.1} MB/s  ({:?} for 8 MiB)",
                "pipe_data/bulk", mb_s, dt
            );
        });

        // 8) Header gates for domain / IPv6 forms.
        let mut hd = vec![b'A'; 56];
        hd.extend_from_slice(b"\r\n");
        hd.push(0x01);
        hd.push(0x03);
        hd.push(11u8);
        hd.extend_from_slice(b"example.com");
        hd.extend_from_slice(&443u16.to_be_bytes());
        hd.extend_from_slice(b"\r\n");
        bench("is_trojan_header_complete/domain", 500_000, || {
            std::hint::black_box(is_trojan_header_complete(std::hint::black_box(&hd)));
        });
        let mut h6 = vec![b'A'; 56];
        h6.extend_from_slice(b"\r\n");
        h6.push(0x01);
        h6.push(0x04);
        h6.extend_from_slice(&[0u8; 16]);
        h6.extend_from_slice(&443u16.to_be_bytes());
        h6.extend_from_slice(b"\r\n");
        bench("is_trojan_header_complete/ipv6", 500_000, || {
            std::hint::black_box(is_trojan_header_complete(std::hint::black_box(&h6)));
        });

        // 9) MTU-sized UDP datagrams (1400 B), the realistic relay unit.
        let big_pl = vec![0x5Au8; 1400];
        let mut big_pkt = vec![0x01, 10, 0, 0, 1];
        big_pkt.extend_from_slice(&53u16.to_be_bytes());
        big_pkt.extend_from_slice(&1400u16.to_be_bytes());
        big_pkt.extend_from_slice(b"\r\n");
        big_pkt.extend_from_slice(&big_pl);
        bench_bytes("parse_udp_packet/1400B", 100_000, big_pkt.len() as u64, || {
            let (a, p, pl, _) = parse_udp_packet(std::hint::black_box(&big_pkt)).unwrap();
            std::hint::black_box(a);
            std::hint::black_box(p);
            std::hint::black_box(pl);
        });
        bench_bytes(
            "encode_udp_response/1400B",
            100_000,
            big_pkt.len() as u64,
            || {
                std::hint::black_box(
                    encode_udp_response(
                        std::hint::black_box("10.0.0.1"),
                        std::hint::black_box(53),
                        std::hint::black_box(&big_pl),
                    )
                    .unwrap(),
                );
            },
        );

        // 10) Multi-block SHA-224 (4 KiB input exercises the Vec path).
        let long_str = "a".repeat(4096);
        bench_bytes("sha224_hex/4K", 2_000, long_str.len() as u64, || {
            std::hint::black_box(sha224_hex(std::hint::black_box(long_str.as_str())));
        });

        // 11) Chatty flow: 10k x 100 B messages through pipe_data (per-read
        // syscall overhead; validates the bigger buffer costs nothing here).
        rt.block_on(async {
            let msgs = 10_000usize;
            let payload = vec![0x42u8; 100];
            let (mut w1, r1) = tokio::io::duplex(256 * 1024);
            let (w2, mut r2) = tokio::io::duplex(256 * 1024);
            let writer = tokio::spawn(async move {
                for _ in 0..msgs {
                    tokio::io::AsyncWriteExt::write_all(&mut w1, &payload)
                        .await
                        .unwrap();
                }
                drop(w1);
            });
            let reader = tokio::spawn(async move {
                let mut got = 0usize;
                let mut buf = [0u8; 4096];
                while got < msgs * 100 {
                    let n = tokio::io::AsyncReadExt::read(&mut r2, &mut buf)
                        .await
                        .unwrap();
                    if n == 0 {
                        break;
                    }
                    got += n;
                }
                got
            });
            let start = std::time::Instant::now();
            pipe_data(r1, w2).await.unwrap();
            writer.await.unwrap();
            let got = reader.await.unwrap();
            let dt = start.elapsed();
            assert_eq!(got, msgs * 100);
            println!(
                "{:<38} {:>24.1} msg/s  {:>10.1} ns/msg",
                "pipe_data/10k-x-100B",
                msgs as f64 / dt.as_secs_f64(),
                dt.as_nanos() as f64 / msgs as f64
            );
        });

        // 12) Borrowed-range UDP parser (the live relay path).
        bench_bytes("parse_udp_packet_parts/100B", 200_000, pkt.len() as u64, || {
            let (t, p, r, s) = parse_udp_packet_parts(std::hint::black_box(&pkt)).unwrap();
            std::hint::black_box(s);
            std::hint::black_box(p);
            std::hint::black_box(matches!(t, UdpTarget::Ip(_)));
            std::hint::black_box(r.start);
            std::hint::black_box(r.end);
        });
        bench_bytes(
            "parse_udp_packet_parts/1400B",
            100_000,
            big_pkt.len() as u64,
            || {
                let (t, p, r, s) =
                    parse_udp_packet_parts(std::hint::black_box(&big_pkt)).unwrap();
                std::hint::black_box(s);
                std::hint::black_box(p);
                std::hint::black_box(matches!(t, UdpTarget::Ip(_)));
                std::hint::black_box(r.start);
                std::hint::black_box(r.end);
            },
        );

        // 13) Direct-IP encoder (live reply path, no string round-trip).
        let ip100: std::net::IpAddr = "8.8.8.8".parse().unwrap();
        bench_bytes("encode_udp_response_ip/100B", 200_000, pkt.len() as u64, || {
            std::hint::black_box(encode_udp_response_ip(
                std::hint::black_box(&ip100),
                std::hint::black_box(53),
                std::hint::black_box(&payload),
            ));
        });
        let ip1400: std::net::IpAddr = "10.0.0.1".parse().unwrap();
        bench_bytes(
            "encode_udp_response_ip/1400B",
            100_000,
            big_pkt.len() as u64,
            || {
                std::hint::black_box(encode_udp_response_ip(
                    std::hint::black_box(&ip1400),
                    std::hint::black_box(53),
                    std::hint::black_box(&big_pl),
                ));
            },
        );

        // 14) Full per-packet relay CPU chain (parse parts + SSRF gate +
        // reply encode), no sockets: the hot-loop cost per datagram.
        bench_bytes("udp_relay_cpu_path/100B", 200_000, pkt.len() as u64, || {
            let (t, port, range, _) = parse_udp_packet_parts(std::hint::black_box(&pkt)).unwrap();
            let ip = match t {
                UdpTarget::Ip(ip) => ip,
                UdpTarget::Domain(_) => unreachable!(),
            };
            let sa = std::net::SocketAddr::new(std::hint::black_box(ip), std::hint::black_box(port));
            std::hint::black_box(is_private_address(std::hint::black_box(sa.ip())));
            std::hint::black_box(encode_udp_response_ip(&sa.ip(), sa.port(), &pkt[range]));
        });
        bench_bytes(
            "udp_relay_cpu_path/1400B",
            100_000,
            big_pkt.len() as u64,
            || {
                let (t, port, range, _) =
                    parse_udp_packet_parts(std::hint::black_box(&big_pkt)).unwrap();
                let ip = match t {
                    UdpTarget::Ip(ip) => ip,
                    UdpTarget::Domain(_) => unreachable!(),
                };
                let sa =
                    std::net::SocketAddr::new(std::hint::black_box(ip), std::hint::black_box(port));
                std::hint::black_box(is_private_address(std::hint::black_box(sa.ip())));
                std::hint::black_box(encode_udp_response_ip(&sa.ip(), sa.port(), &big_pkt[range]));
            },
        );

        // 15) Auth compare + probe scan micro-benches.
        let hk = sha224_hex("correct_test_password_12345");
        let hk_b = hk.clone().into_bytes();
        bench("constant_time_eq/56B", 500_000, || {
            std::hint::black_box(constant_time_eq(
                std::hint::black_box(&hk_b),
                std::hint::black_box(&hk_b),
            ));
        });
        let mut hb = vec![b'A'; 56];
        hb.extend_from_slice(b"\r\n");
        hb.extend_from_slice(b"\r\n\r\n");
        hb.extend_from_slice(&[0u8; 20]);
        bench("http_probe_detected/68B-valid-prefix", 500_000, || {
            std::hint::black_box(http_probe_detected(
                std::hint::black_box(&hb),
                std::hint::black_box(0),
            ));
        });
        let clean4k = vec![b'Q'; 4096];
        bench("http_probe_detected/4K-clean", 200_000, || {
            std::hint::black_box(http_probe_detected(
                std::hint::black_box(&clean4k),
                std::hint::black_box(0),
            ));
        });

        // 16) Worst cases: SSRF gate with all-public input (no early exit)
        // and max-length domain parsing.
        let pubs: [std::net::IpAddr; 4] = [
            "8.8.8.8".parse().unwrap(),
            "1.1.1.1".parse().unwrap(),
            "9.9.9.9".parse().unwrap(),
            "142.250.72.14".parse().unwrap(),
        ];
        let mut j = 0usize;
        bench("is_private_address(all-public)", 1_000_000, || {
            j = j.wrapping_add(1);
            std::hint::black_box(is_private_address(std::hint::black_box(
                pubs[j % pubs.len()],
            )));
        });
        let dmax = "e".repeat(255);
        let mut ddata = vec![0x03, 255u8];
        ddata.extend_from_slice(dmax.as_bytes());
        bench("parse_address/domain-255", 100_000, || {
            let mut c = 0usize;
            std::hint::black_box(parse_address(std::hint::black_box(&ddata), &mut c).unwrap());
        });

        // ====================================================================
        // OLD-vs-NEW shootout: retired implementations kept ONLY as timing
        // baselines. Each pair asserts the live code beats the old method; a
        // failure is a performance regression — investigate and revert.
        // ====================================================================
        println!("--- old-vs-new shootout (new must win) ---");

        // Retired char-push hex (replaced by the byte-array + single check).
        fn legacy_sha224_hex(s: &str) -> String {
            const HEX: &[u8; 16] = b"0123456789abcdef";
            let mut out = String::with_capacity(56);
            for byte in sha224(s.as_bytes()) {
                out.push(HEX[(byte >> 4) as usize] as char);
                out.push(HEX[(byte & 0x0f) as usize] as char);
            }
            out
        }
        // Retired reallocating encoder: Vec::new + up-to-two parses.
        fn legacy_encode_udp_response(
            addr: &str,
            port: u16,
            payload: &[u8],
        ) -> Result<Vec<u8>, String> {
            let mut response = Vec::new();
            if let Ok(ipv4) = addr.parse::<std::net::Ipv4Addr>() {
                response.push(0x01);
                response.extend_from_slice(&ipv4.octets());
            } else if let Ok(ipv6) = addr.parse::<std::net::Ipv6Addr>() {
                response.push(0x04);
                response.extend_from_slice(&ipv6.octets());
            } else {
                return Err("Invalid IP address format".to_string());
            }
            response.extend_from_slice(&port.to_be_bytes());
            response.extend_from_slice(&(payload.len() as u16).to_be_bytes());
            response.extend_from_slice(b"\r\n");
            response.extend_from_slice(payload);
            Ok(response)
        }
        // Retired copying domain parse: Vec copy before UTF-8 validation.
        fn legacy_domain_to_string(bytes: &[u8]) -> String {
            String::from_utf8(bytes.to_vec()).unwrap()
        }
        // Retired full-scan probe (replaced by the incremental window check).
        fn legacy_probe_full_scan(buf: &[u8]) -> bool {
            if buf.windows(4).any(|w| w == b"\r\n\r\n") {
                let is_valid_prefix = buf.len() >= 58 && &buf[56..58] == b"\r\n";
                return !is_valid_prefix;
            }
            false
        }

        fn measure_ns<F: FnMut()>(warmup: u64, iters: u64, mut f: F) -> f64 {
            for _ in 0..warmup {
                f();
            }
            let start = std::time::Instant::now();
            for _ in 0..iters {
                f();
            }
            start.elapsed().as_nanos() as f64 / iters as f64
        }

        fn shootout(name: &str, old_ns: f64, new_ns: f64, min_speedup: f64) {
            let speedup = old_ns / new_ns;
            let verdict = if speedup >= min_speedup {
                "BEATS-OLD"
            } else {
                "REGRESSION"
            };
            println!(
                "{:<38} old {:>9.1} ns  new {:>9.1} ns  {:>6.2}x  [{} >= {:.2}x]",
                name, old_ns, new_ns, speedup, verdict, min_speedup
            );
            assert!(
                speedup >= min_speedup,
                "PERF REGRESSION in {}: {:.2}x < required {:.2}x",
                name, speedup, min_speedup
            );
        }

        // Parity guards: legacy baselines must agree with live code, or the
        // comparison (and the old code it memorializes) is meaningless.
        assert_eq!(legacy_sha224_hex("correct_test_password_12345"), sha224_hex("correct_test_password_12345"));
        assert_eq!(
            legacy_encode_udp_response("8.8.8.8", 53, &payload).unwrap(),
            encode_udp_response("8.8.8.8", 53, &payload).unwrap()
        );
        assert_eq!(legacy_domain_to_string(b"example.com"), {
            let d = b"example.com";
            std::str::from_utf8(d).unwrap().to_owned()
        });

        let old = measure_ns(2_000, 20_000, || {
            std::hint::black_box(legacy_sha224_hex(std::hint::black_box(
                "correct_test_password_12345",
            )));
        });
        let new = measure_ns(2_000, 20_000, || {
            std::hint::black_box(sha224_hex(std::hint::black_box(
                "correct_test_password_12345",
            )));
        });
        // Regression gate only (not a speedup proof): the array-hex form is
        // ~neutral vs char-push (~3%); fail only if it ever gets slower.
        shootout("sha224_hex", old, new, 0.95);

        let old = measure_ns(5_000, 100_000, || {
            std::hint::black_box(
                legacy_encode_udp_response(
                    std::hint::black_box("8.8.8.8"),
                    std::hint::black_box(53),
                    std::hint::black_box(&payload),
                )
                .unwrap(),
            );
        });
        let new = measure_ns(5_000, 100_000, || {
            std::hint::black_box(
                encode_udp_response(
                    std::hint::black_box("8.8.8.8"),
                    std::hint::black_box(53),
                    std::hint::black_box(&payload),
                )
                .unwrap(),
            );
        });
        // margins use the in-harness legacy numbers (~2.8x here), not the
        // noisier first-ever baseline run.
        shootout("encode_udp_response/100B", old, new, 2.0);

        let old = measure_ns(2_000, 100_000, || {
            std::hint::black_box(
                legacy_encode_udp_response(
                    std::hint::black_box("10.0.0.1"),
                    std::hint::black_box(53),
                    std::hint::black_box(&big_pl),
                )
                .unwrap(),
            );
        });
        let new = measure_ns(2_000, 100_000, || {
            std::hint::black_box(
                encode_udp_response(
                    std::hint::black_box("10.0.0.1"),
                    std::hint::black_box(53),
                    std::hint::black_box(&big_pl),
                )
                .unwrap(),
            );
        });
        shootout("encode_udp_response/1400B", old, new, 2.0);

        let dom11 = b"example.com";
        let old = measure_ns(5_000, 200_000, || {
            std::hint::black_box(legacy_domain_to_string(std::hint::black_box(dom11)));
        });
        let new = measure_ns(5_000, 200_000, || {
            std::hint::black_box(
                std::str::from_utf8(std::hint::black_box(dom11))
                    .unwrap()
                    .to_owned(),
            );
        });
        // Regression gate only: `String::from_utf8(Vec)` reuses the Vec
        // buffer, so borrow-vs-copy is inherently ~parity (one small memcpy).
        // Observed run band is 0.94x-1.03x (pure allocator noise); fail only
        // on a real >10% slowdown. Kept for code clarity, not speed.
        shootout("domain_parse/11B", old, new, 0.90);

        // Probe: 4K buffer ending in an (invalid-prefix) double-CRLF; the
        // incremental form scans ~7 windows instead of ~4093.
        let mut probe_buf = vec![b'Q'; 4092];
        probe_buf.extend_from_slice(b"\r\n\r\n");
        assert!(legacy_probe_full_scan(&probe_buf));
        assert!(http_probe_detected(&probe_buf, 4092));
        let old = measure_ns(2_000, 50_000, || {
            std::hint::black_box(legacy_probe_full_scan(std::hint::black_box(&probe_buf)));
        });
        let new = measure_ns(2_000, 50_000, || {
            std::hint::black_box(http_probe_detected(
                std::hint::black_box(&probe_buf),
                std::hint::black_box(4092),
            ));
        });
        shootout("http_probe/4K-found", old, new, 10.0);

        // Borrowed-range parser vs the cloning wrapper (both live).
        let old = measure_ns(5_000, 100_000, || {
            std::hint::black_box(parse_udp_packet(std::hint::black_box(&pkt)).unwrap());
        });
        let new = measure_ns(5_000, 100_000, || {
            let (t, p, r, s) = parse_udp_packet_parts(std::hint::black_box(&pkt)).unwrap();
            std::hint::black_box(s);
            std::hint::black_box(p);
            std::hint::black_box(matches!(t, UdpTarget::Ip(_)));
            std::hint::black_box(r.start);
            std::hint::black_box(r.end);
        });
        shootout("parse_udp_packet_parts/100B", old, new, 5.0);

        // Peer-gate concept check: SipHash contains vs linear scan on a
        // 1-entry set (the common single-peer session shape).
        let mut one: std::collections::HashSet<std::net::SocketAddr> =
            std::collections::HashSet::new();
        one.insert("8.8.8.8:53".parse().unwrap());
        let probe_sa: std::net::SocketAddr = "8.8.8.8:53".parse().unwrap();
        let old = measure_ns(5_000, 500_000, || {
            std::hint::black_box(one.contains(std::hint::black_box(&probe_sa)));
        });
        // Production hybrid gate (live code) vs raw contains.
        let new = measure_ns(5_000, 500_000, || {
            std::hint::black_box(is_allowed_peer(
                std::hint::black_box(&one),
                std::hint::black_box(&probe_sa),
            ));
        });
        shootout("peer_gate/1-entry", old, new, 2.0);

        // Warmed scratch buffer vs fresh allocation per reply (1400 B).
        // Parity is asserted: same bytes, the difference is pure alloc.
        let sip: std::net::IpAddr = "10.0.0.1".parse().unwrap();
        let mut scratch = Vec::new();
        encode_udp_response_ip_into(&mut scratch, &sip, 53, &big_pl);
        assert_eq!(scratch, encode_udp_response_ip(&sip, 53, &big_pl));
        let old = measure_ns(2_000, 100_000, || {
            std::hint::black_box(encode_udp_response_ip(
                std::hint::black_box(&sip),
                std::hint::black_box(53),
                std::hint::black_box(&big_pl),
            ));
        });
        let new = measure_ns(2_000, 100_000, || {
            encode_udp_response_ip_into(
                std::hint::black_box(&mut scratch),
                std::hint::black_box(&sip),
                std::hint::black_box(53),
                std::hint::black_box(&big_pl),
            );
            std::hint::black_box(scratch.len());
        });
        shootout("encode_ip_into/1400B-warmed", old, new, 1.5);

        // ====================================================================
        // ROUND 5 — newly covered paths
        // ====================================================================

        // Resolver dispatch: numeric literals need no network either way, so
        // this trio isolates pure dispatch cost (thread hop vs integer
        // parse). Tuple and string forms must resolve identically.
        let t_new = measure_ns(5_000, 200_000, || {
            let sa = std::net::SocketAddr::new(
                std::hint::black_box("127.0.0.1".parse::<std::net::IpAddr>().unwrap()),
                std::hint::black_box(80),
            );
            std::hint::black_box(sa);
        });
        let (t_tup, t_str) = rt.block_on(async {
            let mut a = tokio::net::lookup_host(("127.0.0.1", 80u16)).await.unwrap();
            let mut b = tokio::net::lookup_host("127.0.0.1:80").await.unwrap();
            assert_eq!(a.next(), b.next(), "tuple and string forms must agree");
            for _ in 0..200 {
                // Consume one item per call: forces any lazy resolution to
                // happen inside the timed region, not after it.
                let mut x = tokio::net::lookup_host(("127.0.0.1", 80u16)).await.unwrap();
                std::hint::black_box(x.next());
                let mut y = tokio::net::lookup_host("127.0.0.1:80").await.unwrap();
                std::hint::black_box(y.next());
            }
            let now = std::time::Instant::now();
            for _ in 0..3_000 {
                let mut it = tokio::net::lookup_host(("127.0.0.1", 80u16)).await.unwrap();
                std::hint::black_box(it.next());
            }
            let t_tup = now.elapsed().as_nanos() as f64 / 3_000.0;
            let now = std::time::Instant::now();
            for _ in 0..3_000 {
                let mut it = tokio::net::lookup_host("127.0.0.1:80").await.unwrap();
                std::hint::black_box(it.next());
            }
            (t_tup, now.elapsed().as_nanos() as f64 / 3_000.0)
        });
        // Margins use the honest consumed-iterator numbers (~3.7x): tokio
        // resolves numerics without a thread hop, so the win is one small
        // dispatch plus the `format!` alloc, not microseconds.
        shootout("resolve/numeric-vs-lookup-tuple", t_tup, t_new, 2.0);
        shootout("resolve/numeric-vs-lookup-string", t_str, t_new, 2.0);

        // Drain churn: 50 pipelined 100B datagrams, drain-per-packet (old)
        // vs consume-offset plus a single compact (new). Same frames out.
        let one100 = {
            let pl = vec![0x61u8; 100];
            let mut p = vec![0x01, 9, 9, 9, 9];
            p.extend_from_slice(&53u16.to_be_bytes());
            p.extend_from_slice(&100u16.to_be_bytes());
            p.extend_from_slice(b"\r\n");
            p.extend_from_slice(&pl);
            p
        };
        let mut pipe50 = Vec::new();
        for _ in 0..50 {
            pipe50.extend_from_slice(&one100);
        }
        // Parity guard: both strategies forward identical bytes.
        let reference = {
            let mut buf = pipe50.clone();
            let mut out = Vec::new();
            let mut n = 0usize;
            while !buf.is_empty() {
                if let Some((_, _, r, sz)) = parse_udp_packet_parts(&buf) {
                    out.extend_from_slice(&buf[r]);
                    n += 1;
                    buf.drain(..sz);
                } else {
                    break;
                }
            }
            (n, out, buf.len())
        };
        let candidate = {
            let mut buf = pipe50.clone();
            let mut consumed = 0usize;
            let mut out = Vec::new();
            let mut n = 0usize;
            while consumed < buf.len() {
                if let Some((_, _, r, sz)) = parse_udp_packet_parts(&buf[consumed..]) {
                    out.extend_from_slice(&buf[consumed + r.start..consumed + r.end]);
                    n += 1;
                    consumed += sz;
                } else {
                    break;
                }
            }
            if consumed > 0 {
                if consumed >= buf.len() {
                    buf.clear();
                } else {
                    buf.drain(..consumed);
                }
            }
            (n, out, buf.len())
        };
        assert_eq!(reference, candidate, "offset strategy must forward identical bytes");
        assert_eq!(reference.0, 50);
        assert_eq!(reference.2, 0);
        let old = measure_ns(200, 2_000, || {
            let mut buf = pipe50.clone();
            let mut n = 0usize;
            let mut bytes = 0usize;
            while !buf.is_empty() {
                if let Some((_, _, r, sz)) = parse_udp_packet_parts(&buf) {
                    bytes += r.end - r.start;
                    n += 1;
                    buf.drain(..sz);
                } else {
                    break;
                }
            }
            std::hint::black_box((n, bytes));
        });
        let new = measure_ns(200, 2_000, || {
            let mut buf = pipe50.clone();
            let mut consumed = 0usize;
            let mut n = 0usize;
            let mut bytes = 0usize;
            while consumed < buf.len() {
                if let Some((_, _, r, sz)) = parse_udp_packet_parts(&buf[consumed..]) {
                    bytes += r.end - r.start;
                    n += 1;
                    consumed += sz;
                } else {
                    break;
                }
            }
            if consumed > 0 {
                if consumed >= buf.len() {
                    buf.clear();
                } else {
                    buf.drain(..consumed);
                }
            }
            std::hint::black_box((n, bytes, buf.len()));
        });
        shootout("buffer/drain-each-vs-offset/50x100B", old, new, 1.2);

        // Remaining uncovered units: domain UDP parse, domain/IPv6 request
        // framing, small probe verdict, mismatch/special-case branches.
        let mut dom_pkt = vec![0x03, 11u8];
        dom_pkt.extend_from_slice(b"example.com");
        dom_pkt.extend_from_slice(&53u16.to_be_bytes());
        dom_pkt.extend_from_slice(&4u16.to_be_bytes());
        dom_pkt.extend_from_slice(b"\r\n");
        dom_pkt.extend_from_slice(b"data");
        bench_bytes("parse_udp_packet/domain-11B", 200_000, dom_pkt.len() as u64, || {
            let (a, p, pl, _) = parse_udp_packet(std::hint::black_box(&dom_pkt)).unwrap();
            std::hint::black_box(a);
            std::hint::black_box(p);
            std::hint::black_box(pl);
        });

        // Same per-iteration build methodology as the ipv4 variant above
        // (fresh hash + buffer each time), so the three are comparable.
        bench("trojan_request/build+parse/domain", 100_000, || {
            let mut v = Vec::new();
            v.extend_from_slice(sha224_hex("correct_test_password_12345").as_bytes());
            v.extend_from_slice(b"\r\n");
            v.push(0x01);
            v.push(0x03);
            v.push(11u8);
            v.extend_from_slice(b"example.com");
            v.extend_from_slice(&443u16.to_be_bytes());
            v.extend_from_slice(b"\r\n");
            std::hint::black_box(is_trojan_header_complete(std::hint::black_box(&v)));
            let req = &v[58..];
            let mut c = 1usize;
            std::hint::black_box(parse_address(std::hint::black_box(req), &mut c).unwrap());
        });
        bench("trojan_request/build+parse/ipv6", 100_000, || {
            let ip6: std::net::Ipv6Addr = "2001:db8::1".parse().unwrap();
            let mut v = Vec::new();
            v.extend_from_slice(sha224_hex("correct_test_password_12345").as_bytes());
            v.extend_from_slice(b"\r\n");
            v.push(0x01);
            v.push(0x04);
            v.extend_from_slice(&ip6.octets());
            v.extend_from_slice(&443u16.to_be_bytes());
            v.extend_from_slice(b"\r\n");
            std::hint::black_box(is_trojan_header_complete(std::hint::black_box(&v)));
            let req = &v[58..];
            let mut c = 1usize;
            std::hint::black_box(parse_address(std::hint::black_box(req), &mut c).unwrap());
        });

        let small_probe = b"GET /\r\n\r\n".to_vec();
        bench("http_probe/11B-probe-true", 500_000, || {
            std::hint::black_box(http_probe_detected(
                std::hint::black_box(&small_probe),
                std::hint::black_box(0),
            ));
        });
        bench("constant_time_eq/len-mismatch", 500_000, || {
            std::hint::black_box(constant_time_eq(
                std::hint::black_box(b"short"),
                std::hint::black_box(b"longer"),
            ));
        });
        bench("is_trojan_header_complete/short-false", 500_000, || {
            let empty: &[u8] = &[];
            std::hint::black_box(is_trojan_header_complete(std::hint::black_box(empty)));
        });
        bench("encode_udp_response/reject-domain", 200_000, || {
            std::hint::black_box(
                encode_udp_response(
                    std::hint::black_box("example.com"),
                    std::hint::black_box(80),
                    std::hint::black_box(b"hi"),
                )
                .unwrap_err(),
            );
        });
        bench("parse_udp_packet/invalid-atyp", 200_000, || {
            let bad = [0xFFu8, 0, 0, 0, 0, 0];
            std::hint::black_box(parse_udp_packet(std::hint::black_box(&bad)));
        });

        // Slow path of the peer gate: 64-entry set takes the hash branch.
        let mut big_set: std::collections::HashSet<std::net::SocketAddr> =
            std::collections::HashSet::new();
        for i in 0..64u16 {
            big_set.insert(std::net::SocketAddr::new(
                std::net::IpAddr::V4(std::net::Ipv4Addr::new(10, 0, (i >> 8) as u8, i as u8)),
                1000 + i,
            ));
        }
        let hit: std::net::SocketAddr = "10.0.0.7:1007".parse().unwrap();
        bench("is_allowed_peer/64-entry", 500_000, || {
            std::hint::black_box(is_allowed_peer(
                std::hint::black_box(&big_set),
                std::hint::black_box(&hit),
            ));
        });

        // ====================================================================
        // ROUND 6 — associate framing, block edges, thresholds, insert churn
        // ====================================================================

        // UDP ASSOCIATE setup: header framing plus first-datagram parse.
        bench("udp_associate/setup+first-parse", 100_000, || {
            let mut hdr = Vec::new();
            hdr.extend_from_slice(sha224_hex("correct_test_password_12345").as_bytes());
            hdr.extend_from_slice(b"\r\n");
            hdr.push(0x03);
            hdr.push(0x01);
            hdr.extend_from_slice(&[8, 8, 8, 8]);
            hdr.extend_from_slice(&53u16.to_be_bytes());
            hdr.extend_from_slice(b"\r\n");
            std::hint::black_box(is_trojan_header_complete(std::hint::black_box(&hdr)));
            let mut udp_pkt = vec![0x01, 1, 2, 3, 4];
            udp_pkt.extend_from_slice(&53u16.to_be_bytes());
            udp_pkt.extend_from_slice(&4u16.to_be_bytes());
            udp_pkt.extend_from_slice(b"\r\n");
            udp_pkt.extend_from_slice(b"data");
            let (t, p, r, s) = parse_udp_packet_parts(std::hint::black_box(&udp_pkt)).unwrap();
            std::hint::black_box(p);
            std::hint::black_box(s);
            std::hint::black_box(matches!(t, UdpTarget::Ip(_)));
            std::hint::black_box(r.end);
        });

        // SHA block edge: 55 B fits one block, 56 B spills into two.
        let s55 = "b".repeat(55);
        let s56 = "b".repeat(56);
        bench_bytes("sha224_hex/55B-one-block", 20_000, 55, || {
            std::hint::black_box(sha224_hex(std::hint::black_box(&s55)));
        });
        bench_bytes("sha224_hex/56B-two-blocks", 20_000, 56, || {
            std::hint::black_box(sha224_hex(std::hint::black_box(&s56)));
        });

        // Probe steady state: 4K clean buffer with simulated history
        // (prev=4093 rescans ~7 windows instead of ~4093).
        bench("http_probe_detected/4K-incremental", 200_000, || {
            std::hint::black_box(http_probe_detected(
                std::hint::black_box(&clean4k),
                std::hint::black_box(4093),
            ));
        });

        // Peer-gate threshold sides: 8 takes linear, 9 takes hash.
        let mut set8: std::collections::HashSet<std::net::SocketAddr> =
            std::collections::HashSet::new();
        for i in 0..8u16 {
            set8.insert(std::net::SocketAddr::new(
                std::net::IpAddr::V4(std::net::Ipv4Addr::new(10, 2, 0, i as u8)),
                2000 + i,
            ));
        }
        let mut set9 = set8.clone();
        set9.insert("10.2.0.8:2008".parse().unwrap());
        let hit8: std::net::SocketAddr = "10.2.0.7:2007".parse().unwrap();
        bench("is_allowed_peer/8-entry-linear", 500_000, || {
            std::hint::black_box(is_allowed_peer(
                std::hint::black_box(&set8),
                std::hint::black_box(&hit8),
            ));
        });
        bench("is_allowed_peer/9-entry-hash", 500_000, || {
            std::hint::black_box(is_allowed_peer(
                std::hint::black_box(&set9),
                std::hint::black_box(&hit8),
            ));
        });

        // Insert churn: 1000 datagrams to one peer, insert-every-time (old)
        // vs cached (new). Same final set (asserted); only hashing differs.
        // Adversarial twin: strict alternation defeats the cache — the new
        // path must stay within 25% (one extra compare per packet).
        let same_peer: std::net::SocketAddr = "9.9.9.9:53".parse().unwrap();
        let other_peer: std::net::SocketAddr = "8.8.4.4:53".parse().unwrap();
        {
            let mut a = std::collections::HashSet::new();
            for _ in 0..1_000 {
                a.insert(same_peer);
            }
            let mut b = std::collections::HashSet::new();
            let mut last = None;
            for _ in 0..1_000 {
                note_allowed_peer(&mut b, &mut last, same_peer);
            }
            assert_eq!(a, b, "cached inserts must build the identical set");
            assert_eq!(last, Some(same_peer));
        }
        let old = measure_ns(500, 2_000, || {
            let mut set = std::collections::HashSet::new();
            for _ in 0..1_000 {
                set.insert(std::hint::black_box(same_peer));
            }
            std::hint::black_box(set.len());
        });
        let new = measure_ns(500, 2_000, || {
            let mut set = std::collections::HashSet::new();
            let mut last = None;
            for _ in 0..1_000 {
                note_allowed_peer(&mut set, &mut last, std::hint::black_box(same_peer));
            }
            std::hint::black_box((set.len(), last));
        });
        shootout("peer_insert/same-x1000", old, new, 2.0);
        let old = measure_ns(500, 2_000, || {
            let mut set = std::collections::HashSet::new();
            for i in 0..1_000 {
                let p = if i % 2 == 0 { same_peer } else { other_peer };
                set.insert(std::hint::black_box(p));
            }
            std::hint::black_box(set.len());
        });
        let new = measure_ns(500, 2_000, || {
            let mut set = std::collections::HashSet::new();
            let mut last = None;
            for i in 0..1_000 {
                let p = if i % 2 == 0 { same_peer } else { other_peer };
                note_allowed_peer(&mut set, &mut last, std::hint::black_box(p));
            }
            std::hint::black_box((set.len(), last));
        });
        // Worst case for the cache (strict alternation always misses): the
        // extra compare costs a few ns per packet. Observed band is
        // 0.78x-0.84x (pure noise on ~2ns); fail only past a real >33%
        // overhead blowout.
        shootout("peer_insert/alternating", old, new, 0.75);

        // Warmed scratch at 100 B (1400 B variant already gated above).
        let qip: std::net::IpAddr = "8.8.8.8".parse().unwrap();
        let qpl = vec![0x51u8; 100];
        let mut qscratch = Vec::new();
        encode_udp_response_ip_into(&mut qscratch, &qip, 53, &qpl);
        assert_eq!(qscratch, encode_udp_response_ip(&qip, 53, &qpl));
        let old = measure_ns(5_000, 200_000, || {
            std::hint::black_box(encode_udp_response_ip(
                std::hint::black_box(&qip),
                std::hint::black_box(53),
                std::hint::black_box(&qpl),
            ));
        });
        let new = measure_ns(5_000, 200_000, || {
            encode_udp_response_ip_into(
                std::hint::black_box(&mut qscratch),
                std::hint::black_box(&qip),
                std::hint::black_box(53),
                std::hint::black_box(&qpl),
            );
            std::hint::black_box(qscratch.len());
        });
        shootout("encode_ip_into/100B-warmed", old, new, 1.5);

        // ====================================================================
        // ROUND 7 — leftover units, branches, and threshold completions
        // ====================================================================

        // Borrowed-range parser on a domain packet (validation, no clone).
        let mut dom100 = vec![0x03, 11u8];
        dom100.extend_from_slice(b"example.com");
        dom100.extend_from_slice(&53u16.to_be_bytes());
        dom100.extend_from_slice(&7u16.to_be_bytes());
        dom100.extend_from_slice(b"\r\n");
        dom100.extend_from_slice(b"payload");
        bench_bytes("parse_udp_packet_parts/domain-11B", 200_000, dom100.len() as u64, || {
            let (t, p, r, s) = parse_udp_packet_parts(std::hint::black_box(&dom100)).unwrap();
            std::hint::black_box(s);
            std::hint::black_box(p);
            std::hint::black_box(matches!(t, UdpTarget::Domain(_)));
            std::hint::black_box(r.end);
        });

        // Direct-IP encoder, IPv6 form (16-byte address path).
        let ip6enc: std::net::IpAddr = "::1".parse().unwrap();
        let pl6 = b"abc".to_vec();
        bench("encode_udp_response_ip/ipv6-100B", 200_000, || {
            std::hint::black_box(encode_udp_response_ip(
                std::hint::black_box(&ip6enc),
                std::hint::black_box(443),
                std::hint::black_box(&pl6),
            ));
        });

        // Header gate: invalid address type (earliest branch out).
        let mut bad_hdr = vec![b'A'; 56];
        bad_hdr.extend_from_slice(b"\r\n");
        bad_hdr.push(0x01);
        bad_hdr.push(0xFF);
        bad_hdr.extend_from_slice(&[0u8; 20]);
        bench("is_trojan_header_complete/invalid-atyp", 500_000, || {
            std::hint::black_box(is_trojan_header_complete(std::hint::black_box(&bad_hdr)));
        });

        // SSRF gate, all-IPv6 public input (segment-mask path, no early exit).
        let v6pubs: [std::net::IpAddr; 4] = [
            "2001:4860:4860::8888".parse().unwrap(),
            "2606:4700:4700::1111".parse().unwrap(),
            "2001:db8::1".parse().unwrap(),
            "64:ff9b::808:808".parse().unwrap(),
        ];
        let mut k = 0usize;
        bench("is_private_address(all-v6-public)", 1_000_000, || {
            k = k.wrapping_add(1);
            std::hint::black_box(is_private_address(std::hint::black_box(
                v6pubs[k % v6pubs.len()],
            )));
        });

        // Parser error branches: truncated domain and invalid UTF-8.
        bench("parse_address/truncated-domain", 200_000, || {
            let data = [0x03, 5u8, b'a', b'b'];
            let mut c = 0usize;
            std::hint::black_box(parse_address(std::hint::black_box(&data), &mut c).unwrap_err());
        });
        bench("parse_address/invalid-utf8", 200_000, || {
            let data = [0x03, 2u8, 0xFF, 0xFE];
            let mut c = 0usize;
            std::hint::black_box(parse_address(std::hint::black_box(&data), &mut c).unwrap_err());
        });

        // Full IPv6 relay CPU chain (parse parts + gate + reply encode).
        let mut pkt6 = vec![0x04];
        pkt6.extend_from_slice(&[0x20, 0x01, 0x0d, 0xb8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x53]);
        pkt6.extend_from_slice(&53u16.to_be_bytes());
        pkt6.extend_from_slice(&4u16.to_be_bytes());
        pkt6.extend_from_slice(b"\r\n");
        pkt6.extend_from_slice(b"v6d!");
        bench_bytes("udp_relay_cpu_path/ipv6-100B", 200_000, pkt6.len() as u64, || {
            let (t, port, range, _) = parse_udp_packet_parts(std::hint::black_box(&pkt6)).unwrap();
            let ip = match t {
                UdpTarget::Ip(ip) => ip,
                UdpTarget::Domain(_) => unreachable!(),
            };
            let sa = std::net::SocketAddr::new(std::hint::black_box(ip), std::hint::black_box(port));
            std::hint::black_box(is_private_address(std::hint::black_box(sa.ip())));
            std::hint::black_box(encode_udp_response_ip(&sa.ip(), sa.port(), &pkt6[range]));
        });

        // Constant-time claim, observed (report-only: equality must hold
        // within noise since there is deliberately no early exit).
        let hk2 = sha224_hex("correct_test_password_12345").into_bytes();
        let mut hk_diff = hk2.clone();
        hk_diff[55] ^= 0x01;
        let t_eq = measure_ns(100_000, 500_000, || {
            std::hint::black_box(constant_time_eq(
                std::hint::black_box(&hk2),
                std::hint::black_box(&hk2),
            ));
        });
        let t_ne = measure_ns(100_000, 500_000, || {
            std::hint::black_box(constant_time_eq(
                std::hint::black_box(&hk2),
                std::hint::black_box(&hk_diff),
            ));
        });
        println!(
            "{:<38} eq {:>9.1} ns  ne {:>9.1} ns  ratio {:>5.2}x (expect ~1.00)",
            "constant_time_eq/equal-vs-last-diff",
            t_eq,
            t_ne,
            t_eq / t_ne
        );

        // Peer-gate matrix completion: empty set (vacuous false).
        let empty_set: std::collections::HashSet<std::net::SocketAddr> =
            std::collections::HashSet::new();
        let probe0: std::net::SocketAddr = "8.8.8.8:53".parse().unwrap();
        bench("is_allowed_peer/empty-set", 500_000, || {
            std::hint::black_box(is_allowed_peer(
                std::hint::black_box(&empty_set),
                std::hint::black_box(&probe0),
            ));
        });

        // Full-duplex relay: 4 MiB EACH WAY simultaneously through the
        // production relay_full_duplex composition (the phone-speedtest
        // shape: up and down at once, neither leg allowed to truncate the
        // other). Correct halves order (a_r, a_w, b_r, b_w) is load-bearing:
        // see test_relay_full_duplex_survives_half_close. Readers run
        // concurrently with writers so 256 KiB channel buffers never wedge.
        rt.block_on(async {
            async fn pump_out(
                mut w: tokio::io::DuplexStream,
                chunk: Vec<u8>,
                total: usize,
            ) {
                let mut left = total;
                while left > 0 {
                    let n = left.min(chunk.len());
                    tokio::io::AsyncWriteExt::write_all(&mut w, &chunk[..n])
                        .await
                        .unwrap();
                    left -= n;
                }
                drop(w);
            }
            async fn pump_in(mut r: tokio::io::DuplexStream, total: usize) -> usize {
                let mut got = 0usize;
                let mut buf = [0u8; 32 * 1024];
                while got < total {
                    let n = tokio::io::AsyncReadExt::read(&mut r, &mut buf)
                        .await
                        .unwrap();
                    if n == 0 {
                        break;
                    }
                    got += n;
                }
                got
            }
            let total: usize = 4 * 1024 * 1024;
            let (a_in_w, a_in_r) = tokio::io::duplex(256 * 1024);
            let (b_out_w, b_out_r) = tokio::io::duplex(256 * 1024);
            let (b_in_w, b_in_r) = tokio::io::duplex(256 * 1024);
            let (a_out_w, a_out_r) = tokio::io::duplex(256 * 1024);
            let w_a = tokio::spawn(pump_out(a_in_w, vec![0x41u8; 64 * 1024], total));
            let r_a = tokio::spawn(pump_in(a_out_r, total));
            let w_b = tokio::spawn(pump_out(b_in_w, vec![0x42u8; 64 * 1024], total));
            let r_b = tokio::spawn(pump_in(b_out_r, total));
            let start = std::time::Instant::now();
            relay_full_duplex(a_in_r, a_out_w, b_in_r, b_out_w).await;
            w_a.await.unwrap();
            w_b.await.unwrap();
            let got_a = r_a.await.unwrap();
            let got_b = r_b.await.unwrap();
            let dt = start.elapsed();
            assert_eq!(got_a, total, "A->B direction lost bytes");
            assert_eq!(got_b, total, "B->A direction lost bytes");
            let mb_s = 2.0 * total as f64 / dt.as_secs_f64() / 1_000_000.0;
            println!(
                "{:<38} {:>24.1} MB/s duplex  ({:?} for 2x4 MiB)",
                "relay_full_duplex/2x4MiB", mb_s, dt
            );
        });

        println!("=== done ===");
    }
}

fn main() {
    server::run();
}
