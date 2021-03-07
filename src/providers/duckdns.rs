use super::Error;
use super::error;
use super::{Response, UpdateResult};

use std::net;

// use isahc::error as isahce;
use isahc;
use lazy_static::lazy_static;
use regex::Regex;
use url::Url;

pub struct Updater<'a> {
    token: &'a str,
    base_url: &'a str,
    http_cli: isahc::HttpClient,
}

impl<'a> Updater<'a> {
    pub fn new(token: &'a str) -> Self {
        Self::new_with_base_url(token, "https://www.duckdns.org/update?verbose=true")
    }

    // this constructor is mainly useful for testing purpose.
    fn new_with_base_url(token: &'a str, base_url: &'a str) -> Self {
        let http_cli = isahc::HttpClientBuilder::new()
            .max_connections(2)
            .connection_cache_size(2)
            .connection_cache_ttl(std::time::Duration::from_secs(5))
            .build()
            .expect("HTTP client initialization error, this due to a bug in this crate, please report it");

        Updater {
            token,
            base_url,
            http_cli,
        }
    }

    pub async fn update_record_a<'b>(
        &self,
        domains: &[&str],
        ipv4: Option<net::Ipv4Addr>,
        ipv6: Option<net::Ipv6Addr>,
    ) -> UpdateResult<'b> {
        let mut params = Vec::with_capacity(3);
        params.push(Self::domains_as_param(domains)?);

        if ipv4.is_none() && ipv6.is_none() {}
        if let Some(ip) = ipv4 {
            params.push(("ip", ip.to_string()))
        }

        if let Some(ip) = ipv6 {
            params.push(("ipv6", ip.to_string()))
        }

        let url = Url::parse_with_params(self.base_url, params)
            .expect("Failed to parse base URL with domains names due to a bug");

        // TODO: continue here using result map_err
        let res = self.http_cli.get_async(url.as_str()).await;
        let res = res.map_err(|err: isahc::Error| {
            use isahc::error::ErrorKind;
            match err.kind() {
                ErrorKind::BadServerCertificate |ErrorKind::InvalidContentEncoding | ErrorKind::ProtocolViolation | ErrorKind::TooManyRedirects=>
                   Error::Provider(error::Provider::Internal),
                ErrorKind::ConnectionFailed | ErrorKind::Timeout =>
                    // TODO: resolve compiling error
                   Error::Network(&err, true),
                ErrorKind::Io | ErrorKind::NameResolution|ErrorKind::TlsEngine =>
                    // TODO: check if it's server or network error, if it's client it assess what
                    // to do
                _ =>  panic!("provider implementation error: there is a bug or the implementation has not been updated to fulfill the last service changes.\nError: {}", err),
            }
        });
        /*
        match res {
            Ok(isahc::Response(&str)) => panic!("asdf")
            Err()
        }
        */

        Ok(Response {
            result_msg: "someting",
            updated: Some(false),
        })
    }

    fn domains_as_param<'b, 'c>(
        domains: &'b [&str],
    ) -> Result<(&'static str, String), Error<'c>> {
        if domains.is_empty() {
            return Err(Error::new_invalid_arguments(
                "domains",
                "domains cannot be empty, it must contain at least one domain name",
            ));
        }

        match Self::validate_domain(domains[0]) {
            Err(Error::InvalidArguments(error::Args { msg, .. })) => {
                return Err(Error::new_invalid_arguments("domains[0]", &msg));
            }
            Err(e) => panic!("Self::validate_domain returned an unexpected error: {}", e),
            Ok(_) => {}
        }

        let mut idx = 1;
        let val = domains
            .iter()
            .skip(1)
            .try_fold(
                String::from(domains[0]),
                |mut acc, d| match Self::validate_domain(d) {
                    Ok(_) => {
                        acc.push(',');
                        acc.push_str(d);
                        idx += 1;
                        Ok(acc)
                    }
                    Err(Error::InvalidArguments(error::Args { msg, .. })) => Err(
                        Error::new_invalid_arguments(&format!("domains[{}]", idx), &msg),
                    ),
                    Err(e) => panic!("Self::validate_domain returned an unexpected error: {}", e),
                },
            )?;

        Ok(("domains", val))
    }

    // Validates domain is a valid DuckDNS name.
    fn validate_domain(domain: &str) -> Result<(), Error> {
        // valid characters are:  A-Z, 0-9, -
        // Check how the Rexp syntax is
        lazy_static! {
            static ref RE: Regex = Regex::new(r"(?i)^[a-z0-9\-]+$").unwrap();
        }

        if !RE.is_match(domain) {
            return Err(
                Error::new_invalid_arguments(
                    "domain",
                    "a domain name can only contain 'a-z', '0-9' and '-' case insensitive characters and must have at least one character",
                ),
            );
        }

        Ok(())
    }

    fn parse_response_body(body: &str) -> ResponseBody {
        let mut iter = body.splitn(4, '\n');
        if let Some(op_status) = iter.next() {
            match op_status {
                "OK" => {
                    let mut iter = iter.skip(2);
                    if let Some(change_status) = iter.next() {
                        return ResponseBody::Success(change_status == "UPDATED");
                    }
                }
                "KO" => return ResponseBody::Failed,
                _ => {}
            };
        }

        panic!(
            r#"unexpected duckdns response body, got: "{}".
This may happen because duckdns has changed the format of the response body and this implementation hasn't been updated, please report to the maintainers."#,
            body
        );
    }

    // TEST
    /*
    fn lets_surf(&self) -> Result<http_types::StatusCode, surf::Error> {
        task::block_on(async {
            // let req = self.http_cli.get("http://httpstat.us/500");
            let req = self.http_cli.get("http://ivan.fraixed.es");
            let code = req.await?.status();
            Ok(code)
        })
    }
    */
}

#[derive(Debug, PartialEq)]
enum ResponseBody {
    // Success indicates that the operation succeeded. When 'true' the operation
    // has made an update, when 'false' there was no update due to the sent
    // values were the same than the ones set.
    Success(bool),
    // Failed indicates that the operation failed.
    Failed,
}

#[cfg(test)]
mod test {
    use super::*;

    const TOKEN: &str = "this-is-my-token";

    #[test]
    fn new() {
        let u = Updater::new(TOKEN);
        assert_eq!(u.token, TOKEN);
    }

    #[test]
    fn update_record_a() {
        use async_std::task;

        // Check errors returned due to invalid parameters
        task::block_on(async {
            let err_invalid_args_tests = &[
            (
                (vec!["an_invalid_domain"], None, None),
                ("domains", 0_i64),
                "a domain name can only contain 'a-z', '0-9' and '-' case insensitive characters and must have at least one character",
                "invalid domain both IPs are none",
            ),
            (
                (
                    vec![],
                    None,
                    Some(net::Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1)),
                ),
                ("domains", -1),
                "domains cannot be empty, it must contain at least one domain name",
                "empty domain IPv4 is none",
            ),
            (
                (
                    vec!["valid-domain", "an_invalid_domain"],
                    Some(net::Ipv4Addr::new(0, 0, 0, 0)),
                    Some(net::Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1)),
                ),
                ("domains", 1),
                "a domain name can only contain 'a-z', '0-9' and '-' case insensitive characters and must have at least one character",
                "domains contain one invalid domain and IPs aren't None",
            ),
            (
                (vec!["some-domain"], None, None),
                ("ipv4,ipv6", -1),
                "at least one IP must be specified V4 or V6, both cannot be None",
                "both IPs are None",
            )];

            let updater = Updater::new(TOKEN);
            for (i, t) in err_invalid_args_tests.iter().enumerate() {
                if let Error::InvalidArguments(error::Args { names, msg }) = updater
                    .update_record_a((t.0).0.as_slice(), (t.0).1, (t.0).2)
                    .await
                    .expect_err(t.3)
                {
                    if (t.1).1 < 0 {
                        assert_eq!(names, String::from((t.1).0), "test: {}", i);
                    } else {
                        assert_eq!(names, format!("{}[{}]", (t.1).0, (t.1).1), "test: {}", i);
                    }

                    assert_eq!(msg, String::from(t.2));
                } else {
                    panic!("expected an invalid argument error");
                }
            }
        });

        task::block_on(async {
            let updater =
                Updater::new_with_base_url(TOKEN, "https://duckdns.test/update?verbose=true");
            if let Error::Network(err, retry) = updater
                .update_record_a(
                    &["a-valid-domain"],
                    Some(net::Ipv4Addr::new(0, 0, 0, 0)),
                    None,
                )
                .await
                .expect_err("network error expected for a domain that cannot be resolved")
            {
                if let Some(e) = err.source() {
                    match e.downcast_ref::<isahc::error::Error>() {
                        Some(isace) => {
                            assert_eq!(isace.is_network(), true);
                            assert_eq!(retry, false);
                        },
                        None => panic!("inner network error should be isach::error:Error"),
                    }
                } else {
                    panic!("network error should return a source error returned by the underlying network library");
                }
            } else {
                panic!("expected a network error");
            }
        });

        // import crates for HTTP server mocking
        use wiremock::matchers::{method, query_param};
        use wiremock::{Mock, MockServer, ResponseTemplate};

        // test when server returns 500 HTTP Status code
        task::block_on(async {
            let domain = "test-500";
            let ip = net::Ipv4Addr::new(1, 1, 1, 1);

            let server = MockServer::start().await;
            Mock::given(method("GET"))
                .and(query_param("domain", domain))
                .and(query_param("ip", ip.to_string()))
                .respond_with(ResponseTemplate::new(500))
                .mount(&server)
                .await;

            let uri = server.uri();
            let updater = Updater::new_with_base_url(TOKEN, &uri);
            if let Error::Provider(p) = updater
                .update_record_a(vec![domain].as_slice(), Some(ip), None)
                .await
                .expect_err("HTTP 500 status must return an error")
            {
                assert_eq!(
                    p,
                    error::Provider::Internal,
                    "expected provider internal error",
                );
            } else {
                panic!("expected a provider error");
            }
        });

        // test when server returns KO with 200 HTTP Status code
        task::block_on(async {
            let domain = "test-KO";
            let ip = net::Ipv4Addr::new(1, 1, 1, 1);

            let server = MockServer::start().await;
            Mock::given(method("GET"))
                .and(query_param("domain", domain))
                .and(query_param("ip", ip.to_string()))
                .respond_with(ResponseTemplate::new(200).set_body_string("KO"))
                .mount(&server)
                .await;

            let uri = server.uri();
            let updater = Updater::new_with_base_url(TOKEN, &uri);
            if let Error::Provider(p) = updater
                .update_record_a(vec![domain].as_slice(), Some(ip), None)
                .await
                .expect_err("HTTP 200  status with KO body message must return an error")
            {
                assert_eq!(
                    p,
                    error::Provider::Unspecified,
                    "expected provider unspecified error",
                );
            } else {
                panic!("expected a provider error");
            }
        });

        // tests when server return successful
        task::block_on(async {
            let domain = "test-OK";

            // Case: updating IP v4
            {
                let ip = net::Ipv4Addr::new(1, 1, 1, 1);
                let body = r"OK
1.1.1.1

UPDATED";
                let server = MockServer::start().await;
                Mock::given(method("GET"))
                    .and(query_param("domain", domain))
                    .and(query_param("ip", ip.to_string()))
                    .respond_with(ResponseTemplate::new(200).set_body_string(body))
                    .mount(&server)
                    .await;

                let uri = server.uri();
                let updater = Updater::new_with_base_url(TOKEN, &uri);
                let resp = updater
                    .update_record_a(vec![domain].as_slice(), Some(ip), None)
                    .await
                    .expect("HTTP 200 with OK message must return a Response");

                assert_eq!(
                    resp.is_updated(),
                    Some(true),
                    "expected a domain IP update option with true value"
                );
                assert_eq!(
                    resp.result_msg(),
                    body,
                    "expected plain text body to be the result message"
                );
            }

            // Case: updating IP v6
            {
                let ip = net::Ipv6Addr::new(0, 0, 0, 0, 0, 0xFFFF, 0x0101, 0x0101);
                let body = r"OK

0:0:0:0:0:FFFF:0101:0101
UPDATED";
                let server = MockServer::start().await;
                Mock::given(method("GET"))
                    .and(query_param("domain", domain))
                    .and(query_param("ipv6", ip.to_string()))
                    .respond_with(ResponseTemplate::new(200).set_body_string(body))
                    .mount(&server)
                    .await;

                let uri = server.uri();
                let updater = Updater::new_with_base_url(TOKEN, &uri);
                let resp = updater
                    .update_record_a(vec![domain].as_slice(), None, Some(ip))
                    .await
                    .expect("HTTP 200 with OK message must return a Response");

                assert_eq!(
                    resp.is_updated(),
                    Some(true),
                    "expected a domain IP update option with true value"
                );
                assert_eq!(
                    resp.result_msg(),
                    body,
                    "expected plain text body to be the result message"
                );
            }

            // Case: updating IP v4 and v6
            {
                let ipv4 = net::Ipv4Addr::new(1, 1, 1, 1);
                let ipv6 = net::Ipv6Addr::new(0, 0, 0, 0, 0, 0xFFFF, 0x0101, 0x0101);
                let body = r"OK
1.1.1.1
0:0:0:0:0:FFFF:0101:0101
UPDATED";
                let server = MockServer::start().await;
                Mock::given(method("GET"))
                    .and(query_param("domain", domain))
                    .and(query_param("ip", ipv4.to_string()))
                    .and(query_param("ipv6", ipv6.to_string()))
                    .respond_with(ResponseTemplate::new(200).set_body_string(body))
                    .mount(&server)
                    .await;

                let uri = server.uri();
                let updater = Updater::new_with_base_url(TOKEN, &uri);
                let resp = updater
                    .update_record_a(vec![domain].as_slice(), Some(ipv4), Some(ipv6))
                    .await
                    .expect("HTTP 200 with OK message must return a Response");

                assert_eq!(
                    resp.is_updated(),
                    Some(true),
                    "expected a domain IP update option with true value"
                );
                assert_eq!(
                    resp.result_msg(),
                    body,
                    "expected plain text body to be the result message"
                );
            }

            // Case: not updating IP v4
            {
                let ip = net::Ipv4Addr::new(1, 1, 1, 1);
                let body = r"OK
1.1.1.1

NOCHANGE";
                let server = MockServer::start().await;
                Mock::given(method("GET"))
                    .and(query_param("domain", domain))
                    .and(query_param("ip", ip.to_string()))
                    .respond_with(ResponseTemplate::new(200).set_body_string(body))
                    .mount(&server)
                    .await;

                let uri = server.uri();
                let updater = Updater::new_with_base_url(TOKEN, &uri);
                let resp = updater
                    .update_record_a(vec![domain].as_slice(), Some(ip), None)
                    .await
                    .expect("HTTP 200 with OK message must return a Response");

                assert_eq!(
                    resp.is_updated(),
                    Some(false),
                    "expected a domain IP update option with false value"
                );
                assert_eq!(
                    resp.result_msg(),
                    body,
                    "expected plain text body to be the result message"
                );
            }

            // Case: not updating IP v6
            {
                let ip = net::Ipv6Addr::new(0, 0, 0, 0, 0, 0xFFFF, 0x0101, 0x0101);
                let body = r"OK

0:0:0:0:0:FFFF:0101:0101
NOCHANGE";
                let server = MockServer::start().await;
                Mock::given(method("GET"))
                    .and(query_param("domain", domain))
                    .and(query_param("ipv6", ip.to_string()))
                    .respond_with(ResponseTemplate::new(200).set_body_string(body))
                    .mount(&server)
                    .await;

                let uri = server.uri();
                let updater = Updater::new_with_base_url(TOKEN, &uri);
                let resp = updater
                    .update_record_a(vec![domain].as_slice(), None, Some(ip))
                    .await
                    .expect("HTTP 200 with OK message must return a Response");

                assert_eq!(
                    resp.is_updated(),
                    Some(false),
                    "expected a domain IP update option with false value"
                );
                assert_eq!(
                    resp.result_msg(),
                    body,
                    "expected plain text body to be the result message"
                );
            }

            // Case: not updating IP v4 and v6
            {
                let ipv4 = net::Ipv4Addr::new(1, 1, 1, 1);
                let ipv6 = net::Ipv6Addr::new(0, 0, 0, 0, 0, 0xFFFF, 0x0101, 0x0101);
                let body = r"OK
1.1.1.1
0:0:0:0:0:FFFF:0101:0101
NOCHANGE";
                let server = MockServer::start().await;
                Mock::given(method("GET"))
                    .and(query_param("domain", domain))
                    .and(query_param("ip", ipv4.to_string()))
                    .and(query_param("ipv6", ipv6.to_string()))
                    .respond_with(ResponseTemplate::new(200).set_body_string(body))
                    .mount(&server)
                    .await;

                let uri = server.uri();
                let updater = Updater::new_with_base_url(TOKEN, &uri);
                let resp = updater
                    .update_record_a(vec![domain].as_slice(), Some(ipv4), Some(ipv6))
                    .await
                    .expect("HTTP 200 with OK message must return a Response");

                assert_eq!(
                    resp.is_updated(),
                    Some(false),
                    "expected a domain IP update option with false value"
                );
                assert_eq!(
                    resp.result_msg(),
                    body,
                    "expected plain text body to be the result message"
                );
            }
        });
    }

    #[test]
    fn domains_as_param() {
        let ok_tests = &[
            (
                vec!["one-valid-domain"],
                "one-valid-domain",
                "domains contain one single valid domain",
            ),
            (
                vec!["valid-domain-1", "valid-domain-2", "valid-domain-3"],
                "valid-domain-1,valid-domain-2,valid-domain-3",
                "domains contain one single valid domain",
            ),
        ];

        for (i, t) in ok_tests.iter().enumerate() {
            let p = Updater::domains_as_param(t.0.as_slice()).expect(t.2);
            assert_eq!(p.0, "domains", "test: {}", i);
            assert_eq!(p.1, String::from(t.1), "test: {}", i);
        }

        let err_tests = &[
            (
                vec![],
                -1,
                "domains cannot be empty, it must contain at least one domain name",
                "domains is empty",
            ),
            (
                vec!["this is invalid"],
                0,
                "a domain name can only contain 'a-z', '0-9' and '-' case insensitive characters and must have at least one character",
                "domains contain one single incorrect domain",
            ),
            (
                vec!["valid-domain-1", "valid-domain-2", "this is invalid"],
                2,
                "a domain name can only contain 'a-z', '0-9' and '-' case insensitive characters and must have at least one character",
                "3 domains the the third is invalid",
            ),
            (
                vec!["no valid", "1", "2", "3"],
                0,
                "a domain name can only contain 'a-z', '0-9' and '-' case insensitive characters and must have at least one character",
                "4 domains the the first is invalid",
            ),
            (
                vec!["a", "b", "", "c", "d"],
                2,
                "a domain name can only contain 'a-z', '0-9' and '-' case insensitive characters and must have at least one character",
                "5 domains the the third is invalid",
            ),
            ];

        for (i, t) in err_tests.iter().enumerate() {
            if let Error::InvalidArguments(error::Args { names, msg }) =
                Updater::domains_as_param(t.0.as_slice()).expect_err(t.3)
            {
                if t.1 < 0 {
                    assert_eq!(names, String::from("domains"), "test: {}", i);
                } else {
                    assert_eq!(names, format!("domains[{}]", t.1), "test: {}", i);
                }

                assert_eq!(msg, String::from(t.2));
            } else {
                panic!("expected an invalid argument error");
            }
        }
    }

    #[test]
    fn validate_domain() {
        Updater::validate_domain("this-is-valid").expect("'this-is-valid' is a valid domain name");
        Updater::validate_domain("THIS-is-Valid").expect("'THIS-is-Valid' is a valid domain name");
        Updater::validate_domain("5451851").expect("'5451851' is a valid domain name");
        Updater::validate_domain("lettersAnd153").expect("'lettersAnd153' is a valid domain name");
        Updater::validate_domain("letters-99").expect("'letters-99' is a valid domain name");

        for (i, val) in ["", "spaces are invalid", "underscores_are_invalid"]
            .iter()
            .enumerate()
        {
            if let Error::InvalidArguments(error::Args { names, msg }) =
                Updater::validate_domain(val).expect_err("empty string is an invalid domain name")
            {
                assert_eq!(names, String::from("domain"), "test: {}", i);
                assert_eq!( msg,
                            String::from("a domain name can only contain 'a-z', '0-9' and '-' case insensitive characters and must have at least one character"),
                            "test: {}", i,
                        );
            } else {
                panic!("expected an invalid argument error");
            }
        }
    }

    #[test]
    fn parse_response_body() {
        let tests = &[
            (
                r"OK


UPDATED",
                ResponseBody::Success(true),
            ),
            (
                r"OK
1.1.1.1

UPDATED",
                ResponseBody::Success(true),
            ),
            (
                r"OK

2002:DB7::21f:5bff:febf:ce22:8a2e
UPDATED",
                ResponseBody::Success(true),
            ),
            (
                r"OK
7.7.7.7
2606:4700:4700::1111,2606:4700:4700::1001
UPDATED",
                ResponseBody::Success(true),
            ),
            (
                r"OK


NOCHANGE",
                ResponseBody::Success(false),
            ),
            (
                r"OK
5.2.150.6

NOCHANGE",
                ResponseBody::Success(false),
            ),
            (
                r"OK

0:0:0:0:0:FFFF:6419:2306
NOCHANGE",
                ResponseBody::Success(false),
            ),
            (
                r"OK
100.25.35.6
0:0:4700:0:0:FFFF:0119:2306
NOCHANGE",
                ResponseBody::Success(false),
            ),
            (
                r"OK
100.25.35.6
0:0:4700:0:0:FFFF:0119:2306
NOCHANGE",
                ResponseBody::Success(false),
            ),
            ("KO", ResponseBody::Failed),
        ];

        for (i, t) in tests.iter().enumerate() {
            let r = Updater::parse_response_body(t.0);
            assert_eq!(r, t.1);
        }
    }

    #[test]
    #[should_panic(
        expected = "unexpected duckdns response body, got: \"NOTGOOD\n100.25.35.6\n0:0:4700:0:0:FFFF:0119:2306\nNOCHANGE\".\nThis may happen because duckdns has changed the format of the response body and this implementation hasn't been updated, please report to the maintainers."
    )]
    fn parse_response_body_unexpected_operation() {
        let body = r"NOTGOOD
100.25.35.6
0:0:4700:0:0:FFFF:0119:2306
NOCHANGE";
        Updater::parse_response_body(body);
    }

    #[test]
    #[should_panic(
        expected = "unexpected duckdns response body, got: \"OK\n100.25.35.6\n0:0:4700:0:0:FFFF:0119:2306\".\nThis may happen because duckdns has changed the format of the response body and this implementation hasn't been updated, please report to the maintainers."
    )]
    fn parse_response_body_unexpected_change_status() {
        let body = r"OK
100.25.35.6
0:0:4700:0:0:FFFF:0119:2306";
        Updater::parse_response_body(body);
    }

    #[test]
    #[should_panic(
        expected = "unexpected duckdns response body, got: \"OK,100.25.35.6,0:0:4700:0:0:FFFF:0119:2306,NOCHANGE\".\nThis may happen because duckdns has changed the format of the response body and this implementation hasn't been updated, please report to the maintainers."
    )]
    fn parse_response_body_unexpected_response_body() {
        let body = "OK,100.25.35.6,0:0:4700:0:0:FFFF:0119:2306,NOCHANGE";
        Updater::parse_response_body(body);
    }

    /*
        #[test]
        fn surf() {
            let u = Updater::new(TOKEN);
            /*
               let code = u.lets_surf().unwrap(); //_or_else(|error| println!("{}", error));
               assert_eq!(http_types::StatusCode::InternalServerError, code)
            */
            match u.lets_surf() {
                Ok(code) => println!("code: {}", code),
                Err(e) => println!("error: {}", e),
            };
        }
    */
}
