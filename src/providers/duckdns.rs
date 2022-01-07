//! Implementation for using with Duck DNS services.

use super::error::Error;
use super::Response;
use crate::error::{Args as ErrArgs, BoxError, Error as ErrorCommon, ExternalService, NetworkSide};

use std::net;

use isahc::AsyncReadResponseExt;
use lazy_static::lazy_static;
use regex::Regex;
use url::Url;

/// The DNS update for the Duck DNS provider.
pub struct Updater<'a> {
    /// The authorization API token.
    token: &'a str,
    /// The API base URL to use.
    base_url: &'a str,
    /// The HTTP client that the instance use for making the requests.
    http_cli: isahc::HttpClient,
}

impl<'a> Updater<'a> {
    /// Creates a Duck DNS updater using the specified API token.
    pub fn new(token: &'a str) -> Self {
        Self::with_base_url(token, "https://www.duckdns.org/update?verbose=true")
    }

    /// Creates a Duck DNS updater using the specified API token and base URL.
    /// This constructor is mainly useful for testing purposes.
    fn with_base_url(token: &'a str, base_url: &'a str) -> Self {
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

    /// Updates the A DNS record for the passed domains to the passed IP V4 and
    /// V6.
    /// At least one domain must be passed and IP V4 or V6 or both, otherwise
    /// an `Error:InvalidArguments` is returned.
    /// Valid domains are case-insensitive and can only contains letters (A-Z),
    /// numbers (0-9), and dashes (-).
    pub async fn update_record_a<'b>(
        &self,
        domains: &[&str],
        ipv4: Option<net::Ipv4Addr>,
        ipv6: Option<net::Ipv6Addr>,
    ) -> Result<Response, Error<'b>> {
        let mut params = Vec::with_capacity(3);
        params.push(Self::domains_as_param(domains)?);

        if ipv4.is_none() && ipv6.is_none() {
            return Err(Error::Common(ErrorCommon::invalid_arguments(
                "(ipv4,ipv6)",
                "at least one IP (V4 or V6) must be specified, both cannot be None",
            )));
        }

        if let Some(ip) = ipv4 {
            params.push(("ip", ip.to_string()))
        }

        if let Some(ip) = ipv6 {
            params.push(("ipv6", ip.to_string()))
        }

        let url = Url::parse_with_params(self.base_url, params)
            .expect("Failed to parse base URL with domains names due to a bug");

        let mut response = self
            .http_cli
            .get_async(url.as_str())
            .await
            .map_err(Error::from_isahc)?;

        if !response.status().is_success() {
            if response.status().is_server_error() {
                return Err(Error::Provider(ExternalService::Internal {
                    reason: format!(
                        r#"Duck DNS service has responded with an HTTP "{}" status code (expected 200)"#,
                        response.status(),
                    ),
                }));
            }

            if response.status() == http::StatusCode::BAD_REQUEST {
                return Err(Error::Common(ErrorCommon::network(
                    BoxError::from(
                        r#"Duck DNS service has returned "400 Bad Request" HTTP status code"#,
                    ),
                    NetworkSide::Client,
                    true,
                )));
            }

            panic!("BUG (please report it): this implementation is outdated, the external service has changed its public API.");
        }

        let body = response.text().await.map_err(|err| {
            Error::Common(ErrorCommon::internal(
                "error while reading the response body as text",
                BoxError::from(err),
            ))
        })?;

        match Self::parse_response_body(&body) {
            ResponseBody::Success(updated) => Ok(Response {
                updated: Some(updated),
            }),
            ResponseBody::Failed => Err(Error::Provider(ExternalService::Unspecified)),
        }
    }

    /// Convert the list of domains to a valid string for sending it to Duck
    /// DNS.
    fn domains_as_param<'b, 'c>(domains: &'b [&str]) -> Result<(&'static str, String), Error<'c>> {
        if domains.is_empty() {
            return Err(Error::Common(ErrorCommon::invalid_arguments(
                "domains",
                "domains cannot be empty, it must contain at least one domain name",
            )));
        }

        match Self::validate_domain(domains[0]) {
            Err(Error::Common(ErrorCommon::InvalidArguments(ErrArgs { msg, .. }))) => {
                return Err(Error::Common(ErrorCommon::invalid_arguments(
                    "domains[0]",
                    &msg,
                )));
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
                    Err(Error::Common(ErrorCommon::InvalidArguments(ErrArgs { msg, .. }))) => {
                        Err(Error::Common(ErrorCommon::invalid_arguments(
                            &format!("domains[{}]", idx),
                            &msg,
                        )))
                    }
                    Err(e) => panic!("Self::validate_domain returned an unexpected error: {}", e),
                },
            )?;

        Ok(("domains", val))
    }

    /// Check if domain is a valid Duck DNS name.
    /// A valid domain is case-insensitive and can only contains letters (A-Z),
    /// numbers (0-9), and dashes (-).
    fn validate_domain(domain: &str) -> Result<(), Error> {
        lazy_static! {
            static ref RE: Regex = Regex::new(r"(?i)^[a-z0-9\-]+$").unwrap();
        }

        if !RE.is_match(domain) {
            return Err(
                Error::Common(ErrorCommon::invalid_arguments(
                    "domain",
                    "a domain name can only contain 'a-z', '0-9' and '-' case insensitive characters and must have at least one character",
                )),
            );
        }

        Ok(())
    }

    /// Parse the response body according Duck DNS expected format.
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
            r#"unexpected Duck DNS response body, got: "{}".
This may happen because Duck DNS has changed the format of the response body and this implementation hasn't been updated, please report to the maintainers."#,
            body
        );
    }
}

/// Indicates that the request to DuckDNS responded with a 2XX HTTP code was
/// successful or not based on the content of the response body.
#[derive(Debug, PartialEq)]
enum ResponseBody {
    /// Success indicates that the operation succeeded. When 'true' the operation
    /// has made an update, when 'false' there was no update due to the sent
    /// values were the same than the ones set.
    Success(bool),
    /// Failed indicates that the operation failed.
    Failed,
}

#[cfg(test)]
mod test {
    use super::*;

    use std::error::Error as StdError;

    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};
    use tokio;
    use wiremock::matchers::{method, query_param};
    use wiremock::{Mock, MockServer, ResponseTemplate};

    const TOKEN: &str = "this-is-my-token";

    #[test]
    fn test_new() {
        let u = Updater::new(TOKEN);
        assert_eq!(u.token, TOKEN);
    }

    #[tokio::test]
    async fn test_update_record_a_invalid_params() {
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
                ("(ipv4,ipv6)", -1),
                "at least one IP (V4 or V6) must be specified, both cannot be None",
                "both IPs are None",
            )];

        let updater = Updater::new(TOKEN);
        for (i, t) in err_invalid_args_tests.iter().enumerate() {
            if let Error::Common(ErrorCommon::InvalidArguments(ErrArgs { names, msg })) = updater
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
                panic!("expected an invalid argument error in test case: {}", i);
            }
        }
    }

    #[tokio::test]
    async fn test_update_record_a_domain_do_not_resolve() {
        let updater = Updater::with_base_url(TOKEN, "https://duckdns.test/update?verbose=true");
        let err = updater
            .update_record_a(
                &["a-valid-domain"],
                Some(net::Ipv4Addr::new(0, 0, 0, 0)),
                None,
            )
            .await
            .expect_err("network error expected for a domain that cannot be resolved");

        if let Error::Common(ErrorCommon::Network(err_net)) = err {
            use crate::error::NetworkSide;
            use std::error::Error;

            println!("{:?}", err_net.source());
            assert_eq!(
                NetworkSide::Client,
                err_net.side,
                "requesting an invalid domain should return a client side error"
            );
            assert!(!err_net.should_retry, "requesting an invalid domain should return an error with should retry set to false");
        } else {
            panic!("expected a network error");
        }
    }

    #[tokio::test]
    #[should_panic(
        expected = "BUG (please report it): this implementation is outdated, the external service has changed its public API."
    )]
    async fn test_update_record_a_response_3xx() {
        let domain = "test-3xx";
        let ip = net::Ipv4Addr::new(1, 1, 1, 1);

        let mut rng = SmallRng::from_entropy();
        let status_code = rng.gen_range(300..=304);

        let server = MockServer::start().await;
        Mock::given(method("GET"))
            .and(query_param("domains", domain))
            .and(query_param("ip", ip.to_string()))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server)
            .await;

        let uri = server.uri();
        let updater = Updater::with_base_url(TOKEN, &uri);
        let _ = updater
            .update_record_a(vec![domain].as_slice(), Some(ip), None)
            .await;
    }

    #[tokio::test]
    async fn test_update_record_a_response_400() {
        let domain = "test-400";
        let ip = net::Ipv4Addr::new(1, 1, 1, 1);

        let server = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(400))
            .mount(&server)
            .await;

        let uri = &server.uri();
        let updater = Updater::with_base_url(TOKEN, &uri);
        if let Error::Common(ErrorCommon::Network(details)) = updater
            .update_record_a(vec![domain].as_slice(), Some(ip), None)
            .await
            .expect_err("HTTP 400 must return an error")
        {
            assert_eq!(details.side, NetworkSide::Client, "network side");
            assert!(details.should_retry, "should retry");
            assert_eq!(
                r#"Duck DNS service has returned "400 Bad Request" HTTP status code"#,
                format!(
                    "{}",
                    details.source().expect("Inner error must not be None")
                ),
                "expected finder internal error"
            );
        } else {
            panic!("expected a finder error")
        }
    }

    #[tokio::test]
    #[should_panic(
        expected = "BUG (please report it): this implementation is outdated, the external service has changed its public API."
    )]
    async fn test_update_record_a_response_4xx() {
        let domain = "test-4xx";
        let ip = net::Ipv4Addr::new(1, 1, 1, 1);

        let mut rng = SmallRng::from_entropy();
        let status_code = rng.gen_range(401..=409);

        let server = MockServer::start().await;
        Mock::given(method("GET"))
            .and(query_param("domains", domain))
            .and(query_param("ip", ip.to_string()))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server)
            .await;

        let uri = server.uri();
        let updater = Updater::with_base_url(TOKEN, &uri);
        let _ = updater
            .update_record_a(vec![domain].as_slice(), Some(ip), None)
            .await;
    }

    #[tokio::test]
    async fn test_update_record_a_response_5xx() {
        let domain = "test-500";
        let ip = net::Ipv4Addr::new(1, 1, 1, 1);

        let mut rng = SmallRng::from_entropy();
        let status_code = rng.gen_range(500..=508);

        let server = MockServer::start().await;
        Mock::given(method("GET"))
            .and(query_param("domains", domain))
            .and(query_param("ip", ip.to_string()))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server)
            .await;

        let uri = server.uri();
        let updater = Updater::with_base_url(TOKEN, &uri);
        if let Error::Provider(ExternalService::Internal { reason }) = updater
            .update_record_a(vec![domain].as_slice(), Some(ip), None)
            .await
            .expect_err("HTTP 500 status must return an error")
        {
            assert_eq!(
                reason,
                format!(
                    r#"Duck DNS service has responded with an HTTP "{}" status code (expected 200)"#,
                    http::StatusCode::from_u16(status_code).unwrap(),
                ),
                "expected provider internal error",
            );
        } else {
            panic!("expected a provider internal error");
        }
    }

    #[tokio::test]
    async fn test_update_record_a_response_200_ko() {
        let domain = "test-KO";
        let ip = net::Ipv4Addr::new(1, 1, 1, 1);

        let server = MockServer::start().await;
        Mock::given(method("GET"))
            .and(query_param("domains", domain))
            .and(query_param("ip", ip.to_string()))
            .respond_with(ResponseTemplate::new(200).set_body_string("KO"))
            .mount(&server)
            .await;

        let uri = server.uri();
        let updater = Updater::with_base_url(TOKEN, &uri);
        if let Error::Provider(p) = updater
            .update_record_a(vec![domain].as_slice(), Some(ip), None)
            .await
            .expect_err("HTTP 200  status with KO body message must return an error")
        {
            match p {
                ExternalService::Unspecified => {}
                _ => panic!("expected a provider unspecified error"),
            };
        } else {
            panic!("expected a provider error");
        }
    }

    #[tokio::test]
    async fn test_update_record_a_response_200_ok() {
        let domain = "test-OK";

        // Case: updating IP v4
        {
            let ip = net::Ipv4Addr::new(1, 1, 1, 1);
            let body = format!("{}\n{}\n\n{}", "OK", "1.1,1.1", "UPDATED");
            let server = MockServer::start().await;
            Mock::given(method("GET"))
                .and(query_param("domains", domain))
                .and(query_param("ip", ip.to_string()))
                .respond_with(ResponseTemplate::new(200).set_body_string(body))
                .mount(&server)
                .await;

            let uri = server.uri();
            let updater = Updater::with_base_url(TOKEN, &uri);
            let resp = updater
                .update_record_a(vec![domain].as_slice(), Some(ip), None)
                .await
                .expect("HTTP 200 with OK message must return a Response");

            assert_eq!(
                resp.is_updated(),
                Some(true),
                "expected a domain IP update option with true value"
            );
        }

        // Case: updating IP v6
        {
            let ip = net::Ipv6Addr::new(0, 0, 0, 0, 0, 0xFFFF, 0x0101, 0x0101);
            let body = format!("{}\n\n{}\n{}", "OK", "0:0:0:0:0:FFFF:0101:0101", "UPDATED");
            let server = MockServer::start().await;
            Mock::given(method("GET"))
                .and(query_param("domains", domain))
                .and(query_param("ipv6", ip.to_string()))
                .respond_with(ResponseTemplate::new(200).set_body_string(body))
                .mount(&server)
                .await;

            let uri = server.uri();
            let updater = Updater::with_base_url(TOKEN, &uri);
            let resp = updater
                .update_record_a(vec![domain].as_slice(), None, Some(ip))
                .await
                .expect("HTTP 200 with OK message must return a Response");

            assert_eq!(
                resp.is_updated(),
                Some(true),
                "expected a domain IP update option with true value"
            );
        }

        // Case: updating IP v4 and v6
        {
            let ipv4 = net::Ipv4Addr::new(1, 1, 1, 1);
            let ipv6 = net::Ipv6Addr::new(0, 0, 0, 0, 0, 0xFFFF, 0x0101, 0x0101);
            let body = format!(
                "{}\n{}\n{}\n{}",
                "OK", "1.1,1.1", "0:0:0:0:0:FFFF:0101:0101", "UPDATED"
            );
            let server = MockServer::start().await;
            Mock::given(method("GET"))
                .and(query_param("domains", domain))
                .and(query_param("ip", ipv4.to_string()))
                .and(query_param("ipv6", ipv6.to_string()))
                .respond_with(ResponseTemplate::new(200).set_body_string(body))
                .mount(&server)
                .await;

            let uri = server.uri();
            let updater = Updater::with_base_url(TOKEN, &uri);
            let resp = updater
                .update_record_a(vec![domain].as_slice(), Some(ipv4), Some(ipv6))
                .await
                .expect("HTTP 200 with OK message must return a Response");

            assert_eq!(
                resp.is_updated(),
                Some(true),
                "expected a domain IP update option with true value"
            );
        }

        // Case: not updating IP v4
        {
            let ip = net::Ipv4Addr::new(1, 1, 1, 1);
            let body = format!("{}\n{}\n\n{}", "OK", "1.1,1.1", "NOCHANGE");
            let server = MockServer::start().await;
            Mock::given(method("GET"))
                .and(query_param("domains", domain))
                .and(query_param("ip", ip.to_string()))
                .respond_with(ResponseTemplate::new(200).set_body_string(body))
                .mount(&server)
                .await;

            let uri = server.uri();
            let updater = Updater::with_base_url(TOKEN, &uri);
            let resp = updater
                .update_record_a(vec![domain].as_slice(), Some(ip), None)
                .await
                .expect("HTTP 200 with OK message must return a Response");

            assert_eq!(
                resp.is_updated(),
                Some(false),
                "expected a domain IP update option with false value"
            );
        }

        // Case: not updating IP v6
        {
            let ip = net::Ipv6Addr::new(0, 0, 0, 0, 0, 0xFFFF, 0x0101, 0x0101);
            let body = format!("{}\n\n{}\n{}", "OK", "0:0:0:0:0:FFFF:0101:0101", "NOCHANGE");
            let server = MockServer::start().await;
            Mock::given(method("GET"))
                .and(query_param("domains", domain))
                .and(query_param("ipv6", ip.to_string()))
                .respond_with(ResponseTemplate::new(200).set_body_string(body))
                .mount(&server)
                .await;

            let uri = server.uri();
            let updater = Updater::with_base_url(TOKEN, &uri);
            let resp = updater
                .update_record_a(vec![domain].as_slice(), None, Some(ip))
                .await
                .expect("HTTP 200 with OK message must return a Response");

            assert_eq!(
                resp.is_updated(),
                Some(false),
                "expected a domain IP update option with false value"
            );
        }

        // Case: not updating IP v4 and v6
        {
            let ipv4 = net::Ipv4Addr::new(1, 1, 1, 1);
            let ipv6 = net::Ipv6Addr::new(0, 0, 0, 0, 0, 0xFFFF, 0x0101, 0x0101);
            let body = format!(
                "{}\n{}\n{}\n{}",
                "OK", "1.1,1.1", "0:0:0:0:0:FFFF:0101:0101", "NOCHANGE"
            );
            let server = MockServer::start().await;
            Mock::given(method("GET"))
                .and(query_param("domains", domain))
                .and(query_param("ip", ipv4.to_string()))
                .and(query_param("ipv6", ipv6.to_string()))
                .respond_with(ResponseTemplate::new(200).set_body_string(body))
                .mount(&server)
                .await;

            let uri = server.uri();
            let updater = Updater::with_base_url(TOKEN, &uri);
            let resp = updater
                .update_record_a(vec![domain].as_slice(), Some(ipv4), Some(ipv6))
                .await
                .expect("HTTP 200 with OK message must return a Response");

            assert_eq!(
                resp.is_updated(),
                Some(false),
                "expected a domain IP update option with false value"
            );
        }
    }

    #[test]
    fn test_domains_as_param() {
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
            if let Error::Common(ErrorCommon::InvalidArguments(ErrArgs { names, msg })) =
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
    fn test_validate_domain() {
        Updater::validate_domain("this-is-valid").expect("'this-is-valid' is a valid domain name");
        Updater::validate_domain("THIS-is-Valid").expect("'THIS-is-Valid' is a valid domain name");
        Updater::validate_domain("5451851").expect("'5451851' is a valid domain name");
        Updater::validate_domain("lettersAnd153").expect("'lettersAnd153' is a valid domain name");
        Updater::validate_domain("letters-99").expect("'letters-99' is a valid domain name");

        for (i, val) in ["", "spaces are invalid", "underscores_are_invalid"]
            .iter()
            .enumerate()
        {
            if let Error::Common(ErrorCommon::InvalidArguments(ErrArgs { names, msg })) =
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
    fn test_parse_response_body() {
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

        for (_, t) in tests.iter().enumerate() {
            let r = Updater::parse_response_body(t.0);
            assert_eq!(r, t.1);
        }
    }

    #[test]
    #[should_panic(
        expected = "unexpected Duck DNS response body, got: \"NOTGOOD\n100.25.35.6\n0:0:4700:0:0:FFFF:0119:2306\nNOCHANGE\".\nThis may happen because Duck DNS has changed the format of the response body and this implementation hasn't been updated, please report to the maintainers."
    )]
    fn test_parse_response_body_unexpected_operation() {
        let body = r"NOTGOOD
100.25.35.6
0:0:4700:0:0:FFFF:0119:2306
NOCHANGE";
        Updater::parse_response_body(body);
    }

    #[test]
    #[should_panic(
        expected = "unexpected Duck DNS response body, got: \"OK\n100.25.35.6\n0:0:4700:0:0:FFFF:0119:2306\".\nThis may happen because Duck DNS has changed the format of the response body and this implementation hasn't been updated, please report to the maintainers."
    )]
    fn test_parse_response_body_unexpected_change_status() {
        let body = r"OK
100.25.35.6
0:0:4700:0:0:FFFF:0119:2306";
        Updater::parse_response_body(body);
    }

    #[test]
    #[should_panic(
        expected = "unexpected Duck DNS response body, got: \"OK,100.25.35.6,0:0:4700:0:0:FFFF:0119:2306,NOCHANGE\".\nThis may happen because Duck DNS has changed the format of the response body and this implementation hasn't been updated, please report to the maintainers."
    )]
    fn test_parse_response_body_unexpected_response_body() {
        let body = "OK,100.25.35.6,0:0:4700:0:0:FFFF:0119:2306,NOCHANGE";
        Updater::parse_response_body(body);
    }
}
