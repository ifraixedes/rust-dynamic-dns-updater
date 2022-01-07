//! Implementation for using with "ipify" services.

use super::Error;
use crate::error::{BoxError, Error as ErrorCommon, ExternalService, NetworkSide};

use std::{
    net::{Ipv4Addr, Ipv6Addr},
    str::FromStr,
};

use isahc::AsyncReadResponseExt;

/// The public IP finder for the "ipify" provider.
pub struct Finder<'a> {
    /// The API base URL to request the public IP V4.
    base_url_v4: &'a str,
    /// The API base URL to request the public IP V6.
    base_url_v6: &'a str,
    /// The HTTP client that the instance use for making the requests.
    http_cli: isahc::HttpClient,
}

impl<'a> Finder<'a> {
    /// Creates an "ipify" finder.
    pub fn new() -> Self {
        Self::with_base_url("https://api.ipify.org", "https://api64.ipify.org")
    }

    /// Creates an "ipify" finder using the specified base URL.
    /// This constructor is mainly useful for testing purposes.
    fn with_base_url(base_url_v4: &'a str, base_url_v6: &'a str) -> Self {
        let http_cli = isahc::HttpClientBuilder::new()
            .max_connections(2)
            .connection_cache_size(2)
            .connection_cache_ttl(std::time::Duration::from_secs(5))
            .build()
            .expect("HTTP client initialization error, this due to a bug in this crate, please report it");

        Self {
            base_url_v4,
            base_url_v6,
            http_cli,
        }
    }

    /// Gets the IP V4 public IP where the machines is running behind.
    pub async fn ipv4<'b>(&self) -> Result<Ipv4Addr, Error<'b>> {
        let mut response = self.send_request(self.base_url_v4).await?;
        let body = response.text().await.map_err(|err| {
            Error::Common(ErrorCommon::internal(
                "error while reading the response body as text",
                BoxError::from(err),
            ))
        })?;

        Ok(Ipv4Addr::from_str(&body).unwrap_or_else(|_| panic!(
                r#"BUG (please report it). Unexpected ipify response body for IP v4, got: "{}".
This may have happened because ipify has changed the format of the response body and this implementation hasn't been updated."#,
        body)))
    }

    /// Gets the IP V6 public IP where the machines is running behind.
    pub async fn ipv6<'b>(&self) -> Result<Ipv6Addr, Error<'b>> {
        let mut response = self.send_request(self.base_url_v6).await?;
        let body = response.text().await.map_err(|err| {
            Error::Common(ErrorCommon::internal(
                "error while reading the response body as text",
                BoxError::from(err),
            ))
        })?;

        Ok(Ipv6Addr::from_str(&body).unwrap_or_else(|_| panic!(
                r#"BUG (please report it). Unexpected ipify response body for IP v6, got: "{}".
This may have happened because ipify has changed the format of the response body and this implementation hasn't been updated."#,
        body)))
    }

    /// Gets the IP V4 & V6 public IPs where the machines is running behind.
    pub async fn ips<'b>(&self) -> Result<(Ipv4Addr, Ipv6Addr), Error<'b>> {
        let (ipv4, ipv6) = tokio::join!(self.ipv4(), self.ipv6());

        if let Err(e) = ipv4 {
            return Err(e);
        }

        if let Err(e) = ipv6 {
            return Err(e);
        }

        Ok((ipv4.unwrap(), ipv6.unwrap()))
    }

    /// Sends a request to `url` and map errors and some response HTTP status
    /// codes to errors according the ipify API.
    async fn send_request<'b>(
        &self,
        url: &str,
    ) -> Result<isahc::Response<isahc::AsyncBody>, Error<'b>> {
        let response = self
            .http_cli
            .get_async(url)
            .await
            .map_err(Error::from_isahc)?;

        if response.status() != http::StatusCode::OK {
            if response.status().is_server_error() {
                return Err(Error::Finder(ExternalService::Internal {
                    reason: format!(
                        r#"ipify service has responded with an HTTP "{}" status code (expected 200)"#,
                        response.status(),
                    ),
                }));
            }

            if response.status() == http::StatusCode::BAD_REQUEST {
                return Err(Error::Common(ErrorCommon::network(
                    BoxError::from(
                        r#"ipify service has returned "400 Bad Request" HTTP status code"#,
                    ),
                    NetworkSide::Client,
                    true,
                )));
            }

            panic!("BUG (please report it): this implementation is outdated, the external service has changed its public API.");
        }

        Ok(response)
    }
}

impl Default for Finder<'_> {
    fn default() -> Self {
        Finder::new()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use std::error::Error as StdError;

    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};
    use tokio;
    use wiremock::matchers::method;
    use wiremock::{Mock, MockServer, ResponseTemplate};

    #[tokio::test]
    async fn test_ipv4_200() {
        let expected_ip = Ipv4Addr::new(1, 1, 1, 1);
        let server = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(200).set_body_string(expected_ip.to_string()))
            .mount(&server)
            .await;

        let uri = &server.uri();
        let finder = Finder::with_base_url(uri, uri);
        let ip = finder.ipv4().await.expect("HTTP 200 must return the IP");
        assert_eq!(ip, expected_ip, "unexpected returned IP");
    }

    #[tokio::test]
    #[should_panic(
        expected = r#"BUG (please report it). Unexpected ipify response body for IP v4, got: "1.1.1".
This may have happened because ipify has changed the format of the response body and this implementation hasn't been updated."#
    )]
    async fn test_ipv4_200_invalid_ip_format() {
        let server = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(200).set_body_string("1.1.1"))
            .mount(&server)
            .await;

        let uri = &server.uri();
        let finder = Finder::with_base_url(uri, uri);
        let _ = finder.ipv4().await;
    }

    #[tokio::test]
    #[should_panic(
        expected = "BUG (please report it): this implementation is outdated, the external service has changed its public API."
    )]
    async fn test_ipv4_3xx() {
        let mut rng = SmallRng::from_entropy();
        let status_code = rng.gen_range(300..=304);
        let server = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server)
            .await;

        let uri = &server.uri();
        let finder = Finder::with_base_url(uri, uri);
        let _ = finder.ipv4().await;
    }

    #[tokio::test]
    async fn test_ipv4_400() {
        let server = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(400))
            .mount(&server)
            .await;

        let uri = &server.uri();
        let finder = Finder::with_base_url(uri, uri);
        if let Error::Common(ErrorCommon::Network(details)) = finder
            .ipv4()
            .await
            .expect_err("HTTP 400 must return an error")
        {
            assert_eq!(details.side, NetworkSide::Client, "network side");
            assert!(details.should_retry, "should retry");
            assert_eq!(
                r#"ipify service has returned "400 Bad Request" HTTP status code"#,
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
    async fn test_ipv4_4xx() {
        let mut rng = SmallRng::from_entropy();
        let status_code = rng.gen_range(401..=409);
        let server = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server)
            .await;

        let uri = &server.uri();
        let finder = Finder::with_base_url(uri, uri);
        let _ = finder.ipv4().await;
    }

    #[tokio::test]
    async fn test_ipv4_5xx() {
        let mut rng = SmallRng::from_entropy();
        let status_code = rng.gen_range(500..=508);
        let server = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server)
            .await;

        let uri = &server.uri();
        let finder = Finder::with_base_url(uri, uri);
        if let Error::Finder(ExternalService::Internal { reason }) = finder
            .ipv4()
            .await
            .expect_err("HTTP 5XX must return an error")
        {
            assert_eq!(
                reason,
                format!(
                    r#"ipify service has responded with an HTTP "{}" status code (expected 200)"#,
                    http::StatusCode::from_u16(status_code).unwrap(),
                ),
                "expected finder internal error"
            );
        } else {
            panic!("expected a finder internal error")
        }
    }

    #[tokio::test]
    async fn test_ipv4_domain_do_not_resolve() {
        let finder = Finder::with_base_url("https://ipify.test", "https://ipify.test");
        let err = finder
            .ipv4()
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
    async fn test_ipv6_200() {
        let expected_ip = Ipv6Addr::new(0, 0, 0, 0, 0, 0xFFFF, 0x0101, 0x0101);
        let server = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(200).set_body_string(expected_ip.to_string()))
            .mount(&server)
            .await;

        let uri = &server.uri();
        let finder = Finder::with_base_url(uri, uri);
        let ip = finder.ipv6().await.expect("HTTP 200 must return the IP");
        assert_eq!(ip, expected_ip, "unexpected returned IP");
    }

    #[tokio::test]
    #[should_panic(
        expected = r#"BUG (please report it). Unexpected ipify response body for IP v6, got: "0::0XFFFFF".
This may have happened because ipify has changed the format of the response body and this implementation hasn't been updated."#
    )]
    async fn test_ipv6_200_invalid_ip_format() {
        let server = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(200).set_body_string("0::0XFFFFF"))
            .mount(&server)
            .await;

        let uri = &server.uri();
        let finder = Finder::with_base_url(uri, uri);
        if let Error::Finder(ExternalService::Internal { reason }) = finder
            .ipv6()
            .await
            .expect_err("HTTP 200 with a malformed IP")
        {
            assert_eq!(
                reason,
                "ipify service has responded with a 200 HTTP status code but '0::0XFFFFF' is not a valid IP ",
                "expected finder internal error"
            );
        } else {
            panic!("expected a finder internal error")
        }
    }

    #[tokio::test]
    #[should_panic(
        expected = "BUG (please report it): this implementation is outdated, the external service has changed its public API."
    )]
    async fn test_ipv6_3xx() {
        let mut rng = SmallRng::from_entropy();
        let status_code = rng.gen_range(300..=304);
        let server = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server)
            .await;

        let uri = &server.uri();
        let finder = Finder::with_base_url(uri, uri);
        let _ = finder.ipv6().await;
    }

    #[tokio::test]
    async fn test_ipv6_400() {
        let server = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(400))
            .mount(&server)
            .await;

        let uri = &server.uri();
        let finder = Finder::with_base_url(uri, uri);
        if let Error::Common(ErrorCommon::Network(details)) = finder
            .ipv6()
            .await
            .expect_err("HTTP 400 must return an error")
        {
            assert_eq!(details.side, NetworkSide::Client, "network side");
            assert!(details.should_retry, "should retry");
            assert_eq!(
                r#"ipify service has returned "400 Bad Request" HTTP status code"#,
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
    async fn test_ipv6_4xx() {
        let mut rng = SmallRng::from_entropy();
        let status_code = rng.gen_range(401..=409);
        let server = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server)
            .await;

        let uri = &server.uri();
        let finder = Finder::with_base_url(uri, uri);
        let _ = finder.ipv6().await;
    }

    #[tokio::test]
    async fn test_ipv6_5xx() {
        let mut rng = SmallRng::from_entropy();
        let status_code = rng.gen_range(500..=508);
        let server = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server)
            .await;

        let uri = &server.uri();
        let finder = Finder::with_base_url(uri, uri);
        if let Error::Finder(ExternalService::Internal { reason }) = finder
            .ipv6()
            .await
            .expect_err("HTTP 5XX must return an error")
        {
            assert_eq!(
                reason,
                format!(
                    r#"ipify service has responded with an HTTP "{}" status code (expected 200)"#,
                    http::StatusCode::from_u16(status_code).unwrap(),
                ),
                "expected finder internal error"
            );
        } else {
            panic!("expected a finder internal error")
        }
    }

    #[tokio::test]
    async fn test_ipv6_domain_do_not_resolve() {
        let finder = Finder::with_base_url("https://ipify.test", "https://ipify.test");
        let err = finder
            .ipv6()
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
    async fn test_ips_200() {
        let expected_ipv4 = Ipv4Addr::new(1, 1, 1, 1);
        let expected_ipv6 = Ipv6Addr::new(0, 0, 0, 0, 0, 0xFFFF, 0x0101, 0x0101);
        let server_ipv4 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(200).set_body_string(expected_ipv4.to_string()))
            .mount(&server_ipv4)
            .await;

        let server_ipv6 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(200).set_body_string(expected_ipv6.to_string()))
            .mount(&server_ipv6)
            .await;

        let uri_ipv4 = &server_ipv4.uri();
        let uri_ipv6 = &server_ipv6.uri();
        let finder = Finder::with_base_url(uri_ipv4, uri_ipv6);
        let (ipv4, ipv6) = finder.ips().await.expect("HTTP 200 must return the IPs");
        assert_eq!(ipv4, expected_ipv4, "unexpected returned IP V4");
        assert_eq!(ipv6, expected_ipv6, "unexpected returned IP V6");
    }
    #[tokio::test]
    #[should_panic(
        expected = r#"BUG (please report it). Unexpected ipify response body for IP v4, got: "1.2.3.4.5".
This may have happened because ipify has changed the format of the response body and this implementation hasn't been updated."#
    )]
    async fn test_ips_200_invalid_ip_v4_format() {
        let server_ipv4 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(200).set_body_string("1.2.3.4.5"))
            .mount(&server_ipv4)
            .await;

        let server_ipv6 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(200).set_body_string("2a01:57a0:3147:9b00::2"))
            .mount(&server_ipv6)
            .await;

        let uri_ipv4 = &server_ipv4.uri();
        let uri_ipv6 = &server_ipv6.uri();
        let finder = Finder::with_base_url(uri_ipv4, uri_ipv6);
        let _ = finder.ips().await;
    }

    #[tokio::test]
    #[should_panic(
        expected = r#"BUG (please report it). Unexpected ipify response body for IP v6, got: "2a01:57a0:3147:9b00::2::85745".
This may have happened because ipify has changed the format of the response body and this implementation hasn't been updated."#
    )]
    async fn test_ips_200_invalid_ip_v6_format() {
        let server_ipv4 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(200).set_body_string("1.2.3.4"))
            .mount(&server_ipv4)
            .await;

        let server_ipv6 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(
                ResponseTemplate::new(200).set_body_string("2a01:57a0:3147:9b00::2::85745"),
            )
            .mount(&server_ipv6)
            .await;

        let uri_ipv4 = &server_ipv4.uri();
        let uri_ipv6 = &server_ipv6.uri();
        let finder = Finder::with_base_url(uri_ipv4, uri_ipv6);
        let _ = finder.ips().await;
    }

    #[tokio::test]
    #[should_panic]
    async fn test_ips_200_invalid_ips_format() {
        let server_ipv4 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(200).set_body_string("1.2.3.4:5"))
            .mount(&server_ipv4)
            .await;

        let server_ipv6 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(
                ResponseTemplate::new(200).set_body_string("2a01:57a0:3147:9b00::2::85745"),
            )
            .mount(&server_ipv6)
            .await;

        let uri_ipv4 = &server_ipv4.uri();
        let uri_ipv6 = &server_ipv6.uri();
        let finder = Finder::with_base_url(uri_ipv4, uri_ipv6);
        match finder.ips().await {
            Err(Error::Finder(ExternalService::Internal { .. })) => {}
            _ => panic!("expected a finder internal error"),
        }
    }

    #[tokio::test]
    #[should_panic(
        expected = "BUG (please report it): this implementation is outdated, the external service has changed its public API."
    )]
    async fn test_ips_3xx_ipv4() {
        let mut rng = SmallRng::from_entropy();
        let status_code = rng.gen_range(300..=304);
        let server_ipv4 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server_ipv4)
            .await;

        let server_ipv6 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(
                ResponseTemplate::new(200).set_body_string(
                    Ipv6Addr::new(0, 0, 0, 0, 0, 0xFFFF, 0x0101, 0x0101).to_string(),
                ),
            )
            .mount(&server_ipv6)
            .await;

        let uri_ipv4 = &server_ipv4.uri();
        let uri_ipv6 = &server_ipv6.uri();

        let finder = Finder::with_base_url(uri_ipv4, uri_ipv6);
        let _ = finder.ips().await;
    }

    #[tokio::test]
    #[should_panic(
        expected = "BUG (please report it): this implementation is outdated, the external service has changed its public API."
    )]
    async fn test_ips_3xx_ipv6() {
        let server_ipv4 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(
                ResponseTemplate::new(200).set_body_string(Ipv4Addr::new(1, 1, 1, 1).to_string()),
            )
            .mount(&server_ipv4)
            .await;

        let mut rng = SmallRng::from_entropy();
        let status_code = rng.gen_range(300..=304);
        let server_ipv6 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server_ipv6)
            .await;

        let uri_ipv4 = &server_ipv4.uri();
        let uri_ipv6 = &server_ipv6.uri();

        let finder = Finder::with_base_url(uri_ipv4, uri_ipv6);
        let _ = finder.ips().await;
    }

    #[tokio::test]
    #[should_panic(
        expected = "BUG (please report it): this implementation is outdated, the external service has changed its public API."
    )]
    async fn test_ips_3xx_both() {
        let mut rng = SmallRng::from_entropy();
        let status_code = rng.gen_range(300..=304);
        let server_ipv4 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server_ipv4)
            .await;

        let status_code = rng.gen_range(300..=304);
        let server_ipv6 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server_ipv6)
            .await;

        let uri_ipv4 = &server_ipv4.uri();
        let uri_ipv6 = &server_ipv6.uri();

        let finder = Finder::with_base_url(uri_ipv4, uri_ipv6);
        let _ = finder.ips().await;
    }

    #[tokio::test]
    async fn test_ips_400_ipv4() {
        let server_ipv4 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(400))
            .mount(&server_ipv4)
            .await;
        let server_ipv6 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(
                ResponseTemplate::new(200).set_body_string(
                    Ipv6Addr::new(0, 0, 0, 0, 0, 0xFFFF, 0x0101, 0x0101).to_string(),
                ),
            )
            .mount(&server_ipv6)
            .await;

        let uri_ipv4 = &server_ipv4.uri();
        let uri_ipv6 = &server_ipv6.uri();

        let finder = Finder::with_base_url(uri_ipv4, uri_ipv6);
        if let Error::Common(ErrorCommon::Network(details)) = finder
            .ips()
            .await
            .expect_err("HTTP 400 must return an error")
        {
            assert_eq!(details.side, NetworkSide::Client, "network side");
            assert!(details.should_retry, "should retry");
            assert_eq!(
                r#"ipify service has returned "400 Bad Request" HTTP status code"#,
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
    async fn test_ips_400_ipv6() {
        let server_ipv4 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(
                ResponseTemplate::new(200).set_body_string(Ipv4Addr::new(1, 1, 1, 1).to_string()),
            )
            .mount(&server_ipv4)
            .await;
        let server_ipv6 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(400))
            .mount(&server_ipv6)
            .await;

        let uri_ipv4 = &server_ipv4.uri();
        let uri_ipv6 = &server_ipv6.uri();

        let finder = Finder::with_base_url(uri_ipv4, uri_ipv6);
        if let Error::Common(ErrorCommon::Network(details)) = finder
            .ips()
            .await
            .expect_err("HTTP 400 must return an error")
        {
            assert_eq!(details.side, NetworkSide::Client, "network side");
            assert!(details.should_retry, "should retry");
            assert_eq!(
                r#"ipify service has returned "400 Bad Request" HTTP status code"#,
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
    async fn test_ips_400_boths() {
        let server_ipv4 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(400))
            .mount(&server_ipv4)
            .await;
        let server_ipv6 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(400))
            .mount(&server_ipv6)
            .await;

        let uri_ipv4 = &server_ipv4.uri();
        let uri_ipv6 = &server_ipv6.uri();

        let finder = Finder::with_base_url(uri_ipv4, uri_ipv6);
        if let Error::Common(ErrorCommon::Network(details)) = finder
            .ips()
            .await
            .expect_err("HTTP 400 must return an error")
        {
            assert_eq!(details.side, NetworkSide::Client, "network side");
            assert!(details.should_retry, "should retry");
            assert_eq!(
                r#"ipify service has returned "400 Bad Request" HTTP status code"#,
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
    async fn test_ips_4xx_ipv4() {
        let mut rng = SmallRng::from_entropy();
        let status_code = rng.gen_range(401..=409);
        let server_ipv4 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server_ipv4)
            .await;

        let server_ipv6 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(
                ResponseTemplate::new(200).set_body_string(
                    Ipv6Addr::new(0, 0, 0, 0, 0, 0xFFFF, 0x0101, 0x0101).to_string(),
                ),
            )
            .mount(&server_ipv6)
            .await;

        let uri_ipv4 = &server_ipv4.uri();
        let uri_ipv6 = &server_ipv6.uri();

        let finder = Finder::with_base_url(uri_ipv4, uri_ipv6);
        let _ = finder.ips().await;
    }

    #[tokio::test]
    #[should_panic(
        expected = "BUG (please report it): this implementation is outdated, the external service has changed its public API."
    )]
    async fn test_ips_4xx_ipv6() {
        let server_ipv4 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(
                ResponseTemplate::new(200).set_body_string(Ipv4Addr::new(1, 1, 1, 1).to_string()),
            )
            .mount(&server_ipv4)
            .await;

        let mut rng = SmallRng::from_entropy();
        let status_code = rng.gen_range(401..=409);
        let server_ipv6 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server_ipv6)
            .await;

        let uri_ipv4 = &server_ipv4.uri();
        let uri_ipv6 = &server_ipv6.uri();

        let finder = Finder::with_base_url(uri_ipv4, uri_ipv6);
        let _ = finder.ips().await;
    }

    #[tokio::test]
    #[should_panic(
        expected = "BUG (please report it): this implementation is outdated, the external service has changed its public API."
    )]
    async fn test_ips_4xx_both() {
        let mut rng = SmallRng::from_entropy();
        let status_code = rng.gen_range(401..=409);
        let server_ipv4 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server_ipv4)
            .await;

        let status_code = rng.gen_range(401..=409);
        let server_ipv6 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server_ipv6)
            .await;

        let uri_ipv4 = &server_ipv4.uri();
        let uri_ipv6 = &server_ipv6.uri();

        let finder = Finder::with_base_url(uri_ipv4, uri_ipv6);
        if let Error::Common(ErrorCommon::Network(details)) = finder
            .ips()
            .await
            .expect_err("HTTP 400 must return an error")
        {
            assert_eq!(details.side, NetworkSide::Client, "network side");
            assert!(details.should_retry, "should retry");
            assert_eq!(
                r#"ipify service has returned "400 Bad Request" HTTP status code"#,
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
    async fn test_ips_500_ipv4() {
        let mut rng = SmallRng::from_entropy();
        let status_code = rng.gen_range(500..=508);

        let server_ipv4 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server_ipv4)
            .await;
        let server_ipv6 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(
                ResponseTemplate::new(200).set_body_string(
                    Ipv6Addr::new(0, 0, 0, 0, 0, 0xFFFF, 0x0101, 0x0101).to_string(),
                ),
            )
            .mount(&server_ipv6)
            .await;

        let uri_ipv4 = &server_ipv4.uri();
        let uri_ipv6 = &server_ipv6.uri();

        let finder = Finder::with_base_url(uri_ipv4, uri_ipv6);
        if let Error::Finder(ExternalService::Internal { reason }) = finder
            .ips()
            .await
            .expect_err("HTTP 5XX must return an error")
        {
            assert_eq!(
                reason,
                format!(
                    r#"ipify service has responded with an HTTP "{}" status code (expected 200)"#,
                    http::StatusCode::from_u16(status_code).unwrap(),
                ),
                "expected finder internal error"
            );
        } else {
            panic!("expected a finder internal error")
        }
    }

    #[tokio::test]
    async fn test_ips_5xx_ipv6() {
        let server_ipv4 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(
                ResponseTemplate::new(200).set_body_string(Ipv4Addr::new(1, 1, 1, 1).to_string()),
            )
            .mount(&server_ipv4)
            .await;

        let mut rng = SmallRng::from_entropy();
        let status_code = rng.gen_range(500..=508);
        let server_ipv6 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server_ipv6)
            .await;

        let uri_ipv4 = &server_ipv4.uri();
        let uri_ipv6 = &server_ipv6.uri();

        let finder = Finder::with_base_url(uri_ipv4, uri_ipv6);
        if let Error::Finder(ExternalService::Internal { reason }) = finder
            .ips()
            .await
            .expect_err("HTTP 5XX must return an error")
        {
            assert_eq!(
                reason,
                format!(
                    r#"ipify service has responded with an HTTP "{}" status code (expected 200)"#,
                    http::StatusCode::from_u16(status_code).unwrap(),
                ),
                "expected finder internal error"
            );
        } else {
            panic!("expected a finder internal error")
        }
    }

    #[tokio::test]
    async fn test_ips_5xx_both() {
        let mut rng = SmallRng::from_entropy();
        let status_code = rng.gen_range(500..=508);

        let server_ipv4 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server_ipv4)
            .await;

        let server_ipv6 = MockServer::start().await;
        Mock::given(method("GET"))
            .respond_with(ResponseTemplate::new(status_code))
            .mount(&server_ipv6)
            .await;

        let uri_ipv4 = &server_ipv4.uri();
        let uri_ipv6 = &server_ipv6.uri();

        let finder = Finder::with_base_url(uri_ipv4, uri_ipv6);
        if let Error::Finder(ExternalService::Internal { reason }) = finder
            .ips()
            .await
            .expect_err("HTTP 5XX must return an error")
        {
            assert_eq!(
                reason,
                format!(
                    r#"ipify service has responded with an HTTP "{}" status code (expected 200)"#,
                    http::StatusCode::from_u16(status_code).unwrap(),
                ),
                "expected finder internal error"
            );
        } else {
            panic!("expected a finder internal error")
        }
    }

    #[tokio::test]
    async fn test_ips_domain_do_not_resolve() {
        let finder = Finder::with_base_url("https://ipify.test", "https://ipify.test");
        let err = finder
            .ips()
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
}
