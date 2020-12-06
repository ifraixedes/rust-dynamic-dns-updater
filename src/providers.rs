pub mod error;
pub mod duckdns;

use error::Error;

pub struct Response<'a> {
    http_status_code: http_types::StatusCode,
    result_msg: &'a str,
    updated: Option<bool>,
}

impl<'a> Response<'a> {
    // Construct a Response based on the provider returned HTTP Status code, a
    // result message and if the IP has been updated or not.
    // updated is an option because only some providers provide that information
    // and for the ones that it's provided, perhaps the implementation provides
    // it, however it isn't obligatory because if it's provided by the
    // implementation then it may mean to do some additional network round
    // trips.
    fn from_http(
        status_code: http_types::StatusCode,
        result_msg: &'a str,
        updated: Option<bool>,
    ) -> Self {
        Response {
            http_status_code: status_code,
            result_msg,
            updated,
        }
    }

    pub fn is_ok(&self) -> bool {
        self.http_status_code.is_success()
    }

    pub fn result_msg(&self) -> &'a str {
        self.result_msg
    }

    // Tells if the request has updated the DNS configuration or it has left it
    // as it was because the sent values were equal the ones set.
    // A provider may not provide this information in the response, and it isn't
    // common that a provider implementation makes a request for finding out to
    // avoid extra round trips, in that case the information is unknown and None
    // is returned.
    pub fn is_updated(&self) -> Option<bool> {
        self.updated
    }
}

pub type UpdateResult<'a> = Result<Response<'a>, Error>;
