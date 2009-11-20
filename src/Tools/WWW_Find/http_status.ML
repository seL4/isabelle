(*  Title:      http_status.ML
    Author:     Timothy Bourke, NICTA

HTTP status codes and reasons.
*)
signature HTTP_STATUS =
sig
  type t

  val to_status_code : t -> int
  val to_reason : t -> string
  val from_status_code : int -> t option

  val continue : t
  val switching_protocols : t
  val ok : t
  val created : t
  val accepted : t
  val non_authoritative_information : t
  val no_content : t
  val reset_content : t
  val partial_content : t
  val multiple_choices : t
  val moved_permanently : t
  val found : t
  val see_other : t
  val not_modified : t
  val use_proxy : t
  val temporary_redirect : t
  val bad_request : t
  val unauthorized : t
  val payment_required : t
  val forbidden : t
  val not_found : t
  val method_not_allowed : t
  val not_acceptable : t
  val proxy_authentication_required : t
  val request_timeout : t
  val conflict : t
  val gone : t
  val length_required : t
  val precondition_failed : t
  val request_entity_too_large : t
  val request_uri_too_long : t
  val unsupported_media_type : t
  val requested_range_not_satisfiable : t
  val expectation_failed : t
  val internal_server_error : t
  val not_implemented : t
  val bad_gateway : t
  val service_unavailable : t
  val gateway_timeout : t
  val http_version_not_supported : t

end;

structure HttpStatus : HTTP_STATUS =
struct

type t = int

local
val int_status_map = Inttab.make
  [(100, "Continue"),
   (101, "Switching Protocols"),
   (200, "OK"),
   (201, "Created"),
   (202, "Accepted"),
   (203, "Non-Authoritative Information"),
   (204, "No Content"),
   (205, "Reset Content"),
   (206, "Partial Content"),
   (300, "Multiple Choices"),
   (301, "Moved Permanently"),
   (302, "Found"),
   (303, "See Other"),
   (304, "Not Modified"),
   (305, "Use Proxy"),
   (307, "Temporary Redirect"),
   (400, "Bad Request"),
   (401, "Unauthorized"),
   (402, "Payment Required"),
   (403, "Forbidden"),
   (404, "Not Found"),
   (405, "Method Not Allowed"),
   (406, "Not Acceptable"),
   (407, "Proxy Authentication Required"),
   (408, "Request Timeout"),
   (409, "Conflict"),
   (410, "Gone"),
   (411, "Length Required"),
   (412, "Precondition Failed"),
   (413, "Request Entity Too Large"),
   (414, "Request URI Too Long"),
   (415, "Unsupported Media Type"),
   (416, "Requested Range Not Satisfiable"),
   (417, "Expectation Failed"),
   (500, "Internal Server Error"),
   (501, "Not Implemented"),
   (502, "Bad Gateway"),
   (503, "Service Unavailable"),
   (504, "Gateway Timeout"),
   (505, "HTTP Version Not Supported")];
in
fun from_status_code i =
  if is_some (Inttab.lookup int_status_map i)
  then SOME i
  else NONE;

val to_reason = the o Inttab.lookup int_status_map;
end;

val to_status_code = I;

val continue = 100;
val switching_protocols = 101;
val ok = 200;
val created = 201;
val accepted = 202;
val non_authoritative_information = 203;
val no_content = 204;
val reset_content = 205;
val partial_content = 206;
val multiple_choices = 300;
val moved_permanently = 301;
val found = 302;
val see_other = 303;
val not_modified = 304;
val use_proxy = 305;
val temporary_redirect = 307;
val bad_request = 400;
val unauthorized = 401;
val payment_required = 402;
val forbidden = 403;
val not_found = 404;
val method_not_allowed = 405;
val not_acceptable = 406;
val proxy_authentication_required = 407;
val request_timeout = 408;
val conflict = 409;
val gone = 410;
val length_required = 411;
val precondition_failed = 412;
val request_entity_too_large = 413;
val request_uri_too_long = 414;
val unsupported_media_type = 415;
val requested_range_not_satisfiable = 416;
val expectation_failed = 417;
val internal_server_error = 500;
val not_implemented = 501;
val bad_gateway = 502;
val service_unavailable = 503;
val gateway_timeout = 504;
val http_version_not_supported = 505;

end;

