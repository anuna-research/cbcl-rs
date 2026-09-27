%% cbcl_erl: Erlang loader for the cbcl-erl NIF (crates/cbcl-erl).
%%
%% The BEAM module name is fixed by rustler::init!("cbcl_erl") in lib.rs;
%% this file matches that name. A host copies it beside its own sources
%% (cbcl-bus keeps one at apps/cbcl_bus/src/cbcl_erl.erl) and points
%% init/0 at wherever it installs libcbcl_erl.so.
%%
%% NIF surface:
%%   SPEC-009 CON-001/CON-002
%%     parse_message/1      :: binary() -> {ok, message()} | {error, binary()}
%%     parse_message_lax/1  :: binary() -> {ok, message()} | {error, binary()}
%%     verify_dialect/1     :: binary() -> ok | {error, binary()}
%%     versions/0           :: () -> {CbclRsGitRevision :: binary(),
%%                                    CbclCoreVersion   :: binary(),
%%                                    CbclErlVersion    :: binary()}
%%   SPEC-019 R.7 (state layer; SPEC-009 CON-003). Each takes one binary()
%%   holding the export's S-expression frame (cbcl_parser::state_exports)
%%   and returns {ok, Bin} | {error, Bin}: JSON for fold, state_schema,
%%   may_send, frontier; the canonical act for intend; <<"ok">> for
%%   verify_state_shape; sha256-<hex> for dialect_hash.
%%     fold/1               :: binary() -> {ok, binary()} | {error, binary()}
%%     intend/1             :: binary() -> {ok, binary()} | {error, binary()}
%%     verify_state_shape/1 :: binary() -> {ok, binary()} | {error, binary()}
%%     state_schema/1       :: binary() -> {ok, binary()} | {error, binary()}
%%     may_send/1           :: binary() -> {ok, binary()} | {error, binary()}
%%     frontier/1           :: binary() -> {ok, binary()} | {error, binary()}
%%     dialect_hash/1       :: binary() -> {ok, binary()} | {error, binary()}
%%     admit/1              :: binary() -> {ok, binary()} | {error, binary()}
%%
%% All bodies below are stubs: when the NIF loads via on_load they are
%% replaced atomically by the rustler-emitted natives. If load_nif fails
%% the stubs raise nif_not_loaded so the failure is loud rather than
%% silent (cf. erlang:nif_error/1 docs).
%%
%% Where the library is: the CBCL_ERL_NIF environment variable, the path
%% of the library without its extension (erlang:load_nif/2 appends .so,
%% which scripts/install-mac-nif.sh provides on macOS); otherwise
%% priv/libcbcl_erl under this application's priv directory.

-module(cbcl_erl).

-export([parse_message/1,
         parse_message_lax/1,
         verify_dialect/1,
         versions/0,
         fold/1,
         intend/1,
         verify_state_shape/1,
         state_schema/1,
         may_send/1,
         frontier/1,
         dialect_hash/1,
         admit/1]).

-on_load(init/0).

init() ->
    Path = case os:getenv("CBCL_ERL_NIF") of
        false -> filename:join(priv_dir(), "libcbcl_erl");
        P     -> P
    end,
    erlang:load_nif(Path, 0).

priv_dir() ->
    case code:priv_dir(cbcl_erl) of
        {error, bad_name} -> "priv";
        Dir               -> Dir
    end.

parse_message(_Bytes)      -> erlang:nif_error(nif_not_loaded).
parse_message_lax(_Bytes)  -> erlang:nif_error(nif_not_loaded).
verify_dialect(_Bytes)     -> erlang:nif_error(nif_not_loaded).
versions()                 -> erlang:nif_error(nif_not_loaded).
fold(_Frame)               -> erlang:nif_error(nif_not_loaded).
intend(_Frame)             -> erlang:nif_error(nif_not_loaded).
verify_state_shape(_Frame) -> erlang:nif_error(nif_not_loaded).
state_schema(_Frame)       -> erlang:nif_error(nif_not_loaded).
may_send(_Frame)           -> erlang:nif_error(nif_not_loaded).
frontier(_Frame)           -> erlang:nif_error(nif_not_loaded).
dialect_hash(_Define)      -> erlang:nif_error(nif_not_loaded).
admit(_Frame)              -> erlang:nif_error(nif_not_loaded).
