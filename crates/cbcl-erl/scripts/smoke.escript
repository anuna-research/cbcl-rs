#!/usr/bin/env escript
%% -*- erlang -*-
%% Smoke test for the cbcl-erl NIF on a real BEAM (SPEC-009 CON-003).
%%
%% Builds the NIF (cargo build -p cbcl-erl --<profile>), installs the .so
%% name on macOS (scripts/install-mac-nif.sh), compiles and loads
%% erlang/cbcl_erl.erl with CBCL_ERL_NIF pointing at the build, and calls
%% every NIF: versions/0, verify_dialect/1, parse_message/1,
%% parse_message_lax/1 and the eight SPEC-019 state NIFs, each once with a
%% valid frame built from dialects/lunch-vote.cbcl and once with a
%% malformed one, asserting the {ok, Bin} / {error, Bin} shapes.
%%
%% Usage:
%%   crates/cbcl-erl/scripts/smoke.escript            # release profile
%%   crates/cbcl-erl/scripts/smoke.escript debug
%%   SKIP_BUILD=1 crates/cbcl-erl/scripts/smoke.escript
%%
%% Exit status 0 when every check passes, 1 otherwise.

main(Args) ->
    Profile = case Args of [P | _] -> P; [] -> "release" end,
    Root = workspace_root(),
    ok = build(Root, Profile),
    Lib = filename:join([Root, "target", Profile, "libcbcl_erl"]),
    os:putenv("CBCL_ERL_NIF", Lib),
    ok = load_module(Root),
    Lunch = lunch_vote(Root),
    Checks = checks(Lunch),
    Results = [run_check(C) || C <- Checks],
    Failed = [R || {fail, _, _} <- Results, R <- [x]],
    io:format("~n~p checks, ~p failed~n", [length(Results), length(Failed)]),
    case Failed of
        [] -> halt(0);
        _ -> halt(1)
    end.

%% --------------------------------------------------------------------
%% Build and load
%% --------------------------------------------------------------------

workspace_root() ->
    Script = filename:absname(escript:script_name()),
    %% scripts/ -> cbcl-erl/ -> crates/ -> workspace
    filename:join(lists:sublist(filename:split(filename:dirname(Script)),
                                length(filename:split(filename:dirname(Script))) - 3)).

build(Root, Profile) ->
    case os:getenv("SKIP_BUILD") of
        false ->
            io:format("== cargo build -p cbcl-erl --~s~n", [Profile]),
            0 = run(Root, "cargo", ["build", "-p", "cbcl-erl", "--" ++ Profile]),
            io:format("== install-mac-nif.sh ~s~n", [Profile]),
            0 = run(Root, filename:join([Root, "crates", "cbcl-erl", "scripts",
                                         "install-mac-nif.sh"]), [Profile]),
            ok;
        _ ->
            io:format("== SKIP_BUILD set; using target/~s as is~n", [Profile]),
            ok
    end.

run(Cwd, Exe, ExeArgs) ->
    Path = case filename:pathtype(Exe) of
        absolute -> Exe;
        _ -> case os:find_executable(Exe) of
                 false -> erlang:error({not_found, Exe});
                 Found -> Found
             end
    end,
    Port = open_port({spawn_executable, Path},
                     [{args, ExeArgs}, {cd, Cwd}, exit_status,
                      stderr_to_stdout, binary, stream]),
    drain(Port).

drain(Port) ->
    receive
        {Port, {data, Data}} ->
            io:put_chars(Data),
            drain(Port);
        {Port, {exit_status, Status}} ->
            Status
    end.

load_module(Root) ->
    Src = filename:join([Root, "crates", "cbcl-erl", "erlang", "cbcl_erl.erl"]),
    io:format("== compile and load ~s~n", [Src]),
    {ok, cbcl_erl, Bin} = compile:file(Src, [binary, report]),
    case code:load_binary(cbcl_erl, Src, Bin) of
        {module, cbcl_erl} -> ok;
        {error, Reason} ->
            io:format("load_nif failed: ~p (CBCL_ERL_NIF=~s)~n",
                      [Reason, os:getenv("CBCL_ERL_NIF")]),
            halt(1)
    end.

%% The lunch-vote dialect with its comment lines removed.
lunch_vote(Root) ->
    Path = filename:join([Root, "dialects", "lunch-vote.cbcl"]),
    {ok, Text} = file:read_file(Path),
    Lines = binary:split(Text, <<"\n">>, [global]),
    Kept = [L || L <- Lines, not comment(L)],
    iolist_to_binary(lists:join(<<"\n">>, Kept)).

comment(Line) ->
    case string:trim(Line, leading) of
        <<";", _/binary>> -> true;
        _ -> false
    end.

%% --------------------------------------------------------------------
%% The checks: {Name, Call, Expectation}
%% --------------------------------------------------------------------

checks(Lunch) ->
    Opener = <<"(lang lunch-vote (propose @lunch :question \"Lunch?\" "
               ":options (\"Pizza\" \"Sushi\") :caused-by begin "
               ":thread \"v1\" :from @aria))">>,
    Acts = <<"(acts (@aria ", Opener/binary, "))">>,
    Frame = fun(Head, Tail) ->
                <<"(", Head/binary, " ", Lunch/binary, " \"v1\" ",
                  Acts/binary, Tail/binary, ")">>
            end,
    Vote = <<"(lang lunch-vote (vote @lunch :choice \"Sushi\" "
             ":caused-by begin :thread \"v1\" :from @bo))">>,
    BadVote = <<"(lang lunch-vote (vote @lunch :choice \"Sushi\" :extra 1 "
                ":caused-by begin :thread \"v1\" :from @bo))">>,
    Orphan = <<"(lang lunch-vote (vote @lunch :choice \"Sushi\" :caused-by "
               "sha256-ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff "
               ":thread \"v1\" :from @bo))">>,
    [
     {"versions/0",
      fun() -> cbcl_erl:versions() end,
      fun({A, B, C}) when is_binary(A), is_binary(B), is_binary(C) -> true;
         (_) -> false end},
     {"verify_dialect/1 accepts lunch-vote",
      fun() -> cbcl_erl:verify_dialect(Lunch) end,
      fun(ok) -> true; (_) -> false end},
     {"verify_dialect/1 rejects garbage",
      fun() -> cbcl_erl:verify_dialect(<<"(define">>) end,
      fun err/1},
     {"parse_message/1",
      fun() -> cbcl_erl:parse_message(<<"(tell @bo \"hi\")">>) end,
      fun ok/1},
     {"parse_message/1 rejects garbage",
      fun() -> cbcl_erl:parse_message(<<"(tell">>) end,
      fun err/1},
     {"parse_message_lax/1",
      fun() -> cbcl_erl:parse_message_lax(<<"(tell @bo \"hi\")">>) end,
      fun ok/1},
     %% SPEC-019 state NIFs: a valid frame and a malformed one each.
     {"fold/1",
      fun() -> cbcl_erl:fold(Frame(<<"fold">>, <<>>)) end,
      fun({ok, <<"{\"question\":\"Lunch?\"", _/binary>>}) -> true;
         (_) -> false end},
     {"fold/1 malformed",
      fun() -> cbcl_erl:fold(<<"(fold">>) end,
      fun err/1},
     {"intend/1",
      fun() -> cbcl_erl:intend(Frame(<<"intend">>, <<" @bo vote (:choice \"Sushi\")">>)) end,
      fun({ok, <<"(lang lunch-vote (vote @lunch", _/binary>>}) -> true;
         (_) -> false end},
     {"intend/1 rejects an out-of-domain choice",
      fun() -> cbcl_erl:intend(Frame(<<"intend">>, <<" @bo vote (:choice \"Tacos\")">>)) end,
      fun({error, <<"{\"reject\":\"domain\"", _/binary>>}) -> true;
         (_) -> false end},
     {"intend/1 malformed",
      fun() -> cbcl_erl:intend(<<"(intend x)">>) end,
      fun err/1},
     {"verify_state_shape/1",
      fun() -> cbcl_erl:verify_state_shape(
                 <<"(verify-state-shape ", Lunch/binary, " ", Vote/binary, ")">>) end,
      fun({ok, <<"ok">>}) -> true; (_) -> false end},
     {"verify_state_shape/1 blames an undeclared field",
      fun() -> cbcl_erl:verify_state_shape(
                 <<"(verify-state-shape ", Lunch/binary, " ", BadVote/binary, ")">>) end,
      fun err/1},
     {"verify_state_shape/1 malformed",
      fun() -> cbcl_erl:verify_state_shape(<<"(verify-state-shape">>) end,
      fun err/1},
     {"state_schema/1",
      fun() -> cbcl_erl:state_schema(<<"(state-schema ", Lunch/binary, ")">>) end,
      fun({ok, <<"{\"question\":", _/binary>>}) -> true; (_) -> false end},
     {"state_schema/1 malformed",
      fun() -> cbcl_erl:state_schema(<<"(state-schema)">>) end,
      fun err/1},
     {"may_send/1",
      fun() -> cbcl_erl:may_send(Frame(<<"may-send">>, <<" @bo">>)) end,
      fun({ok, <<"[\"vote\"]">>}) -> true; (_) -> false end},
     {"may_send/1 malformed",
      fun() -> cbcl_erl:may_send(<<"(may-send">>) end,
      fun err/1},
     {"frontier/1",
      fun() -> cbcl_erl:frontier(Frame(<<"frontier">>, <<>>)) end,
      fun({ok, <<"{\"instance\":\"sha256-", _/binary>>}) -> true; (_) -> false end},
     {"frontier/1 malformed",
      fun() -> cbcl_erl:frontier(<<"(frontier">>) end,
      fun err/1},
     {"dialect_hash/1",
      fun() -> cbcl_erl:dialect_hash(Lunch) end,
      fun({ok, <<"sha256-", Hex:64/binary>>}) -> hex(Hex); (_) -> false end},
     {"dialect_hash/1 malformed",
      fun() -> cbcl_erl:dialect_hash(<<"(nope)">>) end,
      fun err/1},
     {"admit/1 holds an orphan pending",
      fun() -> cbcl_erl:admit(Frame(<<"admit">>, <<" (@bo ", Orphan/binary, ")">>)) end,
      fun({ok, <<"{\"verdict\":\"pending\"}">>}) -> true; (_) -> false end},
     {"admit/1 rejects an undeclared field",
      fun() -> cbcl_erl:admit(Frame(<<"admit">>, <<" (@bo ", BadVote/binary, ")">>)) end,
      fun({ok, <<"{\"verdict\":\"rejected\"", _/binary>>}) -> true; (_) -> false end},
     {"admit/1 malformed",
      fun() -> cbcl_erl:admit(<<"(admit">>) end,
      fun err/1},
     {"invalid utf-8 is a reason, not a crash",
      fun() -> cbcl_erl:fold(<<255, 254>>) end,
      fun({error, <<"invalid utf-8">>}) -> true; (_) -> false end}
    ].

ok({ok, Bin}) when is_binary(Bin) -> true;
ok({ok, _}) -> true;   % parse_message returns a term, not a binary
ok(_) -> false.

err({error, Bin}) when is_binary(Bin) -> true;
err(_) -> false.

hex(Bin) ->
    lists:all(fun(C) -> (C >= $0 andalso C =< $9) orelse (C >= $a andalso C =< $f) end,
              binary_to_list(Bin)).

run_check({Name, Call, Expect}) ->
    Result = try Call() catch Class:Reason -> {caught, Class, Reason} end,
    case catch Expect(Result) of
        true ->
            io:format("ok    ~s~n", [Name]),
            {pass, Name, Result};
        _ ->
            io:format("FAIL  ~s~n      got ~p~n", [Name, Result]),
            {fail, Name, Result}
    end.
