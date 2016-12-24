/*
 * @(#)$Id: socket_server.pl,v 1.2 1997/10/21 12:12:32 rjb Exp $
 *
 * $Log: socket_server.pl,v $
 * Revision 1.2  1997/10/21 12:12:32  rjb
 * Bugfix.
 *
 * Revision 1.1  1997/10/20 16:51:32  rjb
 * Initial revision
 *
 */

/* Provides support for using Clam as a server to another process connected by
 * means of a socket.
 *
 * This code is dependent on SICStus Prolog.
 */

/* Required by SICStus 3 */
:- ensure_loaded(library(sockets)).

:- use_module(library(system),[delete_file/1]).

create_socket(unix,File,Socket):-
    socket('AF_UNIX',Socket),
    socket_bind(Socket,'AF_UNIX'(File)).
create_socket(inet,File,Socket):-
    socket('AF_INET',Socket),
    socket_bind(Socket,'AF_INET'(Host,Port)),
    tell(File), write(Host), nl, write(Port), nl, flush_output, told.
create_socket(_,_,_):-
    write('invalid socket type; use "unix" or "inet".'), nl,
    fail.

wait_for_connection(_,Socket,Stream,TimeOut):-
    socket_select(Socket,Stream,TimeOut,[],_),
    /* Check that Stream is instantiated, i.e. that there was no time-out. */
    nonvar(Stream), !.
wait_for_connection(File,_,_,_):-
    write('timed out.'), nl,
    delete_file(File),
    fail.

/* start_server(+Type,+File,+TimeOut,?Stream).
 *
 * Start a server on a socket called +File of type +Type (`unix' for a local
 * socket or `inet' for an Internet socket). A local socket is a special file;
 * an Internet socket is represented by an ordinary text file containing the
 * Internet domain name of the host machine and the number of the port to
 * which to connect.
 *
 * If TimeOut is of the form Secs:USecs, the server exits if a connection
 * is not made to the socket by Secs seconds and USecs microseconds after it
 * was created. Instantiate TimeOut to `off' for no time-out.
 *
 * Stream is instantiated to a bi-directional stream. (See the SICStus
 * documentation for details.)
 */
start_server(Type,File,TimeOut,Stream):-
    \+ file_exists(File),
    create_socket(Type,File,Socket),
    socket_listen(Socket,1),
    nl, write('Server started. Waiting for connection ... '), flush_output,
    !, wait_for_connection(File,Socket,Stream,TimeOut),
    write('connection established.'), nl.
