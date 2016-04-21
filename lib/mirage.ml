(*
 * Copyright (c) 2013 Thomas Gazagnaire <thomas@gazagnaire.org>
 * Copyright (c) 2013 Anil Madhavapeddy <anil@recoil.org>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

open Rresult
open Astring

module Key = Mirage_key
module Name = Functoria_app.Name
module Cmd = Functoria_app.Cmd
module Log = Functoria_app.Log
module Codegen = Functoria_app.Codegen

include Functoria

let get_target i = Key.(get (Info.context i) target)

end

let main_ml = ref None

let append_main fmt =
  match !main_ml with
  | None    -> failwith "main_ml"
  | Some oc -> append oc fmt

let newline_main () =
  match !main_ml with
  | None    -> failwith "main_ml"
  | Some oc -> newline oc

let set_main_ml file =
  let oc = open_out file in
  main_ml := Some oc

type mode = [
  | `Unix
  | `Xen
  | `Solo5
  | `MacOSX
]

let string_of_mode =
  function
  | `Unix -> "Unix"
  | `Xen -> "Xen"
  | `Solo5 -> "Solo5"
  | `MacOSX -> "MacOS X"

let mode : mode ref = ref `Unix

let set_mode m =
  mode := m

let get_mode () =
  !mode

type _ typ =
  | Type: 'a -> 'a typ
  | Function: 'a typ * 'b typ -> ('a -> 'b) typ

let (@->) f t =
  Function (f, t)

module type CONFIGURABLE = sig
  type t
  val name: t -> string
  val module_name: t -> string
  val packages: t -> string list
  val libraries: t -> string list
  val configure: t -> unit
  val clean: t -> unit
  val update_path: t -> string -> t
end


module TODO (N: sig val name: string end) = struct

  let todo str =
    failwith (Printf.sprintf "TODO: %s.%s" N.name str)

  let name _ =
    todo "name"

  let module_name _ =
    todo "module_name"

  let packages _ =
    todo "packages"

  let libraries _ =
    todo "libraries"

  let configure _ =
    todo "configure"

  let clean _ =
    todo "clean"

  let update_path _ =
    todo "update_path"

end

type ('a, 'b) base = {
  typ: 'a typ;
  t: 'b;
  m: (module CONFIGURABLE with type t = 'b);
}

type 'a foreign = {
  name: string;
  ty: 'a typ;
  libraries: string list;
  packages: string list;
}

type _ impl =
  | Impl: ('a, 'b) base -> 'a impl (* base implementation *)
  | App: ('a, 'b) app -> 'b impl   (* functor application *)
  | Foreign: 'a foreign -> 'a impl (* foreign functor implementation *)

and ('a, 'b) app = {
  f: ('a -> 'b) impl;  (* functor *)
  x: 'a impl;          (* parameter *)
}

let rec string_of_impl: type a. a impl -> string = function
  | Impl { t; m = (module M) } -> Printf.sprintf "Impl (%s)" (M.module_name t)
  | Foreign { name } -> Printf.sprintf "Foreign (%s)" name
  | App { f; x } -> Printf.sprintf "App (%s, %s)" (string_of_impl f) (string_of_impl x)

type 'a folder = {
  fn: 'b. 'a -> 'b impl -> 'a
}

let rec fold: type a. 'b folder -> a impl -> 'b -> 'b =
  fun fn t acc ->
    match t with
    | Impl _
    | Foreign _  -> fn.fn acc t
    | App {f; x} -> fold fn f (fn.fn acc x)

type iterator = {
  i: 'b. 'b impl -> unit
}

let rec iter: type a. iterator -> a impl -> unit =
  fun fn t ->
    match t with
    | Impl _
    | Foreign _  -> fn.i t
    | App {f; x} -> iter fn f; iter fn x; fn.i x

let driver_initialisation_error name =
  Printf.sprintf "fail (Failure %S)" name

module Name = struct

  let ids = Hashtbl.create 1024

  let names = Hashtbl.create 1024

  let create name =
    let n =
      try 1 + Hashtbl.find ids name
      with Not_found -> 1 in
    Hashtbl.replace ids name n;
    Printf.sprintf "%s%d" name n

  let of_key key ~base =
    find_or_create names key (fun () -> create base)

end

module Impl = struct

  (* get the left-most module name (ie. the name of the functor). *)
  let rec functor_name: type a. a impl -> string = function
    | Impl { t; m = (module M) } -> M.module_name t
    | Foreign { name }           -> name
    | App { f }                  -> functor_name f

  (* return a unique variable name holding the state of the given
     module construction. *)
  let rec name: type a. a impl -> string = function
    | Impl { t; m = (module M) } -> M.name t
    | Foreign { name }           -> Name.of_key ("f" ^ name) ~base:"f"
    | App _ as t                 -> Name.of_key (module_name t) ~base:"t"

  (* return a unique module name holding the implementation of the
     given module construction. *)
  and module_name: type a. a impl -> string = function
    | Impl { t; m = (module M) } -> M.module_name t
    | Foreign { name }           -> name
    | App { f; x }   ->
      let name = match module_names f @ [module_name x] with
        | []   -> assert false
        | [m]  -> m
        | h::t -> h ^ String.concat "" (List.map (Printf.sprintf "(%s)") t)
      in
      Name.of_key name ~base:"M"

  and module_names: type a. a impl -> string list =
    function t ->
      let fn = {
        fn = fun acc t -> module_name t :: acc
      } in
      fold fn t []

  let rec names: type a. a impl -> string list = function
    | Foreign _            -> []
    | Impl _ as t          -> [name t]
    | App {f=Foreign f; x} -> names x
    | App {f; x}           -> (names f) @ [name x]

  let configured = Hashtbl.create 31

  let rec configure: type a. a impl -> unit =
    fun t ->
      let name = name t in
      if not (Hashtbl.mem configured name) then (
        Hashtbl.add configured name true;
        match t with
        | Impl { t; m = (module M) } -> M.configure t
        | Foreign _                  -> ()
        | App {f; x} as  app         ->
          configure_app f;
          configure_app x;
          iter { i=configure } app;
          let name = module_name app in
          let body = cofind Name.names name in
          append_main "module %s = %s" name body;
          newline_main ();
      )

  and configure_app: type a. a impl -> unit = function
    | Impl _
    | Foreign _  -> ()
    | App _ as t ->
      let name = name t in
      configure t;
      begin match names t with
        | [n]   -> append_main "let %s = %s" name n
        | names ->
          append_main "let %s () =" name;
          List.iter (fun n ->
              append_main "  %s () >>= function" n;
              append_main "  | `Error e -> %s" (driver_initialisation_error n);
              append_main "  | `Ok %s ->" n;
            ) names;
          append_main "  return (`Ok (%s))" (String.concat ", " names)
      end;
      newline_main ()

  let rec packages: type a. a impl -> string list = function
    | Impl { t; m = (module M) } -> M.packages t
    | Foreign { packages }       -> packages
    | App {f; x}                 -> packages f @ packages x

  let rec libraries: type a. a impl -> string list = function
    | Impl { t; m = (module M) } -> M.libraries t
    | Foreign { libraries }      -> libraries
    | App {f; x}                 -> libraries f @ libraries x

  let rec clean: type a. a impl -> unit = function
    | Impl { t; m = (module M) } -> M.clean t
    | Foreign _                  -> ()
    | App {f; x}                 -> clean f; clean x

  let rec update_path: type a. a impl -> string -> a impl =
    fun t root -> match t with
      | Impl b     ->
        let module M = (val b.m) in Impl { b with t = M.update_path b.t root }
      | Foreign _  -> t
      | App {f; x} -> App { f = update_path f root; x = update_path x root }

end

let impl typ t m =
  Impl { typ; t; m }

let implementation typ t m =
  let typ = Type typ in
  Impl { typ; t; m }

let ($) f x =
  App { f; x }

let foreign name ?(libraries=[]) ?(packages=[]) ty =
  Foreign { name; ty; libraries; packages }

let rec typ: type a. a impl -> a typ = function
  | Impl { typ } -> typ
  | Foreign { ty } -> ty
  | App { f }       -> match typ f with Function (_, b) -> b | _ -> assert false


module Io_page = struct

  (** Memory allocation interface. *)

  type t = unit

  let name () =
    "io_page"

  let module_name () =
    "Io_page"

  let packages () = [
    "io-page"
  ]

  let libraries () =
    match !mode with
    | `Xen | `Solo5 -> ["io-page"]
    | `Unix | `MacOSX -> ["io-page"; "io-page.unix"]

  let configure () = ()

  let clean () = ()

  let update_path () _ = ()

end

type io_page = IO_PAGE
let io_page = Type IO_PAGE

let io_page_conf = object
  inherit base_configurable
  method ty = io_page
  method name = "io_page"
  method module_name = "Io_page"
  method libraries = Key.(if_ is_xen) ["io-page"; "io-page.unix"] ["io-page"]
  method packages = Key.pure [ "io-page" ]
end

let default_io_page = impl io_page_conf

type time = TIME
let time = Type TIME

let default_time: time impl =
  impl time () (module Time)

module Clock = struct

  (** Clock operations. *)

  type t = unit

  let name () =
    "clock"

  let module_name () =
    "Clock"

  let packages () = [
    match !mode with
    | `Unix | `MacOSX -> "mirage-clock-unix"
    | `Xen | `Solo5 -> "mirage-clock-xen"
  ]

  let libraries () = packages ()

  let configure () =
    append_main "let clock () = return (`Ok ())";
    newline_main ()

  let clean () = ()

  let update_path () _ = ()

end

let default_time = impl time_conf

type clock = CLOCK
let clock = Type CLOCK

let clock_conf = object (self)
  inherit base_configurable
  method ty = clock
  method name = "clock"
  method module_name = "Clock"
  method libraries = Key.(if_ is_xen) ["mirage-clock-xen"] ["mirage-clock-unix"]
  method packages = self#libraries
end

let default_clock = impl clock_conf

type random = RANDOM
let random = Type RANDOM

let default_random: random impl =
  impl random () (module Random)

module Console = struct

  type t = string

  let name t =
    Name.of_key ("console" ^ t) ~base:"console"

  let module_name t =
    "Console"

  let construction () =
    match !mode with
    | `Unix | `MacOSX -> "Console_unix"
    | `Xen  -> "Console_xen"
    | `Solo5  -> "Console_solo5"

  let packages _ =
    match !mode with
    | `Unix | `MacOSX -> ["mirage-console"; "mirage-unix"]
    | `Xen | `Solo5 -> ["mirage-console"; "xenstore"; "mirage-xen"; "xen-gnt"; "xen-evtchn"]

  let libraries _ =
    match !mode with
    | `Unix | `MacOSX -> ["mirage-console.unix"]
    | `Xen -> ["mirage-console.xen"]
    | `Solo5 -> ["mirage-console.xen"; "mirage-console.solo5"]

  let configure t =
    append_main "module %s = %s" (module_name t) (construction ());
    newline_main ();
    append_main "let %s () =" (name t);
    append_main "  %s.connect %S" (module_name t) t;
    newline_main ()

  let clean _ =
    ()

  let update_path t _ =
    t

end

let default_random = impl random_conf

type console = CONSOLE
let console = Type CONSOLE

let console_unix str = impl @@ object
    inherit base_configurable
    method ty = console
    val name = Name.ocamlify @@ "console_unix_" ^ str
    method name = name
    method module_name = "Console_unix"
    method packages = Key.pure ["mirage-console"; "mirage-unix"]
    method libraries = Key.pure ["mirage-console.unix"]
    method connect _ modname _args =
      Printf.sprintf "%s.connect %S" modname str
  end

let console_xen str = impl @@ object
    inherit base_configurable
    method ty = console
    val name = Name.ocamlify @@ "console_xen_" ^ str
    method name = name
    method module_name = "Console_xen"
    method packages = Key.pure
        ["mirage-console"; "xenstore"; "mirage-xen"; "xen-gnt"; "xen-evtchn"]
    method libraries = Key.pure ["mirage-console.xen"]
    method connect _ modname _args =
      Printf.sprintf "%s.connect %S" modname str
  end

let console_solo5 str = impl @@ object
    inherit base_configurable
    method ty = console
    val name = Name.ocamlify @@ "console_solo5_" ^ str
    method name = name
    method module_name = "Console_solo5"
    method packages = Key.pure
        ["mirage-console"; "mirage-solo5";]
    method libraries = Key.pure ["mirage-console.solo5"]
    method connect _ modname _args =
      Printf.sprintf "%s.connect %S" modname str
  end

let custom_console str =
  match_impl Key.(value target) [
  `Xen, console_xen str ;
  `Solo5,  console_solo5 str ;
] ~default:(console_unix str)

let default_console = custom_console "0"

type kv_ro = KV_RO
let kv_ro = Type KV_RO


let crunch dirname =
  impl kv_ro dirname (module Crunch)

module Direct_kv_ro = struct

  include Crunch

  let module_name t =
    match !mode with
    | `Xen | `Solo5 -> Crunch.module_name t
    | `Unix | `MacOSX -> "Kvro_fs_unix"

  let packages t =
    match !mode with
    | `Xen | `Solo5 -> Crunch.packages t
    | `Unix | `MacOSX -> "mirage-fs-unix" :: Crunch.packages t

  let libraries t =
    match !mode with
    | `Xen | `Solo5 -> Crunch.libraries t
    | `Unix | `MacOSX -> "mirage-fs-unix" :: Crunch.libraries t

  let configure t =
    match !mode with
    | `Xen | `Solo5 -> Crunch.configure t
    | `Unix | `MacOSX ->
      append_main "let %s () =" (name t);
      append_main "  Kvro_fs_unix.connect %S" t

end

let direct_kv_ro dirname =
  match_impl Key.(value target) [
  `Xen, crunch dirname ;
  `Solo5,  crunch dirname ;
] ~default:(direct_kv_ro_conf dirname)

type block = BLOCK
let block = Type BLOCK
type block_t = { filename: string; number: int }
let all_blocks = Hashtbl.create 7

let make_block_t =
  (* NB: reserve number 0 for the boot disk *)
  let next_number = ref 1 in
  fun filename ->
    let b =
      if Hashtbl.mem all_blocks filename
      then Hashtbl.find all_blocks filename
      else begin
        let number = !next_number in
        incr next_number;
        let b = { filename; number } in
        Hashtbl.add all_blocks filename b;
        b
      end in
    b

class block_conf file =
  let b = make_block_t file in
  let name = Name.create file ~prefix:"block" in
  object (self)
    inherit base_configurable
    method ty = block
    method name = name
    method module_name = "Block"
    method packages = Key.(if_ is_xen) ["mirage-block-xen"] ["mirage-block-unix"]
    method libraries =
      Key.(if_ is_xen) ["mirage-block-xen.front"] ["mirage-block-unix"]

    method private connect_name target root =
      match target with
      | `Unix | `MacOSX -> root / b.filename (* open the file directly *)
      | `Xen ->
        (* We need the xenstore id *)
        (* Taken from https://github.com/mirage/mirage-block-xen/blob/
           a64d152586c7ebc1d23c5adaa4ddd440b45a3a83/lib/device_number.ml#L64 *)
        (if b. number < 16
         then (202 lsl 8) lor (b.number lsl 4)
         else (1 lsl 28)  lor (b.number lsl 8)) |> string_of_int

    method connect i s _ =
      Printf.sprintf "%s.connect %S" s
        (self#connect_name (get_target i) @@ Info.root i)

  end

let block_of_file file = impl (new block_conf file)

let tar_block dir =
  let name = Name.create ("tar_block" ^ dir) ~prefix:"tar_block" in
  let block_file = name ^ ".img" in
  impl @@ object
    inherit block_conf block_file as super
    method configure i =
      Cmd.run "tar -C %s -cvf %s ." dir block_file >>= fun () ->
      super#configure i
  end

let archive_conf = impl @@ object
    inherit base_configurable
    method ty = block @-> kv_ro
    method name = "archive"
    method module_name = "Tar_mirage.Make_KV_RO"
    method packages = Key.pure [ "tar-format" ]
    method libraries = Key.pure [ "tar.mirage" ]
    method connect _ modname = function
      | [ block ] ->
        Fmt.strf "%s.connect %s" modname block
      | _ -> failwith "The archive connect should receive exactly one argument."

  end

let archive block = archive_conf $ block
let archive_of_files ?(dir=".") () = archive @@ tar_block dir

type fs = FS
let fs = Type FS

let fat ?(io_page=default_io_page) block: fs impl =
  let t = { Fat.block; io_page } in
  impl fs t (module Fat)

(* This would deserve to be in its own lib. *)
let kv_ro_of_fs x: kv_ro impl =
  let dummy_fat = fat (block_of_file "xx") in
  let libraries = Impl.libraries dummy_fat in
  let packages = Impl.packages dummy_fat in
  let fn = foreign "Fat.KV_RO.Make" ~libraries ~packages (fs @-> kv_ro) in
  fn $ x

module Fat_of_files = struct

  type t = {
    dir   : string option;
    regexp: string;
  }

  let name t =
    Name.of_key
      ("fat" ^ (match t.dir with None -> "." | Some d -> d) ^ ":" ^ t.regexp)
      ~base:"fat"

  let module_name t =
    String.capitalize (name t)

  let block_file t =
    name t ^ ".img"

  let block t =
    block_of_file (block_file t)

  let packages t =
    Impl.packages (fat (block t))

  let libraries t =
    Impl.libraries (fat (block t))

  let configure t =
    let fat = fat (block t) in
    Impl.configure fat;
    append_main "module %s = %s" (module_name t) (Impl.module_name fat);
    append_main "let %s = %s" (name t) (Impl.name fat);
    newline_main ();
    let file = Printf.sprintf "make-%s-image.sh" (name t) in
    let oc = open_out file in
    append oc "#!/bin/sh";
    append oc "";
    append oc "echo This uses the 'fat' command-line tool to build a simple FAT";
    append oc "echo filesystem image.";
    append oc "";
    append oc "FAT=$(which fat)";
    append oc "if [ ! -x \"${FAT}\" ]; then";
    append oc "  echo I couldn\\'t find the 'fat' command-line tool.";
    append oc "  echo Try running 'opam install fat-filesystem'";
    append oc "  exit 1";
    append oc "fi";
    append oc "";
    append oc "IMG=$(pwd)/%s" (block_file t);
    append oc "rm -f ${IMG}";
    (match t.dir with None -> () | Some d -> append oc "cd %s/" d);
    append oc "SIZE=$(du -s . | cut -f 1)";
    append oc "${FAT} create ${IMG} ${SIZE}KiB";
    append oc "${FAT} add ${IMG} %s" t.regexp;
    append oc "echo Created '%s'" (block_file t);

    close_out oc;
    Unix.chmod file 0o755;
    command "./make-%s-image.sh" (name t)

  let clean t =
    command "rm -f make-%s-image.sh %s" (name t) (block_file t);
    Impl.clean (block t)

  let update_path t root =
    match t.dir with
    | None   -> t
    | Some d -> { t with dir = Some (root / d) }

end

let fat_of_files: ?dir:string -> ?regexp:string -> unit -> fs impl =
  fun ?dir ?regexp () ->
    let regexp = match regexp with
      | None   -> "*"
      | Some r -> r in
    impl fs { Fat_of_files.dir; regexp } (module Fat_of_files)

type network_config = Tap0 | Custom of string

module Network = struct

  type t = network_config

  let name t =
    "net_" ^ match t with
    | Tap0     -> "tap0"
    | Custom s -> s

  let module_name _ =
    "Netif"

  let packages t =
    match !mode with
    | `Unix -> ["mirage-net-unix"]
    | `MacOSX -> ["mirage-net-macosx"]
    | `Xen -> ["mirage-net-xen"]
    | `Solo5 -> ["mirage-net-solo5"]

  let libraries t =
    packages t

  let configure t =
    append_main "let %s () =" (name t);
    append_main "  %s.connect %S"
      (module_name t)
      (match t with Tap0 -> "tap0" | Custom s -> s);
    newline_main ()

  let clean _ =
    ()

  let update_path t _ =
    t

end

type network = NETWORK
let network = Type NETWORK

let all_networks = ref []

let network_conf (intf : string Key.key) =
  let key = Key.abstract intf in
  object (self)
    inherit base_configurable
    method ty = network
    val name = Functoria_app.Name.create "net" ~prefix:"net"
    method name = name
    method module_name = "Netif"
    method keys = [ key ]

    method packages =
      Key.match_ Key.(value target) @@ function
      | `Unix   -> ["mirage-net-unix"]
      | `MacOSX -> ["mirage-net-macosx"]
      | `Xen    -> ["mirage-net-xen"]

    method libraries = self#packages

    method connect _ modname _ =
      Fmt.strf "%s.connect %a" modname Key.serialize_call key

  let libraries t =
    Impl.libraries t @
    match !mode with
    | `Unix | `MacOSX -> [ "tcpip.ethif-unix" ]
    | `Xen | `Solo5 -> [ "tcpip.ethif" ]

  end

let netif ?group dev = impl (network_conf @@ Key.network ?group dev)
let tap0 = netif "tap0"

type ethernet = ETHERNET
let ethernet = Type ETHERNET

let ethernet_conf = object
  inherit base_configurable
  method ty = network @-> ethernet
  method name = "ethif"
  method module_name = "Ethif.Make"
  method packages = Key.pure ["tcpip"]
  method libraries = Key.pure ["tcpip.ethif"]
  method connect _ modname = function
    | [ eth ] -> Printf.sprintf "%s.connect %s" modname eth
    | _ -> failwith "The ethernet connect should receive exactly one argument."
end

let etif_func = impl ethernet_conf
let etif network = etif_func $ network

type arpv4 = Arpv4
let arpv4 = Type Arpv4

let arpv4_conf = object
  inherit base_configurable
  method ty = ethernet @-> clock @-> time @-> arpv4
  method name = "arpv4"
  method module_name = "Arpv4.Make"
  method packages = Key.pure ["tcpip"]
  method libraries = Key.pure ["tcpip.arpv4"]

  method connect _ modname = function
    | [ eth ; _clock ; _time ] -> Printf.sprintf "%s.connect %s" modname eth
    | _ -> failwith "The arpv4 connect should receive exactly three arguments."

end

let arp_func = impl arpv4_conf
let arp ?(clock = default_clock) ?(time = default_time) (eth : ethernet impl) =
  arp_func $ eth $ clock $ time

type ('ipaddr, 'prefix) ip_config = {
  address: 'ipaddr;
  netmask: 'prefix;
  gateways: 'ipaddr list;
}

type ipv4_config = (Ipaddr.V4.t, Ipaddr.V4.t) ip_config

let meta_ipv4_config t =
  Printf.sprintf "(Ipaddr.V4.of_string_exn %S, Ipaddr.V4.of_string_exn %S, [%s])"
    (Ipaddr.V4.to_string t.address)
    (Ipaddr.V4.to_string t.netmask)
    (String.concat "; "
       (List.map (Printf.sprintf "Ipaddr.V4.of_string_exn %S")
          (List.map Ipaddr.V4.to_string t.gateways)))

module IPV4 = struct

  type t = {
    arpv4 : arpv4 impl;
    config  : ipv4_config;
  }
  (* XXX: should the type if ipv4.id be ipv4.t ?
     N.connect ethif |> N.set_ip up *)

  let name t =
    let key = "ipv4" ^ Impl.name t.arpv4 ^ meta_ipv4_config t.config in
    Name.of_key key ~base:"ipv4"

  let module_name t =
    String.capitalize (name t)

  let packages t =
    "tcpip" :: Impl.packages t.arpv4 

  let libraries t  =
    (match !mode with
     | `Unix | `MacOSX -> [ "tcpip.ipv4-unix" ]
     | `Xen | `Solo5 -> [ "tcpip.ipv4" ])
    @ Impl.libraries t.arpv4

  let configure t =
    let name = name t in
    let mname = module_name t in
    Impl.configure t.arpv4;
    append_main "module %s = Ipv4.Make(%s)"
      (module_name t) (Impl.module_name t.arpv4);
    newline_main ();
    append_main "let %s () =" name;
    append_main "   %s () >>= function" (Impl.name t.arpv4);
    append_main "   | `Error _ -> %s" (driver_initialisation_error name);
    append_main "   | `Ok arp ->";
    append_main "   %s.connect arp >>= function" mname;
    append_main "   | `Error _ -> %s" (driver_initialisation_error "IPV4");
    append_main "   | `Ok ip   ->";
    append_main "   let i = Ipaddr.V4.of_string_exn in";
    append_main "   %s.set_ip ip (i %S) >>= fun () ->"
      mname (Ipaddr.V4.to_string t.config.address);
    append_main "   %s.set_ip_netmask ip (i %S) >>= fun () ->"
      mname (Ipaddr.V4.to_string t.config.netmask);
    append_main "   %s.set_ip_gateways ip [%s] >>= fun () ->"
      mname
      (String.concat "; "
         (List.map
            (fun n -> Printf.sprintf "(i %S)" (Ipaddr.V4.to_string n))
            t.config.gateways));
    append_main "   return (`Ok ip)";
    newline_main ()

  let clean t =
    Impl.clean t.arpv4

  let update_path t root =
    { t with arpv4 = Impl.update_path t.arpv4 root }

end

type ipv6_config = (Ipaddr.V6.t, Ipaddr.V6.Prefix.t list) ip_config

let meta_ipv6_config t =
  Printf.sprintf "(Ipaddr.V6.of_string_exn %S, [%s], [%s])"
    (Ipaddr.V6.to_string t.address)
    (String.concat "; "
       (List.map (Printf.sprintf "Ipaddr.V6.Prefix.of_string_exn %S")
          (List.map Ipaddr.V6.Prefix.to_string t.netmask)))
    (String.concat "; "
       (List.map (Printf.sprintf "Ipaddr.V6.of_string_exn %S")
          (List.map Ipaddr.V6.to_string t.gateways)))

module IPV6 = struct

  type t = {
    time    : time impl;
    clock   : clock impl;
    ethernet: ethernet impl;
    config  : ipv6_config;
  }
  (* XXX: should the type if ipv4.id be ipv4.t ?
     N.connect ethif |> N.set_ip up *)

  let name t =
    let key = "ipv6" ^ Impl.name t.time ^ Impl.name t.clock ^ Impl.name t.ethernet ^ meta_ipv6_config t.config in
    Name.of_key key ~base:"ipv6"

  let module_name t =
    String.capitalize (name t)

  let packages t =
    "tcpip" :: Impl.packages t.time @ Impl.packages t.clock @ Impl.packages t.ethernet

  let libraries t  =
    (match !mode with
     | `Unix | `MacOSX -> [ "tcpip.ipv6-unix" ]
     | `Xen | `Solo5 -> [ "tcpip.ipv6" ])
    @ Impl.libraries t.time @ Impl.libraries t.clock @ Impl.libraries t.ethernet

  let configure t =
    let name = name t in
    let mname = module_name t in
    Impl.configure t.ethernet;
    append_main "module %s = Ipv6.Make(%s)(%s)(%s)"
      (module_name t) (Impl.module_name t.ethernet) (Impl.module_name t.time) (Impl.module_name t.clock);
    newline_main ();
    append_main "let %s () =" name;
    append_main "   %s () >>= function" (Impl.name t.ethernet);
    append_main "   | `Error _ -> %s" (driver_initialisation_error name);
    append_main "   | `Ok eth  ->";
    append_main "   %s.connect eth >>= function" mname;
    append_main "   | `Error _ -> %s" (driver_initialisation_error name);
    append_main "   | `Ok ip   ->";
    append_main "   let i = Ipaddr.V6.of_string_exn in";
    append_main "   %s.set_ip ip (i %S) >>= fun () ->"
      mname (Ipaddr.V6.to_string t.config.address);
    List.iter begin fun netmask ->
      append_main "   %s.set_ip_netmask ip (i %S) >>= fun () ->"
        mname (Ipaddr.V6.Prefix.to_string netmask)
    end t.config.netmask;
    append_main "   %s.set_ip_gateways ip [%s] >>= fun () ->"
      mname
      (String.concat "; "
         (List.map
            (fun n -> Printf.sprintf "(i %S)" (Ipaddr.V6.to_string n))
            t.config.gateways));
    append_main "   return (`Ok ip)";
    newline_main ()

  let clean t =
    Impl.clean t.time;
    Impl.clean t.clock;
    Impl.clean t.ethernet

  let update_path t root =
    { t with
      time = Impl.update_path t.time root;
      clock = Impl.update_path t.clock root;
      ethernet = Impl.update_path t.ethernet root }

end

type v4
type v6
type 'a ip = IP
type ipv4 = v4 ip
type ipv6 = v6 ip

let ip = Type IP
let ipv4: ipv4 typ = ip
let ipv6: ipv6 typ = ip

let pp_triple ?(sep=Fmt.cut) ppx ppy ppz fmt (x,y,z) =
  ppx fmt x ; sep fmt () ; ppy fmt y ; sep fmt () ; ppz fmt z

let meta_triple ppx ppy ppz =
  Fmt.parens @@ pp_triple ~sep:(Fmt.unit ",@ ") ppx ppy ppz

let meta_ipv4 ppf s =
  Fmt.pf ppf "(Ipaddr.V4.of_string_exn %S)" (Ipaddr.V4.to_string s)

type ipv4_config = (Ipaddr.V4.t, Ipaddr.V4.t) ip_config

let pp_key fmt k = Key.serialize_call fmt (Key.abstract k)
let opt_key s = Fmt.(option @@ prefix (unit ("~"^^s)) pp_key)
let opt_map f = function Some x -> Some (f x) | None -> None
let (@?) x l = match x with Some s -> s :: l | None -> l
let (@??) x y = opt_map Key.abstract x @? y

let ipv4_conf ?address ?netmask ?gateways () = impl @@ object
    inherit base_configurable
    method ty = ethernet @-> arpv4 @-> ipv4
    method name = Name.create "ipv4" ~prefix:"ipv4"
    method module_name = "Ipv4.Make"
    method packages = Key.pure ["tcpip"]
    method libraries = Key.pure ["tcpip.ipv4"]
    method keys = address @?? netmask @?? gateways @?? []
    method connect _ modname = function
      | [ etif ; arp ] ->
        Fmt.strf
          "%s.connect@[@ %a@ %a@ %a@ %s@ %s@]"
          modname
          (opt_key "ip") address
          (opt_key "netmask") netmask
          (opt_key "gateways") gateways
          etif arp
      | _ -> failwith "The ipv4 connect should receive exactly two arguments."
  end

let create_ipv4
    ?(clock = default_clock) ?(time = default_time)
    ?group net { address ; netmask ; gateways } =
  let etif = etif net in
  let arp = arp ~clock ~time etif in
  let address = Key.V4.ip ?group address in
  let netmask = Key.V4.netmask ?group netmask in
  let gateways = Key.V4.gateways ?group gateways in
  ipv4_conf ~address ~netmask ~gateways () $ etif $ arp

let default_ipv4_conf =
  let i = Ipaddr.V4.of_string_exn in
  {
    address  = i "10.0.0.2";
    netmask  = i "255.255.255.0";
    gateways = [i "10.0.0.1"];
  }

let default_ipv4 ?group net = create_ipv4 ?group net default_ipv4_conf

type ipv6_config = (Ipaddr.V6.t, Ipaddr.V6.Prefix.t list) ip_config

let ipv6_conf ?address ?netmask ?gateways () = impl @@ object
    inherit base_configurable
    method ty = ethernet @-> time @-> clock @-> ipv6
    method name = Name.create "ipv6" ~prefix:"ipv6"
    method module_name = "Ipv6.Make"
    method packages = Key.pure ["tcpip"]
    method libraries = Key.pure ["tcpip.ipv6"]
    method keys = address @?? netmask @?? gateways @?? []
    method connect _ modname = function
      | [ etif ; _time ; _clock ] ->
        Fmt.strf
          "%s.connect@[@ %a@ %a@ %a@ %s@@]"
          modname
          (opt_key "ip") address
          (opt_key "netmask") netmask
          (opt_key "gateways") gateways
          etif
      | _ -> failwith "The ipv6 connect should receive exactly three arguments."
  end

let create_ipv6
    ?(time = default_time)
    ?(clock = default_clock)
    ?group net { address ; netmask ; gateways } =
  let etif = etif net in
  let address = Key.V6.ip ?group address in
  let netmask = Key.V6.netmask ?group netmask in
  let gateways = Key.V6.gateways ?group gateways in
  ipv6_conf ~address ~netmask ~gateways () $ etif $ time $ clock

type 'a icmp = ICMP
type icmpv4 = v4 icmp

let icmp = Type ICMP
let icmpv4: icmpv4 typ = icmp

let icmpv4_direct_conf () = object
  inherit base_configurable
  method ty : ('a ip -> 'a icmp) typ = ip @-> icmp
  method name = "icmpv4"
  method module_name = "Icmpv4.Make"
  method packages = Key.pure [ "tcpip" ]
  method libraries = Key.pure [ "tcpip.icmpv4" ]
  method connect _ modname = function
    | [ ip ] -> Printf.sprintf "%s.connect %s" modname ip
    | _  -> failwith "The icmpv4 connect should receive exactly one argument."
end

module UDPV4_socket = struct

  type t = Ipaddr.V4.t option

  let name _ = "udpv4_socket"

  let module_name _ = "Udpv4_socket"

  let packages t = [ "tcpip" ]

  let libraries t =
    match !mode with
    | `Unix | `MacOSX -> [ "tcpip.udpv4-socket" ]
    | `Xen | `Solo5 -> failwith "No socket implementation available for Xen"

  let configure t =
    append_main "let %s () =" (name t);
    let ip = match t with
      | None    -> "None"
      | Some ip ->
        Printf.sprintf "Some (Ipaddr.V4.of_string_exn %s)" (Ipaddr.V4.to_string ip)
    in
    append_main " %s.connect %S" (module_name t) ip;
    newline_main ()

  let clean t =
    ()

  let update_path t root =
    t

end

type 'a udp = UDP
type udpv4 = v4 udp
type udpv6 = v6 udp

let udp = Type UDP
let udpv4: udpv4 typ = udp
let udpv6: udpv6 typ = udp

(* Value restriction ... *)
let udp_direct_conf () = object
  inherit base_configurable
  method ty : ('a ip -> 'a udp) typ = ip @-> udp
  method name = "udp"
  method module_name = "Udp.Make"
  method packages = Key.pure [ "tcpip" ]
  method libraries = Key.pure [ "tcpip.udp" ]
  method connect _ modname = function
    | [ ip ] -> Printf.sprintf "%s.connect %s" modname ip
    | _  -> failwith "The udpv6 connect should receive exactly one argument."
end

module TCPV4_socket = struct

  type t = Ipaddr.V4.t option

  let name _ = "tcpv4_socket"

  let module_name _ = "Tcpv4_socket"

  let packages t = [ "tcpip" ]

  let libraries t =
    match !mode with
    | `Unix | `MacOSX -> [ "tcpip.tcpv4-socket" ]
    | `Xen | `Solo5 -> failwith "No socket implementation available for Xen"

  let configure t =
    append_main "let %s () =" (name t);
    let ip = match t with
      | None    -> "None"
      | Some ip ->
        Printf.sprintf "Some (Ipaddr.V4.of_string_exn %s)" (Ipaddr.V4.to_string ip)
    in
    append_main "  %s.connect %S" (module_name t) ip;
    newline_main ()

  let clean t =
    ()

  let update_path t root =
    t

end

let socket_udpv4 ?group ip = impl (udpv4_socket_conf @@ Key.V4.socket ?group ip)

type 'a tcp = TCP
type tcpv4 = v4 tcp
type tcpv6 = v6 tcp

let tcp = Type TCP
let tcpv4 : tcpv4 typ = tcp
let tcpv6 : tcpv6 typ = tcp

(* Value restriction ... *)
let tcp_direct_conf () = object
  inherit base_configurable
  method ty =
    (ip: 'a ip typ) @-> time @-> clock @-> random @-> (tcp: 'a tcp typ)
  method name = "tcp"
  method module_name = "Tcp.Flow.Make"
  method packages = Key.pure [ "tcpip" ]
  method libraries = Key.pure [ "tcpip.tcp" ]
  method connect _ modname = function
    | [ip; _time; _clock; _random] -> Printf.sprintf "%s.connect %s" modname ip
    | _ -> failwith "The tcp connect should receive exactly four arguments."
end

(* Value restriction ... *)
let tcp_direct_func () = impl (tcp_direct_conf ())

let direct_tcp
    ?(clock=default_clock) ?(random=default_random) ?(time=default_time) ip =
  tcp_direct_func () $ ip $ time $ clock $ random

let tcpv4_socket_conf ipv4_key = object
  inherit base_configurable
  method ty = tcpv4
  val name = Name.create "tcpv4_socket" ~prefix:"tcpv4_socket"
  method name = name
  method module_name = "Tcpv4_socket"
  method keys = [ Key.abstract ipv4_key ]
  method packages = Key.pure [ "tcpip" ]
  method libraries =
    Key.match_ Key.(value target) @@ function
    | `Unix | `MacOSX -> [ "tcpip.tcpv4-socket" ]
    | `Xen  -> failwith "No socket implementation available for Xen"
  method connect _ modname _ =
    Format.asprintf "%s.connect %a" modname  pp_key ipv4_key
end

let socket_tcpv4 ?group ip = impl (tcpv4_socket_conf @@ Key.V4.socket ?group ip)

type stackv4 = STACKV4
let stackv4 = Type STACKV4

let pp_stackv4_config fmt = function
  | `DHCP   -> Fmt.pf fmt "`DHCP"
  | `IPV4 i -> Fmt.pf fmt "`IPv4 %a" (meta_triple pp_key pp_key pp_key) i

let add_suffix s ~suffix = if suffix = "" then s else s^"_"^suffix

let stackv4_direct_conf ?(group="") config = impl @@ object
    inherit base_configurable

    method ty =
      console @-> time @-> random @-> network @->
      ethernet @-> arpv4 @-> ipv4 @-> icmpv4 @-> udpv4 @-> tcpv4 @->
      stackv4

    val name =
      let base = match config with
        | `DHCP -> "dhcp"
        | `IPV4 _ -> "ip"
      in add_suffix ("stackv4_" ^ base) ~suffix:group

    method name = name
    method module_name = "Tcpip_stack_direct.Make"

    method keys = match config with
      | `DHCP -> []
      | `IPV4 (addr,netm,gate) -> [
          Key.abstract addr;
          Key.abstract netm;
          Key.abstract gate
        ]

    method packages = Key.pure [ "tcpip" ]
    method libraries = Key.pure [ "tcpip.stack-direct" ; "mirage.runtime" ]

    method connect _i modname = function
      | [ console; _t; _r; interface; ethif; arp; ip; icmp; udp; tcp ] ->
        Fmt.strf
          "@[<2>let config = {V1_LWT.@ \
           name = %S;@ console = %s;@ \
           interface = %s;@ mode = %a }@]@ in@ \
           %s.connect config@ %s %s %s %s %s %s"
          name console
          interface  pp_stackv4_config config
          modname ethif arp ip icmp udp tcp
      | _ -> failwith "Wrong arguments to connect to tcpip direct stack."

  end


let direct_stackv4_with_config
    ?(clock=default_clock)
    ?(random=default_random)
    ?(time=default_time)
    ?group
    console network config =
  let eth = etif_func $ network in
  let arp = arp ~clock ~time eth in
  let ip = ipv4_conf () $ eth $ arp in
  stackv4_direct_conf ?group config
  $ console $ time $ random $ network
  $ eth $ arp $ ip
  $ direct_icmpv4 ip
  $ direct_udp ip
  $ direct_tcp ~clock ~random ~time ip

let direct_stackv4_with_dhcp
    ?clock ?random ?time ?group console network =
  direct_stackv4_with_config
    ?clock ?random ?time ?group console network `DHCP

let direct_stackv4_with_static_ipv4
    ?clock ?random ?time ?group console network
    {address; netmask; gateways} =
  let address = Key.V4.ip ?group address in
  let netmask = Key.V4.netmask ?group netmask in
  let gateways = Key.V4.gateways ?group gateways in
  direct_stackv4_with_config
    ?clock ?random ?time ?group console network
    (`IPV4 (address, netmask, gateways))

let direct_stackv4_with_default_ipv4
    ?clock ?random ?time ?group console network =
  direct_stackv4_with_static_ipv4
    ?clock ?random ?time ?group console network
    default_ipv4_conf

let stackv4_socket_conf ?(group="") interfaces = impl @@ object
    inherit base_configurable
    method ty = console @-> stackv4
    val name = add_suffix "stackv4_socket" ~suffix:group
    method name = name
    method module_name = "Tcpip_stack_socket.Make"
    method keys = [ Key.abstract interfaces ]
    method packages = Key.pure [ "tcpip" ]
    method libraries = Key.pure [ "tcpip.stack-socket" ]
    method deps = [
      abstract (socket_udpv4 None);
      abstract (socket_tcpv4 None);
    ]

    method connect _i modname = function
      | [ console ; udpv4 ; tcpv4 ] ->
        Fmt.strf
          "let config =@[@ \
           { V1_LWT.name = %S;@ console = %s ;@ \
           interface = %a ;@ mode = () }@] in@ \
           %s.connect config %s %s"
          name
          console  pp_key interfaces
          modname udpv4 tcpv4
      | _ -> failwith "Wrong arguments to connect to tcpip socket stack."

  end

let socket_stackv4 ?group console ipv4s =
  stackv4_socket_conf ?group (Key.V4.interfaces ?group ipv4s) $ console

(** Generic stack *)

let generic_stackv4
    ?group
    ?(dhcp_key = Key.value @@ Key.dhcp ?group ())
    ?(net_key = Key.value @@ Key.net ?group ())
    console tap =
  if_impl
    Key.(pure ((=) `Socket) $ net_key)
    (socket_stackv4 console ?group [Ipaddr.V4.any])
    (if_impl
       dhcp_key
       (direct_stackv4_with_dhcp ?group console tap)
       (direct_stackv4_with_default_ipv4 ?group console tap)
    )

(* This is to check that entropy is a dependency if "tls" is in
   the package array. *)
let enable_entropy, is_entropy_enabled =
  let r = ref false in
  let f () = r := true in
  let g () = !r in
  (f, g)

let check_entropy libs =
  Cmd.OCamlfind.query ~recursive:true libs
  >>| List.exists ((=) "nocrypto")
  >>= fun is_needed ->
  if is_needed && not (is_entropy_enabled ()) then
    Log.error
      "The \"nocrypto\" library is loaded but entropy is not enabled!@ \
       Please enable the entropy by adding a dependency to the nocrypto \
       device. You can do so by adding ~deps:[abstract nocrypto] \
       to the arguments of Mirage.foreign."
  else R.ok ()

let nocrypto = impl @@ object
    inherit base_configurable
    method ty = job
    method name = "nocrypto"
    method module_name = "Nocrypto_entropy"

    method packages =
      Key.(if_ is_xen)
        [ "nocrypto" ; "mirage-entropy-xen" ; "zarith-xen" ]
        [ "nocrypto" ]

    method libraries =
      Key.(if_ is_xen)
        ["nocrypto.xen"]
        ["nocrypto.lwt"]

    method configure _ = R.ok (enable_entropy ())
    method connect i _ _ =
      let s = if Key.(eval (Info.context i) is_xen)
        then "Nocrypto_entropy_xen.initialize ()"
        else "Nocrypto_entropy_lwt.initialize ()"
      in
      Fmt.strf "%s >|= fun x -> `Ok x" s

  end

type conduit_connector = Conduit_connector
let conduit_connector = Type Conduit_connector

let tcp_conduit_connector = impl @@ object
    inherit base_configurable
    method ty = stackv4 @-> conduit_connector
    method name = "tcp_conduit_connector"
    method module_name = "Conduit_mirage.With_tcp"
    method packages = Key.pure [ "mirage-conduit" ]
    method libraries = Key.pure [ "conduit.mirage" ]
    method connect _ modname = function
      | [ stack ] ->
        Fmt.strf "let f = %s.connect %s in@ return (`Ok f)@;" modname stack
      | _ -> failwith "Wrong arguments to connect to tcp conduit connector."
  end

let tls_conduit_connector = impl @@ object
    inherit base_configurable
    method ty = conduit_connector
    method name = "tls_conduit_connector"
    method module_name = "Conduit_mirage"
    method packages = Key.pure [ "mirage-conduit" ; "tls" ]
    method libraries = Key.pure [ "conduit.mirage" ; "tls.mirage" ]
    method deps = [ abstract nocrypto ]
    method connect _ _ _ = "return (`Ok Conduit_mirage.with_tls)"
  end

type conduit = Conduit
let conduit = Type Conduit

let conduit_direct ?(tls=false) s =
  impl conduit { Conduit.stackv4 = Some s; tls } (module Conduit)

module Resolver_unix = struct
  type t = unit

  let name t =
    let key = "resolver_unix" in
    Name.of_key key ~base:"resolver"

  let module_name t =
    String.capitalize (name t)

  let packages t =
    match !mode with
    |`Unix | `MacOSX -> [ "mirage-conduit" ]
    |`Xen | `Solo5 -> failwith "Resolver_unix not supported on Xen"

  let libraries t =
    [ "conduit.mirage"; "conduit.lwt-unix" ]

  let configure t =
    append_main "module %s = Resolver_lwt" (module_name t);
    append_main "let %s () =" (name t);
    append_main "  return (`Ok Resolver_lwt_unix.system)";
    newline_main ()

  let clean t = ()

  let update_path t root = t

let conduit_direct ?(tls=false) s =
  (* TCP must be before tls in the list. *)
  let connectors = [tcp_conduit_connector $ s] in
  let connectors =
    if tls
    then connectors @ [tls_conduit_connector]
    else connectors
  in
  conduit_with_connectors connectors

type resolver = Resolver
let resolver = Type Resolver

let resolver_unix_system = impl @@ object
    inherit base_configurable
    method ty = resolver
    method name = "resolver_unix"
    method module_name = "Resolver_lwt"
    method packages =
      Key.match_ Key.(value target) @@ function
      | `Unix | `MacOSX -> [ "mirage-conduit" ]
      | `Xen -> failwith "Resolver_unix not supported on Xen"
    method libraries = Key.pure [ "conduit.mirage"; "conduit.lwt-unix" ]
    method connect _ _modname _ = "return (`Ok Resolver_lwt_unix.system)"
  end

let resolver_dns_conf ~ns ~ns_port = impl @@ object
    inherit base_configurable
    method ty = time @-> stackv4 @-> resolver
    method name = "resolver"
    method module_name = "Resolver_mirage.Make_with_stack"
    method packages = Key.pure [ "dns"; "tcpip" ]
    method libraries = Key.pure [ "dns.mirage" ]

    method connect _ modname = function
      | [ _t ; stack ] ->
        let meta_ns = Fmt.Dump.option meta_ipv4 in
        let meta_port = Fmt.(Dump.option int) in
        Fmt.strf
          "let ns = %a in@;\
           let ns_port = %a in@;\
           let res = %s.R.init ?ns ?ns_port ~stack:%s () in@;\
           return (`Ok res)@;"
          meta_ns ns
          meta_port ns_port
          modname stack
      | _ -> failwith "The resolver connect should receive exactly two arguments."

  end

let resolver_dns ?ns ?ns_port ?(time = default_time) stack =
  resolver_dns_conf ~ns ~ns_port $ time $ stack

type http = HTTP
let http = Type HTTP

let http_server conduit = impl http { HTTP.conduit } (module HTTP)

type job = JOB

let job = Type JOB

module Job = struct

  type t = {
    name: string;
    impl: job impl;
  }

  let create impl =
    let name = Name.create "job" in
    { name; impl }

  let name t =
    t.name

  let module_name t =
    "Job_" ^ t.name

  let packages t =
    Impl.packages t.impl

  let libraries t =
    Impl.libraries t.impl

  let configure t =
    Impl.configure t.impl;
    newline_main ()

  let clean t =
    Impl.clean t.impl

  let update_path t root =
    { t with impl = Impl.update_path t.impl root }

let argv_solo5 = impl @@ object
    inherit base_configurable
    method ty = Functoria_app.argv
    method name = "argv_solo5"
    method module_name = "Bootvar"
    method packages = Key.pure [ "mirage-bootvar-solo5" ]
    method libraries = Key.pure [ "mirage-bootvar" ]
    method connect _ _ _ = "Bootvar.argv ()"
  end

let argv_dynamic =
  match_impl Key.(value target) [
  `Xen, argv_xen ;
  `Solo5, argv_solo5 ;
] ~default:(argv_unix)

  let libraries _ =
    match !mode with
    | `Unix | `MacOSX -> StringSet.singleton "mirage-profile.unix"
    | `Xen | `Solo5 -> StringSet.singleton "mirage-profile.xen"

  let configure t =
    if Sys.command "ocamlfind query lwt.tracing 2>/dev/null" <> 0 then (
      flush stdout;
      error "lwt.tracing module not found. Hint:\n\
             opam pin add lwt 'https://github.com/mirage/lwt.git#tracing'"
    );

    append_main "let () = ";
    begin match !mode with
    | `Unix | `MacOSX ->
        append_main "  let buffer = MProf_unix.mmap_buffer ~size:%d %S in" t.size unix_trace_file;
        append_main "  let trace_config = MProf.Trace.Control.make buffer MProf_unix.timestamper in";
        append_main "  MProf.Trace.Control.start trace_config";
    | `Xen | `Solo5 ->
        append_main "  let trace_pages = MProf_xen.make_shared_buffer ~size:%d in" t.size;
        append_main "  let buffer = trace_pages |> Io_page.to_cstruct |> Cstruct.to_bigarray in";
        append_main "  let trace_config = MProf.Trace.Control.make buffer MProf_xen.timestamper in";
        append_main "  MProf.Trace.Control.start trace_config;";
        append_main "  MProf_xen.share_with (module Gnt.Gntshr) (module OS.Xs) ~domid:0 trace_pages";
        append_main "  |> OS.Main.run";
    end;
    newline_main ()
end

type tracing = Tracing.t

let mprof_trace ~size () =
  { Tracing.size }

module Nocrypto_entropy = struct

  (* XXX
   * Nocrypto needs `mirage-entropy-xen` if compiled for xen.
   * This is currently handled by always installing this library, regardless of
   * usage of Nocrypto.
   * As `libraries` is run after opam setup, it will correctly detect Nocrypto
   * usage and inject appropriate deps for linkage, if needed.
   * The `packages` function, unconditional installation of
   * `mirage-entropy-xen`, and this comment, should be cleared once we have
   * conditional dependencies support in opam.
   * See https://github.com/mirage/mirage/pull/394 for discussion.
   *)

  module SS = StringSet

  let remembering r f =
    match !r with
    | Some x -> x
    | None   -> let x = f () in r := Some x ; x

  let linkage_ = ref None

  let linkage () =
    match !linkage_ with
    | None   -> failwith "Nocrypto_entropy: `linkage` queried before `libraries`"
    | Some x -> x

  let packages () =
    match !mode with
    | `Xen -> SS.singleton "mirage-entropy-xen"
    | _    -> SS.empty

  let libraries libs =
    remembering linkage_ @@ fun () ->
      let needed =
        OCamlfind.query ~recursive:true (SS.elements libs)
          |> List.exists ((=) "nocrypto") in
      match !mode with
      | (`Xen  | `Solo5)  when needed -> SS.singleton "nocrypto.xen"
      | (`Unix | `MacOSX) when needed -> SS.singleton "nocrypto.lwt"
      | _                             -> SS.empty

  let configure () =
    SS.elements (linkage ()) |> List.iter (fun lib ->
      if not (OCamlfind.installed lib) then
        error "%s module not found. Hint: reinstall nocrypto." lib
      )

  let preamble () =
    match (!mode, not (SS.is_empty @@ linkage ())) with
    | ((`Xen  | `Solo5), true) -> "Nocrypto_entropy_xen.initialize ()"
    | ((`Unix | `MacOSX), true) -> "Nocrypto_entropy_lwt.initialize ()"
    | _                         -> "return_unit"
end

type t = {
  name: string;
  root: string;
  jobs: job impl list;
  tracing: tracing option;
}

let t = ref None

let config_file = ref None

let reset () =
  config_file := None;
  t := None

let set_config_file f =
  config_file := Some f

let get_config_file () =
  match !config_file with
  | None -> Sys.getcwd () / "config.ml"
  | Some f -> f

let update_path t root =
  { t with jobs = List.map (fun j -> Impl.update_path j root) t.jobs }

let register ?tracing name jobs =
  let root = match !config_file with
    | None   -> failwith "no config file"
    | Some f -> Filename.dirname f in
  t := Some { name; jobs; root; tracing }

let registered () =
  match !t with
  | None   -> { name = "empty"; jobs = []; root = Sys.getcwd (); tracing = None }
  | Some t -> t

let ps = ref StringSet.empty

let add_to_opam_packages p =
  ps := StringSet.union (StringSet.of_list p) !ps

let packages t =
  let m = match !mode with
    | `Unix | `MacOSX -> "mirage-unix"
    | `Xen | `Solo5 -> "mirage-xen" in
  let ps = StringSet.add m !ps in
  let ps = match t.tracing with
    | None -> ps
    | Some tracing -> StringSet.union (Tracing.packages tracing) ps in
  let ps = List.fold_left (fun set j ->
      let ps = StringSet.of_list (Impl.packages j) in
      StringSet.union ps set
    ) ps t.jobs in
  let ps = StringSet.union ps (Nocrypto_entropy.packages ()) in
  StringSet.elements ps

let ls = ref StringSet.empty

let add_to_ocamlfind_libraries l =
  ls := StringSet.union !ls (StringSet.of_list l)

let libraries t =
  let m = match !mode with
    | `Unix | `MacOSX -> "mirage-types.lwt"
    | `Xen | `Solo5 -> "mirage-types.lwt" in
  let ls = StringSet.add m !ls in
  let ls = match t.tracing with
    | None -> ls
    | Some tracing -> StringSet.union (Tracing.libraries tracing) ls in
  let ls = List.fold_left (fun set j ->
      let ls = StringSet.of_list (Impl.libraries j) in
      StringSet.union ls set
    ) ls t.jobs in
  let ls = StringSet.union ls (Nocrypto_entropy.libraries ls) in
  StringSet.elements ls

let configure_myocamlbuild_ml t =
  let minor, major = ocaml_version () in
  if minor < 4 || major < 1 then (
    (* Previous ocamlbuild versions weren't able to understand the
       --output-obj rules *)
    let file = t.root / "myocamlbuild.ml" in
    let oc = open_out file in
    append oc "(* %s *)" generated_by_mirage;
    newline oc;
    append oc
      "open Ocamlbuild_pack;;\n\
       open Ocamlbuild_plugin;;\n\
       open Ocaml_compiler;;\n\
       \n\
       let native_link_gen linker =\n\
      \  link_gen \"cmx\" \"cmxa\" !Options.ext_lib [!Options.ext_obj; \"cmi\"] linker;;\n\
       \n\
       let native_output_obj x = native_link_gen ocamlopt_link_prog\n\
      \  (fun tags -> tags++\"ocaml\"++\"link\"++\"native\"++\"output_obj\") x;;\n\
       \n\
       rule \"ocaml: cmx* & o* -> native.o\"\n\
      \  ~tags:[\"ocaml\"; \"native\"; \"output_obj\" ]\n\
      \  ~prod:\"%%.native.o\" ~deps:[\"%%.cmx\"; \"%%.o\"]\n\
      \  (native_output_obj \"%%.cmx\" \"%%.native.o\");;\n\
       \n\
       \n\
       let byte_link_gen = link_gen \"cmo\" \"cma\" \"cma\" [\"cmo\"; \"cmi\"];;\n\
       let byte_output_obj = byte_link_gen ocamlc_link_prog\n\
      \  (fun tags -> tags++\"ocaml\"++\"link\"++\"byte\"++\"output_obj\");;\n\
       \n\
       rule \"ocaml: cmo* -> byte.o\"\n\
      \  ~tags:[\"ocaml\"; \"byte\"; \"link\"; \"output_obj\" ]\n\
       ~prod:\"%%.byte.o\" ~dep:\"%%.cmo\"\n\
      \  (byte_output_obj \"%%.cmo\" \"%%.byte.o\");;";
    close_out oc
  )

let clean_main_libvirt_xml ~root ~name =
  Cmd.remove (root / name ^ "_libvirt.xml")

(* We generate an example .xl with common defaults, and a generic
   .xl.in which has @VARIABLES@ which must be substituted by sed
   according to the preferences of the system administrator.

   The common defaults chosen for the .xl file will be based on values
   detected from the build host. We assume that the .xl file will
   mainly be used by developers where build and deployment are on the
   same host. Production users should use the .xl.in and perform the
   appropriate variable substition.
*)

let detected_bridge_name =
  (* Best-effort guess of a bridge name stem to use. Note this
     inspects the build host and will probably be wrong if the
     deployment host is different.  *)
  match List.fold_left (fun sofar x -> match sofar with
      | None ->
        (* This is Linux-specific *)
        if Sys.file_exists (Printf.sprintf "/sys/class/net/%s0" x)
        then Some x
        else None
      | Some x -> Some x
    ) None [ "xenbr"; "br"; "virbr" ] with
  | Some x -> x
  | None -> "br"

module Substitutions = struct

  type v =
    | Name
    | Kernel
    | Memory
    | Block of block_t
    | Network of string

  let string_of_v = function
    | Name -> "@NAME@"
    | Kernel -> "@KERNEL@"
    | Memory -> "@MEMORY@"
    | Block b -> Printf.sprintf "@BLOCK:%s@" b.filename
    | Network n -> Printf.sprintf "@NETWORK:%s@" n

  let lookup ts v =
    if List.mem_assoc v ts
    then List.assoc v ts
    else string_of_v v

  let defaults i =
    let blocks = List.map (fun b ->
        Block b, Filename.concat (Info.root i) b.filename
      ) (Hashtbl.fold (fun _ v acc -> v :: acc) all_blocks []) in
    let networks = List.mapi (fun i n ->
        Network n, Printf.sprintf "%s%d" detected_bridge_name i
      ) !all_networks in [
      Name, (Info.name i);
      Kernel, Printf.sprintf "%s/mir-%s.xen" (Info.root i) (Info.name i);
      Memory, "256";
    ] @ blocks @ networks

end

let configure_main_xl ?substitutions ext i =
  let open Substitutions in
  let substitutions = match substitutions with
    | Some x -> x
    | None -> defaults i in
  let file = Info.root i / Info.name i ^ ext in
  let open Codegen in
  Cmd.with_file file @@ fun fmt ->
  append fmt "# %s" (generated_header ()) ;
  newline fmt;
  append fmt "name = '%s'" (lookup substitutions Name);
  append fmt "kernel = '%s'" (lookup substitutions Kernel);
  append fmt "builder = 'linux'";
  append fmt "memory = %s" (lookup substitutions Memory);
  append fmt "on_crash = 'preserve'";
  newline fmt;
  let blocks = List.map (fun b ->
      (* We need the Linux version of the block number (this is a
         strange historical artifact) Taken from
         https://github.com/mirage/mirage-block-xen/blob/
         a64d152586c7ebc1d23c5adaa4ddd440b45a3a83/lib/device_number.ml#L128 *)
      let rec string_of_int26 x =
        let (/) = Pervasives.(/) in
        let high, low = x / 26 - 1, x mod 26 + 1 in
        let high' = if high = -1 then "" else string_of_int26 high in
        let low' =
          String.v 1 (fun _ -> char_of_int (low + (int_of_char 'a') - 1))
        in
        high' ^ low' in
      let vdev = Printf.sprintf "xvd%s" (string_of_int26 b.number) in
      let path = lookup substitutions (Block b) in
      Printf.sprintf "'format=raw, vdev=%s, access=rw, target=%s'" vdev path
    ) (Hashtbl.fold (fun _ v acc -> v :: acc) all_blocks []) in
  append fmt "disk = [ %s ]" (String.concat ~sep:", " blocks);
  newline fmt;
  let networks = List.map (fun n ->
      Printf.sprintf "'bridge=%s'" (lookup substitutions (Network n))
    ) !all_networks in
  append fmt "# if your system uses openvswitch then either edit \
              /etc/xen/xl.conf and set";
  append fmt "#     vif.default.script=\"vif-openvswitch\"";
  append fmt "# or add \"script=vif-openvswitch,\" before the \"bridge=\" \
              below:";
  append fmt "vif = [ %s ]" (String.concat ~sep:", " networks);
  ()

let clean_main_xl ~root ~name ext = Cmd.remove (root / name ^ ext)

let configure_main_xe ~root ~name =
  let open Codegen in
  let file = root / name ^ ".xe" in
  Cmd.with_file file @@ fun fmt ->
  append fmt "#!/bin/sh";
  append fmt "# %s" (generated_header ());
  newline fmt;
  append fmt "set -e";
  newline fmt;
  append fmt "# Dependency: xe";
  append fmt "command -v xe >/dev/null 2>&1 || { echo >&2 \"I require xe but \
              it's not installed.  Aborting.\"; exit 1; }";
  append fmt "# Dependency: xe-unikernel-upload";
  append fmt "command -v xe-unikernel-upload >/dev/null 2>&1 || { echo >&2 \"I \
              require xe-unikernel-upload but it's not installed.  Aborting.\"\
              ; exit 1; }";
  append fmt "# Dependency: a $HOME/.xe";
  append fmt "if [ ! -e $HOME/.xe ]; then";
  append fmt "  echo Please create a config file for xe in $HOME/.xe which \
              contains:";
  append fmt "  echo server='<IP or DNS name of the host running xapi>'";
  append fmt "  echo username=root";
  append fmt "  echo password=password";
  append fmt "  exit 1";
  append fmt "fi";
  newline fmt;
  append fmt "echo Uploading VDI containing unikernel";
  append fmt "VDI=$(xe-unikernel-upload --path %s/mir-%s.xen)" root name;
  append fmt "echo VDI=$VDI";
  append fmt "echo Creating VM metadata";
  append fmt "VM=$(xe vm-create name-label=%s)" name;
  append fmt "echo VM=$VM";
  append fmt "xe vm-param-set uuid=$VM PV-bootloader=pygrub";
  append fmt "echo Adding network interface connected to xenbr0";
  append fmt "ETH0=$(xe network-list bridge=xenbr0 params=uuid --minimal)";
  append fmt "VIF=$(xe vif-create vm-uuid=$VM network-uuid=$ETH0 device=0)";
  append fmt "echo Atting block device and making it bootable";
  append fmt "VBD=$(xe vbd-create vm-uuid=$VM vdi-uuid=$VDI device=0)";
  append fmt "xe vbd-param-set uuid=$VBD bootable=true";
  append fmt "xe vbd-param-set uuid=$VBD other-config:owner=true";
  List.iter (fun b ->
      append fmt "echo Uploading data VDI %s" b.filename;
      append fmt "echo VDI=$VDI";
      append fmt "SIZE=$(stat --format '%%s' %s/%s)" root b.filename;
      append fmt "POOL=$(xe pool-list params=uuid --minimal)";
      append fmt "SR=$(xe pool-list uuid=$POOL params=default-SR --minimal)";
      append fmt "VDI=$(xe vdi-create type=user name-label='%s' \
                  virtual-size=$SIZE sr-uuid=$SR)" b.filename;
      append fmt "xe vdi-import uuid=$VDI filename=%s/%s" root b.filename;
      append fmt "VBD=$(xe vbd-create vm-uuid=$VM vdi-uuid=$VDI device=%d)"
        b.number;
      append fmt "xe vbd-param-set uuid=$VBD other-config:owner=true";
    ) (Hashtbl.fold (fun _ v acc -> v :: acc) all_blocks []);
  append fmt "echo Starting VM";
  append fmt "xe vm-start uuid=$VM";
  Unix.chmod file 0o755

let clean_main_xe ~root ~name = Cmd.remove (root / name ^ ".xe")

(* Implement something similar to the @name/file extended names of findlib. *)
let rec expand_name ~lib param =
  match String.cut param ~sep:"@" with
  | None -> param
  | Some (prefix, name) -> match String.cut name ~sep:"/" with
    | None              -> prefix ^ lib / name
    | Some (name, rest) -> prefix ^ lib / name / expand_name ~lib rest

(* Get the linker flags for any extra C objects we depend on.
 * This is needed when building a Xen image as we do the link manually. *)
let get_extra_ld_flags pkgs =
  Cmd.read "opam config var lib" >>= fun s ->
  let lib = String.trim s in
  Cmd.read
    "ocamlfind query -r -format '%%d\t%%(xen_linkopts)' -predicates native %s"
    (String.concat ~sep:" " pkgs) >>| fun output ->
  String.cuts output ~sep:"\n"
  |> List.fold_left (fun acc line ->
      match String.cut line ~sep:"\t" with
      | None -> acc
      | Some (dir, ldflags) ->
        let ldflags = String.cuts ldflags ~sep:" " in
        let ldflags = List.map (expand_name ~lib) ldflags in
        let ldflags = String.concat ~sep:" " ldflags in
        Printf.sprintf "-L%s %s" dir ldflags :: acc
    ) []

(* Get the linker flags for any extra C objects we depend on.
 * This is needed when building a Xen image as we do the link manually. *)
let get_extra_ld_flags_solo5 pkgs =
  Cmd.read "opam config var lib" >>= fun s ->
  let lib = String.trim s in
  Cmd.read
    "ocamlfind query -r -format '%%d\t%%(xen_linkopts)' -predicates native %s"
    (String.concat ~sep:" " pkgs) >>| fun output ->
  String.cuts output ~sep:"\n"
  |> List.fold_left (fun acc line ->
      match String.cut line ~sep:"\t" with
      | None -> acc
      | Some (dir, ldflags) ->
        let ldflags = String.cuts ldflags ~sep:" " in
        let ldflags = List.map (expand_name ~lib) ldflags in
        let ldflags = String.concat ~sep:" " ldflags in
        let ldflags = Str.global_replace (Str.regexp "tcpip_xen_stubs") "tcpip_stubs" ldflags in
        Printf.sprintf "-L%s %s" dir ldflags :: acc
    ) []

      
let configure_myocamlbuild_ml ~root =
  let minor, major = Cmd.ocaml_version () in
  if minor < 4 || major < 1 then (
    (* Previous ocamlbuild versions weren't able to understand the
       --output-obj rules *)
    let file = root / "myocamlbuild.ml" in
    Cmd.with_file file @@ fun fmt ->
    Codegen.append fmt "(* %s *)" (Codegen.generated_header ());
    Codegen.newline fmt;
    Codegen.append fmt
      "open Ocamlbuild_pack;;\n\
       open Ocamlbuild_plugin;;\n\
       open Ocaml_compiler;;\n\
       \n\
       let native_link_gen linker =\n\
      \  link_gen \"cmx\" \"cmxa\" !Options.ext_lib [!Options.ext_obj; \"cmi\"\
       ] linker;;\n\
       \n\
       let native_output_obj x = native_link_gen ocamlopt_link_prog\n\
      \  (fun tags -> tags++\"ocaml\"++\"link\"++\"native\"++\"output_obj\") \
       x;;\n\
       \n\
       rule \"ocaml: cmx* & o* -> native.o\"\n\
      \  ~tags:[\"ocaml\"; \"native\"; \"output_obj\" ]\n\
      \  ~prod:\"%%.native.o\" ~deps:[\"%%.cmx\"; \"%%.o\"]\n\
      \  (native_output_obj \"%%.cmx\" \"%%.native.o\");;\n\
       \n\
       \n\
       let byte_link_gen = link_gen \"cmo\" \"cma\" \"cma\" [\"cmo\"; \"cmi\"\
       ];;\n\
       let byte_output_obj = byte_link_gen ocamlc_link_prog\n\
      \  (fun tags -> tags++\"ocaml\"++\"link\"++\"byte\"++\"output_obj\");;\n\
       \n\
       rule \"ocaml: cmo* -> byte.o\"\n\
      \  ~tags:[\"ocaml\"; \"byte\"; \"link\"; \"output_obj\" ]\n\
       ~prod:\"%%.byte.o\" ~dep:\"%%.cmo\"\n\
      \  (byte_output_obj \"%%.cmo\" \"%%.byte.o\");;";
  )

let clean_myocamlbuild_ml ~root = Cmd.remove (root / "myocamlbuild.ml")

let configure_makefile ~target ~root ~name ~warn_error info =
  let open Codegen in
  let file = root / "Makefile" in
  let libs = Info.libraries info in
  let libraries =
    match libs with
    | [] -> ""
    | l -> Fmt.(strf "-pkgs %a" (list ~sep:(unit ",") string)) l
  in
  let packages =
    Fmt.(strf "%a" (list ~sep:(unit " ") string)) @@ Info.packages info
  in
  Cmd.with_file file @@ fun fmt ->
  append fmt "# %s" (generated_header ());
  newline fmt;
  append fmt "LIBS   = %s" libraries;
  append fmt "PKGS   = %s" packages;
  let default_tags =
    (if warn_error then "warn_error(+1..49)," else "") ^
    "warn(A-4-41-44),debug,bin_annot,\
     strict_sequence,principal,safe_string"
  in
  begin match target with
    | `Xen ->
      append fmt "SYNTAX = -tags \"%s\"\n" default_tags;
      append fmt "FLAGS  = -cflag -g -lflags -g,-linkpkg,-dontlink,unix\n";
      append fmt "XENLIB = $(shell ocamlfind query mirage-xen)\n"
    | `Solo5 ->
      append fmt "SYNTAX = -tags \"%s\"\n" default_tags;
      append fmt "FLAGS  = -cflag -g -lflags -g,-linkpkg,-dontlink,unix\n";
      append fmt "XENLIB = $(shell ocamlfind query mirage-solo5)\n"
    | `Unix ->
      append fmt "SYNTAX = -tags \"%s\"\n" default_tags;
      append fmt "FLAGS  = -r -cflag -g -lflags -g,-linkpkg\n"
    | `MacOSX ->
      append fmt "SYNTAX = -tags \"thread,%s\"\n" default_tags;
      append fmt "FLAGS  = -r -cflag -g -lflags -g,-linkpkg\n"
  end;
  append fmt "SYNTAX += -tag-line \"<static*.*>: warn(-32-34)\"\n";
  append fmt "BUILD  = ocamlbuild -use-ocamlfind $(LIBS) $(SYNTAX) $(FLAGS)\n\
              OPAM   = opam\n\n\
              export PKG_CONFIG_PATH=$(shell opam config var prefix)\
              /lib/pkgconfig\n\n\
              export OPAMVERBOSE=1\n\
              export OPAMYES=1";
  newline fmt;
  append fmt ".PHONY: all depend clean build main.native\n\
              all:: build\n\
              \n\
              depend::\n\
              \t$(OPAM) install $(PKGS) --verbose\n\
              \n\
              main.native:\n\
              \t$(BUILD) main.native\n\
              \n\
              main.native.o:\n\
              \t$(BUILD) main.native.o";
  newline fmt;

  (* On ARM, we must convert the ELF image to an ARM boot executable zImage,
   * while on x86 we leave it as it is. *)
  let generate_image =
    let need_zImage =
      match Cmd.uname_m () with
      | Some machine ->
        String.length machine > 2 && String.is_prefix ~affix:"arm" machine
      | None -> failwith "uname -m failed; can't determine target machine type!"
    in
    if need_zImage then (
      Printf.sprintf "\t  -o mir-%s.elf\n\
                      \tobjcopy -O binary mir-%s.elf mir-%s.xen"
        name name name
    ) else (
      Printf.sprintf "\t  -o mir-%s.xen" name
    ) in

  begin match target with
    | `Xen ->
      get_extra_ld_flags libs
      >>| String.concat ~sep:" \\\n\t  "
      >>= fun extra_c_archives ->
      append fmt "build:: main.native.o";
      let pkg_config_deps = "mirage-xen" in
      append fmt "\tpkg-config --print-errors --exists %s" pkg_config_deps;
      append fmt "\tld -d -static -nostdlib \\\n\
                  \t  _build/main.native.o \\\n\
                  \t  %s \\\n\
                  \t  $$(pkg-config --static --libs %s) \\\n\
                  \t  $(shell gcc -print-libgcc-file-name) \\\n\
                  %s"
        extra_c_archives pkg_config_deps generate_image ;
      append fmt "\t@@echo Build succeeded";
      R.ok ()
    | `Solo5 ->
      get_extra_ld_flags_solo5 libs
      >>| String.concat ~sep:" \\\n\t  "
      >>= fun extra_c_archives ->
      append fmt "build:: main.native.o";
      let pkg_config_deps = "mirage-solo5" in
      append fmt "\tpkg-config --print-errors --exists %s" pkg_config_deps;
      append fmt "\tld -T $$(pkg-config --variable=linkscript solo5-kernel-ukvm)\\\n\
	    \t  -O2 -nostdlib -z max-page-size=0x1000 -static \\\n\
	    \t -o %s \\\n\
        \t  $$(pkg-config --static --libs solo5-kernel-ukvm)\\\n\
        \t  _build/main.native.o \\\n\
        \t  $$(pkg-config --variable=libdir mirage-solo5)/mirage-xen-ocaml/libxenotherlibs.a \\\n\
        \t  $$(pkg-config --variable=libdir mirage-solo5)/mirage-xen-ocaml/libxenasmrun.a \\\n\
        \t  $$(pkg-config --variable=libdir mirage-solo5)/mirage-xen-posix/libxenposix.a \\\n\
        \t  $$(pkg-config --static --libs mirage-solo5) \\\n\
        \t  $$(pkg-config --variable=libdir mirage-solo5)/libopenlibm.a \\\n\
        \t  %s \\\n\
        \t  $$(pkg-config --static --libs %s)"
        (Printf.sprintf "mir-%s.solo5-ukvm" name) extra_c_archives pkg_config_deps;
      append fmt "\t@@echo Build succeeded";
      R.ok ()
    | `Unix | `MacOSX ->
      append fmt "build: main.native";
      append fmt "\tln -nfs _build/main.native mir-%s" name;
      R.ok ()
  end >>= fun () ->
  newline fmt;
  append fmt "clean::\n\
              \tocamlbuild -clean";
  newline fmt;
  append fmt "-include Makefile.user";
  R.ok ()

let clean_makefile ~root = Cmd.remove (root / "Makefile")

let check_ocaml_version () =
  (* Similar to [Functoria_app.Cmd.ocaml_version] but with the patch number *)
  let ocaml_version =
    let version =
      let v = Sys.ocaml_version in
      match String.cut v ~sep:"+" with None -> v | Some (v, _) -> v
    in
    match String.cuts version ~sep:"." with
    | [major; minor; patch] ->
      begin
        try int_of_string major, int_of_string minor, int_of_string patch
        with _ -> 0, 0, 0
      end
    | _ -> 0, 0, 0
  in
  let major, minor, patch = ocaml_version in
  if major < 4 ||
     (major = 4 && minor < 2) ||
     (major = 4 && minor = 2 && patch < 3)
  then (
    Log.error
      "Your version of OCaml (%d.%02d.%d) is not supported. Please upgrade to\n\
       at least OCaml 4.02.3 or use `--no-ocaml-version-check`."
      major minor patch
  ) else
    R.ok ()

let configure i =
  let name = Info.name i in
  let root = Info.root i in
  let ctx = Info.context i in
  let target = Key.(get ctx target) in
  let ocaml_check = not Key.(get ctx no_ocaml_check) in
  let warn_error = Key.(get ctx warn_error) in
  begin
    if ocaml_check then check_ocaml_version ()
    else R.ok ()
  end >>= fun () ->
  check_entropy @@ Info.libraries i >>= fun () ->
  Log.info "%a %a" Log.blue "Configuring for target:" Key.pp_target target ;
  Cmd.in_dir root (fun () ->
      configure_main_xl ".xl" i;
      configure_main_xl ~substitutions:[] ".xl.in" i;
      configure_main_xe ~root ~name;
      configure_main_libvirt_xml ~root ~name;
      configure_myocamlbuild_ml ~root;
      configure_makefile ~target ~root ~name ~warn_error i;
    )

let clean i =
  let name = Info.name i in
  let root = Info.root i in
  Cmd.in_dir root (fun () ->
      clean_main_xl ~root ~name ".xl";
      clean_main_xl ~root ~name ".xl.in";
      clean_main_xe ~root ~name;
      clean_main_libvirt_xml ~root ~name;
      clean_myocamlbuild_ml ~root;
      clean_makefile ~root;
      Cmd.run "rm -rf %s/mir-%s" root name;
    )

module Project = struct
  let name = "mirage"
  let version = Mirage_version.current
  let prelude =
    "open Lwt\n\
     let run = OS.Main.run"
  let driver_error = driver_error

  let create jobs = impl @@ object
      inherit base_configurable
      method ty = job
      method name = "mirage"
      method module_name = "Mirage_runtime"
      method keys = [
        Key.(abstract target);
        Key.(abstract unix);
        Key.(abstract xen);
        Key.(abstract no_ocaml_check);
        Key.(abstract warn_error);
      ]

      method packages =
        let l = [ "lwt"; "mirage-types"; "mirage-types-lwt" ] in
		Key.match_ Key.(value target) @@function
		  | `Xen -> "mirage-xen" :: l
		  | `Solo5 -> "mirage-solo5" :: l
		  | `Unix | `MacOSX -> "mirage-unix" :: l

      method libraries =
        let l = [ "mirage.runtime"; "mirage-types.lwt" ] in
		Key.match_ Key.(value target) @@function
		  | `Xen -> "mirage-xen" :: l
		  | `Solo5 -> "mirage-solo5" :: l
		  | `Unix | `MacOSX -> "mirage-unix" :: l

      method configure = configure
      method clean = clean
      method connect _ _mod _names = "Lwt.return_unit"
      method deps = List.map abstract jobs
    end

end

include Functoria_app.Make (Project)

(** {Deprecated functions} *)

let get_mode () = Key.(get (get_base_context ()) target)

let libraries_ref = ref []
let add_to_ocamlfind_libraries l =
  libraries_ref := !libraries_ref @ l

let packages_ref = ref []
let add_to_opam_packages l =
  packages_ref := !packages_ref @ l

(** {Custom registration} *)

let (++) acc x = match acc, x with
  | _       , None   -> acc
  | None    , Some x -> Some [x]
  | Some acc, Some x -> Some (acc @ [x])

let register
    ?(argv=default_argv) ?tracing ?(reporter=default_reporter ())
    ?keys ?(libraries=[]) ?(packages=[])
    name jobs =
  let libraries = !libraries_ref @ libraries in
  let packages = !packages_ref @ packages in
  let argv = Some (Functoria_app.keys argv) in
  let reporter = if reporter == no_reporter then None else Some reporter in
  let init = None ++ argv ++ reporter ++ tracing in
  register ?keys ~libraries ~packages ?init name jobs
