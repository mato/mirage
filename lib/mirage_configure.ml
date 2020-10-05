open Rresult
open Astring
open Mirage_impl_misc

module Key = Mirage_key
module Info = Functoria.Info
module Codegen = Functoria_app.Codegen

open Mirage_configure_xen
open Mirage_configure_solo5

let myocamlbuild_path = Fpath.(v "myocamlbuild.ml")

(* ocamlbuild will give a misleading hint on build failures
 * ( https://github.com/ocaml/ocamlbuild/blob/0eb62b72b5abd520484210125b18073338a634bc/src/ocaml_compiler.ml#L130 )
 * if it doesn't detect that the project is an ocamlbuild
 * project.  The only facility for hinting this is presence of
 * myocamlbuild.ml or _tags
 * ( https://github.com/ocaml/ocamlbuild/blob/0eb62b72b5abd520484210125b18073338a634bc/src/options.ml#L375-L387 )
 * so we create an empty myocamlbuild.ml . *)
let configure_myocamlbuild () =
  Bos.OS.File.exists myocamlbuild_path >>= function
  | true -> R.ok ()
  | false -> Bos.OS.File.write myocamlbuild_path ""

(* we made it, so we should clean it up *)
let clean_myocamlbuild () =
  match Bos.OS.Path.stat myocamlbuild_path with
  | Ok stat when stat.Unix.st_size = 0 -> Bos.OS.File.delete myocamlbuild_path
  | _ -> R.ok ()

let opam_path ~name = Fpath.(v name + "opam")

let artifact ~name = function
  | #Mirage_key.mode_solo5 | #Mirage_key.mode_xen as tgt ->
    let ext = snd (Mirage_configure_solo5.solo5_bindings_pkg tgt) in
    let file = Fpath.v (name ^ ext) in
    file, file
  | #Mirage_key.mode_unix ->
    Fpath.(v "_build" / "main" + "native"), Fpath.v name

let additional_artifacts ~name =
  let libvirt = Mirage_configure_libvirt.filename ~name in
  function
  | `Xen -> Fpath.[ v name + "xl" ; v name + "xl.in" ; v name + "xe" ; libvirt ]
  | `Virtio -> [ libvirt ]
  | _ -> []

let find_git () =
  let is_git p = Bos.OS.Dir.exists Fpath.(p / ".git") in
  let app_opt p d = match p with None -> d | Some p -> Fpath.(d // p) in
  let rec find p path =
    if Fpath.is_root p
    then Error (`Msg "no git repo found, reached root")
    else is_git p >>= fun has_git ->
      if has_git
      then Ok path
      else find (Fpath.parent p) (Some (app_opt path (Fpath.base p)))
  in
  Bos.OS.Dir.current () >>= fun cwd ->
  find cwd None >>= fun subdir ->
  let git_branch = Bos.Cmd.(v "git" % "rev-parse" % "--abbrev-ref" % "HEAD") in
  Bos.OS.Cmd.(run_out git_branch |> out_string |> success) >>= fun branch ->
  let git_remote = Bos.Cmd.(v "git" % "remote" % "get-url" % "origin") in
  Bos.OS.Cmd.(run_out git_remote |> out_string |> success) >>| fun git_url ->
  subdir, branch, git_url

let configure_opam ~name info =
  let open Codegen in
  let subdir, git_info =
    match find_git () with
    | Error _ -> None, None
    | Ok (subdir, branch, git_url) -> subdir, Some (branch, git_url)
  in
  let file = opam_path ~name in
  with_output file (fun oc () ->
      let fmt = Format.formatter_of_out_channel oc in
      append fmt "# %s" (generated_header ());
      Info.opam ~name fmt info;
      append fmt {|maintainer: "dummy"|};
      append fmt {|authors: "dummy"|};
      append fmt {|homepage: "dummy"|};
      append fmt {|bug-reports: "dummy"|};
      Format.fprintf fmt {|build: [ "sh" "-exc" "|};
      (match subdir with
       | None -> ()
       | Some p -> Format.fprintf fmt "cd %a && " Fpath.pp p);
      append fmt {|mirage %s && mirage build" ]|}
        (String.concat ~sep:" " (List.tl (Array.to_list Sys.argv)));
      append fmt {|synopsis: "This is a dummy"|};
      let target = Key.(get (Info.context info) target)
      and name = Info.name info
      in
      let src, dst = artifact ~name target in
      let src' = match subdir with None -> src | Some p -> Fpath.(p // src) in
      append fmt {|install: [|};
      append fmt {|  [ "cp" "%a" "%%{bin}%%/%a" ]|} Fpath.pp src' Fpath.pp dst;
      (match additional_artifacts ~name target with
       | [] -> ()
       | xs ->
         let xs' = match subdir with
           | None -> xs
           | Some d -> (List.map (fun a -> Fpath.(d // a)) xs)
         in
         append fmt {|  [ "cp" %a "%%{etc}%%" ]|}
           Fmt.(list ~sep:(unit " ") (quote Fpath.pp)) xs');
      append fmt {|]|};
      (match git_info with
       | None -> ()
       | Some (branch, origin) ->
         (* TODO is there a library for git urls anywhere? *)
         let public = match Astring.String.cut ~sep:"github.com:" origin with
           | Some (_, post) -> "git+https://github.com/" ^ post
           | _ -> origin
         in
         append fmt {|url { src: "%s#%s" }|} public branch);
      R.ok ())
    "opam file"

let opam_name ~name ~target =
  String.concat ~sep:"-" ["mirage"; "unikernel"; name; target]

let unikernel_opam_name ~name target =
  let target = Fmt.strf "%a" Key.pp_target target in
  opam_name ~name ~target

let clean_opam ~name target =
  Bos.OS.File.delete (opam_path ~name:(unikernel_opam_name ~name target))

let configure_makefile ~no_depext ~opam_name =
  let open Codegen in
  let file = Fpath.(v "Makefile") in
  with_output file (fun oc () ->
      let fmt = Format.formatter_of_out_channel oc in
      append fmt "# %s" (generated_header ());
      newline fmt;
      append fmt "-include Makefile.user";
      newline fmt;
      let depext = if no_depext then "" else "\n\t$(DEPEXT)" in
      append fmt "OPAM = opam\n\
                  DEPEXT ?= $(OPAM) pin add -k path --no-action --yes %s . &&\\\n\
                  \t$(OPAM) depext --yes --update %s ;\\\n\
                  \t$(OPAM) pin remove --no-action %s\n\
                  \n\
                  .PHONY: all depend depends clean build\n\
                  all:: build\n\
                  \n\
                  depend depends::%s\n\
                  \t$(OPAM) install -y --deps-only .\n\
                  \n\
                  build::\n\
                  \tmirage build\n\
                  \n\
                  clean::\n\
                  \tmirage clean\n"
        opam_name opam_name opam_name depext;
      R.ok ())
    "Makefile"

let configure i =
  let name = Info.name i in
  let root = Fpath.to_string (Info.build_dir i) in
  let ctx = Info.context i in
  let target = Key.(get ctx target) in
  Log.info (fun m -> m "Configuring for target: %a" Key.pp_target target);
  let opam_name = unikernel_opam_name ~name target in
  let target_debug = Key.(get ctx target_debug) in
  if target_debug && target <> `Hvt then
    Log.warn (fun m -> m "-g not supported for target: %a" Key.pp_target target);
  configure_myocamlbuild () >>= fun () ->
  rr_iter (clean_opam ~name)
    [`Unix; `MacOSX; `Xen; `Qubes; `Hvt; `Spt; `Virtio; `Muen; `Genode]
  >>= fun () ->
  configure_opam ~name:opam_name i >>= fun () ->
  let no_depext = Key.(get ctx no_depext) in
  configure_makefile ~no_depext ~opam_name >>= fun () ->
  (match target with
    | #Mirage_key.mode_solo5 -> generate_manifest_json true ()
    (* On Xen, a Solo5 manifest must be present to keep the build system and
     * Solo5 happy, but we intentionally do not generate any devices[] as
     * their naming does not follow the Solo5 rules. *)
    | #Mirage_key.mode_xen -> generate_manifest_json false ()
    | _ -> R.ok ()) >>= fun () ->
  match target with
  | `Xen ->
    configure_main_xl ~ext:"xl" i >>= fun () ->
    configure_main_xl ~substitutions:[] ~ext:"xl.in" i >>= fun () ->
    Mirage_configure_libvirt.configure_main ~root ~name
  | `Virtio ->
    Mirage_configure_libvirt.configure_virtio ~root ~name
  | _ -> R.ok ()
