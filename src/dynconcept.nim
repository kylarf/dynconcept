import macros
import sugar


template expand(body: untyped): untyped =
  body


template dyn*(T: typedesc): typedesc =
  {.error: "type `" & $T & "` is not a dynamic concept".}


proc unwrap_postfix(name: NimNode): NimNode =
  case name.kind:
    of nnkIdent:
      name
    of nnkPostfix:
      name[1]
    else:
      error("Expected nnkIdent or nnkPostfix.")


proc dyn_ident(typename: NimNode): NimNode =
  let is_exported = (typename.kind == nnkPostfix)
  let symbol = unwrap_postfix(typename)
  let dyn_symbol = genSym(nskType, "DynamicConcept" & $symbol)
  if is_exported:
    postfix(dyn_symbol, "*")
  else:
    dyn_symbol


proc dyn_formal_params(typename: NimNode, params: NimNode): NimNode =
  params.expectKind(nnkFormalParams)
  for i, p in pairs(params):
    let ident_str = case p.kind:
      of nnkIdent:
        p.strval
      of nnkIdentDefs:
        p[1].strval
      else:
        error("Expected either nnkIdent or nnkIdentDefs.")
    let is_self_type = ident_str == "Self"
    if i == 1:
      if not is_self_type:
        error("Dynamic-compatible concepts must take type Self in receiver position.")
    elif is_self_type:
      error(
        "Dynamic-compatible concepts may not take or return type Self outside receiver position."
      )
  result = params.copyNimTree()
  # replace receiver-position ident def type Self with 
  result[1][1] = typename


proc proc_impl_name(name: NimNode): NimNode =
  expectKind(name, nnkIdent)
  ident(name.strval & "_impl")


proc dyn_concept_member(procdef: NimNode): NimNode =
  procdef.expectKind(nnkProcDef)
  let
    name = proc_impl_name(procdef.name)
    params = procdef.params.copyNimTree()
  params.del(1)  # remove receiver since it is captured in closure

  result = nnkIdentDefs.newTree(
    name,
    nnkProcTy.newTree(
      params,
      nnkPragma.newTree(ident("closure")),
    ),
    newEmptyNode(),
  )


proc dyn_concept_body(procs: NimNode): NimNode =
  expectKind(procs, nnkStmtList)
  result = newNimNode(nnkRecList)
  for p in procs:
    result.add dyn_concept_member(p)


proc dyn_concept_typedef(name: NimNode, procs: NimNode): NimNode =
  let body = dyn_concept_body(procs)
  nnkTypeDef.newTree(
    name,
    newEmptyNode(),
    nnkObjectTy.newTree(
      newEmptyNode(),
      newEmptyNode(),
      body,
    )
  )


proc params_to_call_list(p: NimNode): NimNode =
  expectKind(p, nnkFormalParams)
  # 'p' is a nnkFormalParams node (e.g., from a proc definition)
  result = newTree(nnkArgList)
  
  # FormalParams[0] is return type, [1..^1] are params
  for i in 1 ..< p.len:
    let paramGroup = p[i]
    # paramGroup looks like: (nnkIdentDefs, ident1, ident2, typeNode, defaultVal)
    # Iterate through identifiers (everything before the type node)
    for j in 0 ..< paramGroup.len - 2:
      result.add(paramGroup[j])


proc trampoline(p: NimNode, typename: NimNode, is_exported: bool): NimNode =
  expectKind(p, nnkProcDef)
  let declared_symbol =
    if is_exported:
      postfix(p.name, "*")
    else:
      p.name
  let
    proc_name = proc_impl_name(p.name)
    params = dyn_formal_params(typename, p.params.copyNimTree())
    receiver_name = params[1][0]
  params[1] = nnkIdentDefs.newTree(
    receiver_name,  # forward the old param name
    unwrap_postfix(typename),
    newEmptyNode(),
  )
  let call_args = nnkArgList.newTree(params_to_call_list(p.params)[1..^1])
  let arg_node =
    if len(call_args) > 0:
      call_args
    else:
      nnkArgList.newTree()
  let body = quote do:
    `receiver_name`.`proc_name`(`arg_node`)
  nnkProcDef.newTree(
    declared_symbol,
    newEmptyNode(),
    newEmptyNode(),
    params,
    nnkPragma.newTree(ident("inject")),
    newEmptyNode(),
    body
  )


proc build_trampolines(typename, procs: NimNode): NimNode =
  result = newNimNode(nnkStmtList)
  let is_exported = (typename.kind == nnkPostfix)
  for p in procs:
    result.add trampoline(p, typename, is_exported)


proc proc_assign(procdef: NimNode, captured_ident: NimNode): NimNode =
  captured_ident.expectKind(nnkIdent)
  procdef.expectKind(nnkProcDef)
  let
    proc_name = procdef.name
    impl_name = proc_impl_name(procdef.name)
    params = procdef.params.copyNimTree()
  params.del(1)  # remove receiver since it is captured in closure
  let
    call_args = nnkArgList.newTree(captured_ident)
    addl_params = params_to_call_list(params)
  if len(addl_params) > 0:
    call_args.add(addl_params)

  let call_expr = quote do:
    `proc_name`(`call_args`)

  let lhs = newDotExpr(ident("result"), impl_name)
  let rhs = nnkProcDef.newTree(
    newEmptyNode(),
    newEmptyNode(),
    newEmptyNode(),
    params,
    nnkPragma.newTree(ident("closure")),
    newEmptyNode(),
    nnkStmtList.newTree(call_expr)
  )
  result = nnkAsgn.newTree(lhs, rhs)


proc converter_body(procdefs: NimNode): NimNode =
  let mixins = collect:
    for p in procdefs:
      nnkMixinStmt.newTree(p.name)
  let
    self_ident = ident("self")
    captured_ident = ident("captured")
  let capture_assign = nnkVarSection.newTree(
    nnkIdentDefs.newTree(
      captured_ident,
      newEmptyNode(),
      self_ident,
    ),
  )
  let proc_assigns = collect:
    for p in procdefs:
      proc_assign(p, captured_ident)
  let body = newTree(nnkStmtList)
  for m in mixins:
    body.add(m)
  body.add(capture_assign)
  for p in proc_assigns:
    body.add(p)
  body


proc asIdent(T: NimNode): NimNode =
  ident($T)


proc build_converter(
  typename: NimNode, concept_name: NimNode, procdefs: NimNode, is_exported: bool
): NimNode =
  let
    body = converter_body(procdefs)
    converter_name = ident("toDyn" & $concept_name)
  let converter_decl =
    if is_exported:
      postfix(converter_name, "*")
    else:
      converter_name
  let into = ident("into")
  let into_decl =
    if is_exported:
      postfix(into, "*")
    else:
      into
  let self_ident = ident("self")
  quote do:
    mixin dyn
    converter `converter_decl`(`self_ident`: sink `typename`): dyn `concept_name` {.inject.} =
      `body`
    proc `into_decl`(`self_ident`: sink `typename`, toType: typedesc[dyn `concept_name`]): dyn `concept_name` {.inject.} =
      result = `self_ident`


proc dyn_qualifier_helper(C: NimNode, dyn_name: NimNode): NimNode =
  let template_name = case C.kind:
    of nnkPostfix:
      postfix(ident("dyn"), "*")
    else:
      ident("dyn")
  let concept_typedesc = unwrap_postfix(C)
  quote do:
    template `template_name`(T: typedesc[`concept_typedesc`]): typedesc {.inject.} =
      `dyn_name`


macro dynamic*(defn: untyped): untyped =
  result = defn.copyNimTree()
  defn.expectKind(nnkTypeDef)
  let
    basename = defn[0].copyNimTree()
    concept_def = defn[2].copyNimTree()
    outname = basename.copyNimTree()
  basename[1].add(ident("inject"))
  outname[0] = dyn_ident(outname[0])
  outname[1].add(ident("inject"))
  let
    dyn_qual_template = dyn_qualifier_helper(basename[0], unwrap_postfix(outname[0]))
    procs = defn[2][3].copyNimTree()
    dyn_def = dyn_concept_typedef(outname, procs)
    trampolines = build_trampolines(outname[0], procs)
  let template_body = nnkStmtList.newTree(
    nnkTypeSection.newTree(
      nnkTypeDef.newTree(
        basename,
        newEmptyNode(),
        concept_def,
      ),
      dyn_def,
    ),
    trampolines,
    dyn_qual_template,
    unwrap_postfix(basename[0])
  )
  result[0] = genSym(nskType, unwrap_postfix(basename[0]).strval & "DynamicExpansion")
  result[2] = newCall(ident("expand"), template_body)
  echo result.repr


proc syms_to_idents(n: NimNode): NimNode =
  ## Deep-copy `n`, replacing every nnkSym with an nnkIdent
  ## of the same spelling.
  if n.kind == nnkSym:
    return ident($n)
  result = copyNimNode(n)
  for child in n:
    result.add syms_to_idents(child)


proc base_type_sym(t: NimNode): NimNode =
  ## Extract the base nominal type symbol from:
  ##   Foo
  ##   ref Foo
  ##   ptr Foo
  ##   var Foo
  ##   Foo[T]
  ##   ref Foo[T]
  ##
  ## Raises unless the final base is a resolved nnkSym.
  case t.kind:
    of nnkSym:
      result = t
    of nnkRefTy, nnkPtrTy, nnkVarTy:
      result = base_type_sym(t[0])
    of nnkBracketExpr:
      # Generic instantiation: Foo[T] -> Foo.
      # Nim's docs describe brackets as instantiating generic procs,
      # iterators, or types; in AST terms this is represented as
      # nnkBracketExpr(head, args...).
      result = base_type_sym(t[0])
    else:
      error("expected resolved nominal type, ref/ptr/var type, or generic instantiation")


proc generate_concept_check(T: NimNode, C: NimNode): NimNode =
  result = quote do:
    block:
      proc check[U: `C`](_: typedesc[U]) = discard
      when not compiles(check(`T`)):
        {.error: "dynconcept impl failed: type `" & $`T` &
          "` does not satisfy concept `" & $`C` & "`".}
      else:
        check(`T`)


proc impl_impl(T: NimNode, C: NimNode): NimNode =
  let
    is_exported = base_type_sym(T).isExported
    concept_def = getImpl(C)[2]
    concept_procs = concept_def[3].syms_to_idents()
    converter_def = build_converter(T, C, concept_procs, is_exported)
    concept_check = generate_concept_check(T, C)
  result = quote do:
    `concept_check`
    `converter_def`


macro impl*(T: typedesc, C: typedesc): untyped =
  result = impl_impl(T, C)


macro impl*(T: typedesc, C: typedesc, defns: untyped): untyped =
  let checked_impl = impl_impl(T, C)
  result = quote do:
    `defns`
    `checked_impl`
