from lang_loop.loop_ast import *
from common.wasm import *
import lang_loop.loop_tychecker as loop_tychecker
from common.compilerSupport import *
from typing import List, Dict, Type, cast
from functools import reduce
import operator

# Counter for generating unique labels
_label_counter = 0


def generate_label(prefix: str) -> WasmId:
    """Generates a unique WASM label."""
    global _label_counter
    _label_counter += 1
    return WasmId(f"${prefix}_{_label_counter}")


# | Less | LessEq | Greater | GreaterEq | Eq | NotEq | And | Or
# "eq", "ne", "lt_s", "lt_u", "gt_s", "gt_u", "le_s", "le_u", "ge_s", "ge_u"
WasmBinops = Literal["add", "sub", "mul", "lt_s", "le_s", "gt_s", "ge_s", "eq", "ne"]
binop_to_wasm: Dict[Type[binaryop], WasmBinops] = {
    Add: "add",
    Sub: "sub",
    Mul: "mul",
    Less: "lt_s",
    LessEq: "le_s",
    Greater: "gt_s",
    GreaterEq: "ge_s",
    Eq: "eq",
    NotEq: "ne",
}


def identToWasmId(id: ident) -> WasmId:
    return WasmId(f"${id.name}")


def tyOfExp(e: exp) -> ty:
    match e.ty:
        case None:
            raise Exception(f"Expression type is None: {e}")
        case Void():
            raise Exception(f"Expression type is void: {e}")
        case NotVoid(ty):
            return ty


def tyToWasmStr(ty_: ty) -> WasmValtype:
    match ty_:
        case Int():
            return "i64"
        case Bool():
            return "i32"


def compileUnaryOp(exp_: exp) -> List[WasmInstr]:
    match exp_:
        case UnOp(USub(), arg):
            exp_ty = tyToWasmStr(tyOfExp(exp_))
            instructions: List[WasmInstr] = [WasmInstrConst(ty=exp_ty, val=0)]
            instructions.extend(compileExp(arg))
            instructions.append(WasmInstrNumBinOp(ty=exp_ty, op="sub"))
            return instructions
        case UnOp(Not(), arg):
            exp_ty = tyToWasmStr(tyOfExp(exp_))
            instructions: List[WasmInstr] = compileExp(arg)
            instructions.append(WasmInstrConst(ty="i32", val=0))
            instructions.append(WasmInstrIntRelOp(ty="i32", op="eq"))
            return instructions
        case _:
            return []


def compileBinaryOp(exp_: exp) -> List[WasmInstr]:
    match exp_:
        case BinOp(left, And(), right):
            exp_ty = tyToWasmStr(tyOfExp(left))
            return [
                *compileExp(left),
                WasmInstrIf(
                    resultType=exp_ty,
                    thenInstrs=compileExp(right),
                    elseInstrs=[WasmInstrConst(ty=exp_ty, val=0)],
                ),
            ]
        case BinOp(left, Or(), right):
            exp_ty = tyToWasmStr(tyOfExp(left))
            return [
                *compileExp(left),
                WasmInstrIf(
                    resultType=exp_ty,
                    thenInstrs=[WasmInstrConst(ty=exp_ty, val=1)],
                    elseInstrs=compileExp(right),
                ),
            ]
        case BinOp(left, op, right):
            exp_ty = tyToWasmStr(tyOfExp(left))
            instructions: List[WasmInstr] = compileExp(left)
            instructions.extend(compileExp(right))
            wasm_op: WasmBinops = binop_to_wasm[type(op)]

            # NOTE: really hate this, fix
            if type(op) in [Add, Sub, Mul]:
                num_op = cast(Literal["add", "sub", "mul"], wasm_op)
                instructions.append(WasmInstrNumBinOp(ty=exp_ty, op=num_op))
            elif type(op) in [Less, LessEq, Greater, GreaterEq, Eq, NotEq]:
                cmp_op = cast(
                    Literal["lt_s", "le_s", "gt_s", "ge_s", "eq", "ne"], wasm_op
                )
                lit_ty = cast(Literal["i32", "i64"], exp_ty)
                instructions.append(WasmInstrIntRelOp(ty=lit_ty, op=cmp_op))
            return instructions
        case _:
            return []


# IntConst | Name | Call | UnOp | BinOp
def compileExp(exp_: exp) -> List[WasmInstr]:
    match exp_:
        case IntConst(value):
            exp_ty = tyToWasmStr(tyOfExp(exp_))
            return [WasmInstrConst(ty=exp_ty, val=value)]
        case BoolConst(value):
            exp_ty = tyToWasmStr(tyOfExp(exp_))
            instr: List[WasmInstr] = [WasmInstrConst(ty=exp_ty, val=int(value))]
            return instr
        case Name(ident_):
            exp_ty = tyToWasmStr(tyOfExp(exp_))
            return [WasmInstrVarLocal(op="get", id=identToWasmId(ident_))]
        case UnOp():
            return compileUnaryOp(exp_)
        case BinOp():
            return compileBinaryOp(exp_)
        case Call(ident_, args):
            match ident_:
                case Ident(name="print"):
                    arg_instr = compileExp(args[0])
                    arg_type = tyOfExp(args[0])
                    if isinstance(arg_type, Bool):
                        return [
                            *arg_instr,
                            WasmInstrCall(WasmId("$print_bool")),
                        ]
                    return [
                        *arg_instr,
                        WasmInstrCall(WasmId(f"$print_{tyToWasmStr(arg_type)}")),
                    ]

                case Ident(name="input_int"):
                    return [WasmInstrCall(WasmId("$input_i64"))]
                case _:
                    return []
        case _:
            return []


def compileStmts(stmts: List[stmt]) -> List[WasmInstr]:
    def compileStmt(stmt_: stmt) -> List[WasmInstr]:
        match stmt_:
            case StmtExp(exp_):
                return compileExp(exp_)
            case Assign(ident_, exp_):
                instructions = compileExp(exp_)
                instructions.append(
                    WasmInstrVarLocal(op="set", id=identToWasmId(ident_))
                )
                return instructions
            case IfStmt(cond, thenBody, elseBody):
                return [
                    *compileExp(cond),
                    WasmInstrIf(
                        resultType=None,
                        thenInstrs=compileStmts(thenBody),
                        elseInstrs=compileStmts(elseBody),
                    ),
                ]
            case WhileStmt(cond, body):
                block_label = generate_label("while_block")
                loop_label = generate_label("while_loop")
                return [
                    WasmInstrBlock(
                        label=block_label,
                        result=None,
                        body=[
                            WasmInstrLoop(  # The loop itself
                                label=loop_label,
                                body=[
                                    # check condition first
                                    *compileExp(cond),
                                    WasmInstrConst(ty="i32", val=0),
                                    WasmInstrIntRelOp(ty="i32", op="eq"),
                                    # if condition is false, break
                                    WasmInstrBranch(
                                        target=block_label, conditional=True
                                    ),
                                    # one iteration
                                    *compileStmts(body),
                                    # jump to beginning
                                    WasmInstrBranch(
                                        target=loop_label, conditional=False
                                    ),
                                ],
                            )
                        ],
                    )
                ]
            case _:
                return []

    all_instructions: List[WasmInstr] = []
    return reduce(operator.iconcat, map(compileStmt, stmts), all_instructions)


def compileModule(m: mod, cfg: CompilerConfig) -> WasmModule:
    """
    Compiles the given module.
    """
    # this will reset the lable counter for each module
    global _label_counter
    _label_counter = 0

    vars: loop_tychecker.Symtab = loop_tychecker.tycheckModule(m)
    instrs: List[WasmInstr] = compileStmts(m.stmts)
    idMain: WasmId = WasmId("$main")
    locals: list[tuple[WasmId, WasmValtype]] = [
        (identToWasmId(k), tyToWasmStr(v.ty)) for k, v in vars.items()
    ]
    return WasmModule(
        imports=wasmImports(cfg.maxMemSize),
        exports=[WasmExport("main", WasmExportFunc(idMain))],
        globals=[],
        data=[],
        funcTable=WasmFuncTable([]),
        funcs=[WasmFunc(idMain, [], None, locals, instrs)],
    )
