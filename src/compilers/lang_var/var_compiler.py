from lang_var.var_ast import *
from common.wasm import *
import lang_var.var_tychecker as var_tychecker
from common.compilerSupport import *
from typing import List, Set, Dict, Type
from functools import reduce
import operator


WasmBinops = Literal["add", "sub", "mul"]
binop_to_wasm: Dict[Type[binaryop], WasmBinops] = {
    Add: "add",
    Sub: "sub",
    Mul: "mul",
}


def identToWasmId(id: ident) -> WasmId:
    return WasmId(f"${id.name}")


# IntConst | Name | Call | UnOp | BinOp
def compileExp(exp_: exp) -> List[WasmInstr]:
    match exp_:
        case IntConst(value):
            return [WasmInstrConst(ty="i64", val=value)]
        case Name(ident_):
            return [WasmInstrVarLocal(op="get", id=identToWasmId(ident_))]
        # NOTE: there might be a better way to do this
        case UnOp(_USub, arg):
            instructions: List[WasmInstr] = [WasmInstrConst(ty="i64", val=0)]
            instructions.extend(compileExp(arg))
            instructions.append(WasmInstrNumBinOp(ty="i64", op="sub"))
            return instructions
        case BinOp(left, op, right):
            instructions: List[WasmInstr] = compileExp(left)
            instructions.extend(compileExp(right))
            wasm_op: WasmBinops = binop_to_wasm[type(op)]
            # assert wasm_op is not None, "Idk"
            instructions.append(WasmInstrNumBinOp(ty="i64", op=wasm_op))
            return instructions
        # NOTE: function call missing
        case Call(ident_, args):
            match ident_:
                case Ident(name="print"):
                    instructions = []
                    for arg in args:
                        instructions.extend(compileExp(arg))
                    instructions.append(WasmInstrCall(WasmId("$print_i64")))
                    return instructions
                case Ident(name="input_int"):
                    return [WasmInstrCall(WasmId("$input_i64"))]
                case _:
                    raise Exception("Only print and input function supported so far")
        case _:
            raise Exception(f"Not yet implemented for: {exp_}")


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

    all_instructions: List[WasmInstr] = []
    return reduce(operator.iconcat, map(compileStmt, stmts), all_instructions)


def compileModule(m: mod, cfg: CompilerConfig) -> WasmModule:
    """
    Compiles the given module.
    """
    vars: Set[ident] = var_tychecker.tycheckModule(m)
    instrs: List[WasmInstr] = compileStmts(m.stmts)
    idMain: WasmId = WasmId("$main")
    locals: list[tuple[WasmId, WasmValtype]] = [(identToWasmId(x), "i64") for x in vars]
    return WasmModule(
        imports=wasmImports(cfg.maxMemSize),
        exports=[WasmExport("main", WasmExportFunc(idMain))],
        globals=[],
        data=[],
        funcTable=WasmFuncTable([]),
        funcs=[WasmFunc(idMain, [], None, locals, instrs)],
    )
