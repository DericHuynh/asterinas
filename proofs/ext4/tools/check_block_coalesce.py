#!/usr/bin/env python3
# SPDX-License-Identifier: MPL-2.0
"""Run the byte coalescer against its actual successful diagnostic library.

This is component evidence, never a replacement for the official strict gate.
"""
from pathlib import Path
import argparse, hashlib, json, os, resource, subprocess, time

parser=argparse.ArgumentParser()
parser.add_argument("--proof-dir",type=Path,required=True)
parser.add_argument("--out-dir",type=Path,required=True)
args=parser.parse_args()
root=Path(__file__).resolve().parents[1]
proof=args.proof_dir.resolve()
out=args.out_dir.resolve()
out.mkdir()
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
result=json.loads((proof/"result.json").read_text())
assert result["returncode"]==0 and result["snapshot_unchanged"]
raw=json.loads((proof/"stdout").read_text())
vr=raw["verification-results"]
assert not vr["errors"] and not vr["encountered-error"] and not vr["encountered-vir-error"]
assert vr["verified"]>0 and not vr["is-verifying-entire-crate"]
assert result["verified_modules"]==["block_coalesce"]
command=json.loads((proof/"command.json").read_text())
assert command["verified_modules"]==["block_coalesce"] and command["declared_new_modules"]==["block_coalesce"]
assert "--compile" in command["argv"] and "--no-verify" not in command["argv"]
sources=json.loads((proof/"source-sha256.json").read_text())
assert "src/block_coalesce.rs" in sources["snapshot"]
def source_integrity():
    for name,digest in sources["snapshot"].items():
        assert sha(proof/name)==digest,name
    for name,digest in sources["live_source_before_entrypoint_declarations"].items():
        assert sha(root/name)==digest,name
    assert sha(root/"toolchain.lock.json")==sha(proof/"baseline-toolchain.lock.json")
source_integrity()
assert sha(root/"src/block_coalesce.rs")==sha(proof/"src/block_coalesce.rs")
library=proof/"build/libverified_ext4.rlib"
assert library.is_file()
protected=[library,proof/"stdout",proof/"result.json",proof/"command.json",proof/"source-sha256.json",
    proof/"baseline-toolchain.lock.json",root/"tests/block_coalesce.rs",Path(__file__)]
before={str(p):sha(p) for p in protected}
rustc=os.environ.get("RUSTC_BIN","/task/verus/rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/bin/rustc")
deps=os.environ.get("VERUS_LIB_DIR","/task/verus/installed")
prefix=[rustc,"--edition=2024","--extern",f"verified_ext4={library}","-L",f"dependency={deps}"]
records=[]
def cap():
    resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,4*1024**3))
def run(name,argv,timeout):
    start=time.monotonic()
    with (out/(name+".stdout")).open("xb") as so,(out/(name+".stderr")).open("xb") as se:
        p=subprocess.run(argv,stdout=so,stderr=se,timeout=timeout,preexec_fn=cap)
    entry={"name":name,"argv":argv,"returncode":p.returncode,"elapsed_seconds":time.monotonic()-start}
    records.append(entry)
    return p.returncode,(out/(name+".stderr")).read_text(errors="replace")
native=root/"tests/block_coalesce.rs"
binary=out/"block-coalesce"
rc,_=run("compile-native",prefix+[str(native),"-o",str(binary)],60)
assert rc==0
rc,_=run("native",[str(binary)],120)
assert rc==0
fixtures={
"private-fields":("E0451","use verified_ext4::{block_coalesce::BlockEditor,source_block::SourceBlock}; fn bad(source:SourceBlock)->BlockEditor{BlockEditor{source,bytes:vec![],covered:vec![]}}"),
"mutable-output":("E0594","use verified_ext4::block_coalesce::BlockEditor; fn bad(owner: &BlockEditor){owner.raw()[0]=0;}"),
"mutable-original":("E0594","use verified_ext4::block_coalesce::BlockEditor; fn bad(owner: &BlockEditor){owner.original().raw()[0]=0;}"),
"duplicate-owner":("E0599","use verified_ext4::block_coalesce::BlockEditor; fn bad(owner:&BlockEditor)->BlockEditor{(*owner).clone()}"),
"use-after-edit":("E0382","use verified_ext4::block_coalesce::BlockEditor; fn bad(owner:BlockEditor){let _next=owner.apply(0,&[0],&[1]);let _old=owner.raw();}"),
}
for name,(code,body) in fixtures.items():
    source=out/(name+".rs");source.write_text(body+"\n")
    artifact=out/(name+".rlib")
    rc,err=run(name,prefix+["--crate-type=lib","--crate-name",name.replace("-","_"),str(source),"-o",str(artifact)],60)
    assert rc!=0 and code in err and not artifact.exists(),(name,rc,err)
source=out/"allowed.rs"
source.write_text("use verified_ext4::{block_coalesce::BlockEditor,source_block::SourceBlock,transaction::AfterImage}; pub fn allowed(block:SourceBlock)->Result<AfterImage,BlockEditor>{let owner=BlockEditor::from_source(block);let _=owner.original();let _=owner.identity();let _=owner.raw();owner.into_after_image()}\n")
rc,err=run("allowed",prefix+["--crate-type=lib",str(source),"-o",str(out/"allowed.rlib")],60)
assert rc==0,err
source_integrity()
assert all(sha(Path(name))==digest for name,digest in before.items())
manifest={"library":sha(library),"component_source":sha(root/"src/block_coalesce.rs"),"native_driver":sha(native),"checker":sha(Path(__file__))}
summary={"status":"passed","scope":"component native checks; no whole-crate/kernel/durability claim","proof_directory":str(proof),"focused_verification_results":vr,"hashes":manifest,"input_before_after_sha256":before,"snapshot_source_count":len(sources["snapshot"]),"checks":records,"rejected_api_fixtures":len(fixtures),"allowed_api_fixtures":1,"native_summary":(out/"native.stdout").read_text()}
(out/"result.json").write_text(json.dumps(summary,indent=2)+"\n")
print(json.dumps(summary,indent=2))
