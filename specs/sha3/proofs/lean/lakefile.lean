import Lake
open Lake DSL

package libcrux_iot_sha3 where
  version := v!"0.1.0"

def haxHome := run_io do
  let some path ← IO.getEnv "HAX_HOME" | throw (IO.userError "HAX_HOME is not set")
  return path

require Hax from haxHome / "hax-lib/proof-libs/lean"

lean_lib libcrux_iot_sha3 where
  roots := #[`extraction.helpers]
