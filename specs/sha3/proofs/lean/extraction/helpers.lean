import Hax

@[spec]
def core_models.num.Impl_9.from_le_bytes (x : RustArray u8 8) : RustM u64 :=
  pure (x.toVec[0].toUInt64
  + (x.toVec[1].toUInt64 <<< 8)
  + (x.toVec[2].toUInt64 <<< 16)
  + (x.toVec[3].toUInt64 <<< 24)
  + (x.toVec[4].toUInt64 <<< 32)
  + (x.toVec[5].toUInt64 <<< 40)
  + (x.toVec[6].toUInt64 <<< 48)
  + (x.toVec[7].toUInt64 <<< 56))

@[spec]
def core_models.num.Impl_9.to_le_bytes (x : u64) : RustM (RustArray u8 8) :=
  pure (.ofVec #v[
    (x % 256).toUInt8,
    (x >>> 8 % 256).toUInt8,
    (x >>> 16 % 256).toUInt8,
    (x >>> 24 % 256).toUInt8,
    (x >>> 32 % 256).toUInt8,
    (x >>> 40 % 256).toUInt8,
    (x >>> 48 % 256).toUInt8,
    (x >>> 56 % 256).toUInt8,
  ])


def core_models.num.Impl_11.MAX : usize := -1
