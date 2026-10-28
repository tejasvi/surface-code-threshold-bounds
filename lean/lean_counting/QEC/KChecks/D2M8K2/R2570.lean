import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10280 = true := by
  decide +kernel

theorem tot10280 : totK PD2M8K2 D2M8K2.t10280 = [0, 180898988409, 451852471343, 261111918738, 25645705363, 0, 0, 0] := by
  decide +kernel

theorem rows10281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10281 = true := by
  decide +kernel

theorem tot10281 : totK PD2M8K2 D2M8K2.t10281 = [0, 138155131991, 442996830366, 306115165930, 26035811131, 0, 0, 0] := by
  decide +kernel

theorem rows10282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10282 = true := by
  decide +kernel

theorem tot10282 : totK PD2M8K2 D2M8K2.t10282 = [0, 0, 216355355767, 496150743313, 165558523022, 3336250681, 0, 0] := by
  decide +kernel

theorem rows10283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10283 = true := by
  decide +kernel

theorem tot10283 : totK PD2M8K2 D2M8K2.t10283 = [0, 0, 191287448373, 461957147021, 220742803969, 16730491881, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
