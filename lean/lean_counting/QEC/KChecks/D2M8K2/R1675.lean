import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6700 = true := by
  decide +kernel

theorem tot6700 : totK PD2M8K2 D2M8K2.t6700 = [0, 3757117624, 208743238818, 502324533414, 182279975526, 5393550755, 0, 0] := by
  decide +kernel

theorem rows6701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6701 = true := by
  decide +kernel

theorem tot6701 : totK PD2M8K2 D2M8K2.t6701 = [0, 185453502675, 448703906354, 243739601645, 22743001907, 0, 0, 0] := by
  decide +kernel

theorem rows6702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6702 = true := by
  decide +kernel

theorem tot6702 : totK PD2M8K2 D2M8K2.t6702 = [0, 193142013850, 477319441559, 222478668720, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows6703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6703 = true := by
  decide +kernel

theorem tot6703 : totK PD2M8K2 D2M8K2.t6703 = [0, 37500061737, 323706848947, 439087309054, 82151137656, 1128973710, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
