import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12520 = true := by
  decide +kernel

theorem tot12520 : totK PD2M8K2 D2M8K2.t12520 = [0, 0, 168403117094, 461676650873, 216022609110, 8876103891, 0, 0] := by
  decide +kernel

theorem rows12521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12521 = true := by
  decide +kernel

theorem tot12521 : totK PD2M8K2 D2M8K2.t12521 = [0, 0, 0, 299506920511, 467018219050, 83658659457, 1206465782, 0] := by
  decide +kernel

theorem rows12522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12522 = true := by
  decide +kernel

theorem tot12522 : totK PD2M8K2 D2M8K2.t12522 = [0, 0, 141951066431, 431368923474, 306701274433, 28014713063, 0, 0] := by
  decide +kernel

theorem rows12523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12523 = true := by
  decide +kernel

theorem tot12523 : totK PD2M8K2 D2M8K2.t12523 = [0, 0, 187893386569, 484462413712, 211416501627, 11222661413, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
