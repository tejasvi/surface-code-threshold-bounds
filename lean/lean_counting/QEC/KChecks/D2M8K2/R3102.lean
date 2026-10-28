import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12408 = true := by
  decide +kernel

theorem tot12408 : totK PD2M8K2 D2M8K2.t12408 = [0, 177781631315, 454787477977, 242768987591, 18068955215, 0, 0, 0] := by
  decide +kernel

theorem rows12409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12409 = true := by
  decide +kernel

theorem tot12409 : totK PD2M8K2 D2M8K2.t12409 = [0, 0, 311855228501, 490658196854, 91080651180, 1096505104, 0, 0] := by
  decide +kernel

theorem rows12410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12410 = true := by
  decide +kernel

theorem tot12410 : totK PD2M8K2 D2M8K2.t12410 = [0, 79593250177, 305347076481, 389092093630, 109110242628, 3884009855, 0, 0] := by
  decide +kernel

theorem rows12411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12411 = true := by
  decide +kernel

theorem tot12411 : totK PD2M8K2 D2M8K2.t12411 = [0, 172989078723, 454011001612, 262167155546, 22233834688, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
