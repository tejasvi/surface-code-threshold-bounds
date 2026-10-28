import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12468 = true := by
  decide +kernel

theorem tot12468 : totK PD2M8K2 D2M8K2.t12468 = [0, 174553809823, 466999865620, 244795650423, 15248594464, 0, 0, 0] := by
  decide +kernel

theorem rows12469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12469 = true := by
  decide +kernel

theorem tot12469 : totK PD2M8K2 D2M8K2.t12469 = [0, 0, 282858309461, 507775798334, 112026164917, 1369150432, 0, 0] := by
  decide +kernel

theorem rows12470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12470 = true := by
  decide +kernel

theorem tot12470 : totK PD2M8K2 D2M8K2.t12470 = [0, 87964691079, 402068864542, 380642698846, 42138688121, 0, 0, 0] := by
  decide +kernel

theorem rows12471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12471 = true := by
  decide +kernel

theorem tot12471 : totK PD2M8K2 D2M8K2.t12471 = [0, 183665635996, 443398102902, 248629448484, 22788479236, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
