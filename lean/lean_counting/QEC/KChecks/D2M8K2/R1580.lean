import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6320 = true := by
  decide +kernel

theorem tot6320 : totK PD2M8K2 D2M8K2.t6320 = [0, 0, 266854793182, 492360217060, 125473093205, 3699256714, 0, 0] := by
  decide +kernel

theorem rows6321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6321 = true := by
  decide +kernel

theorem tot6321 : totK PD2M8K2 D2M8K2.t6321 = [0, 0, 197751162037, 490049522592, 197758994025, 10122467735, 0, 0] := by
  decide +kernel

theorem rows6322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6322 = true := by
  decide +kernel

theorem tot6322 : totK PD2M8K2 D2M8K2.t6322 = [0, 0, 163752460680, 465488948196, 205290210519, 10508483767, 0, 0] := by
  decide +kernel

theorem rows6323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6323 = true := by
  decide +kernel

theorem tot6323 : totK PD2M8K2 D2M8K2.t6323 = [0, 0, 86084750795, 343066547866, 355363143366, 70699679437, 1275377855, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
