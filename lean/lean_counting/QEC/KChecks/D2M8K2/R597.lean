import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2388 = true := by
  decide +kernel

theorem tot2388 : totK PD2M8K2 D2M8K2.t2388 = [0, 0, 190678971866, 464077346986, 249268497636, 15839787604, 0, 0] := by
  decide +kernel

theorem rows2389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2389 = true := by
  decide +kernel

theorem tot2389 : totK PD2M8K2 D2M8K2.t2389 = [0, 0, 191116531916, 477258888253, 215364211199, 14342531486, 0, 0] := by
  decide +kernel

theorem rows2390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2390 = true := by
  decide +kernel

theorem tot2390 : totK PD2M8K2 D2M8K2.t2390 = [0, 0, 180399615677, 459316789669, 251233752541, 16767813208, 0, 0] := by
  decide +kernel

theorem rows2391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2391 = true := by
  decide +kernel

theorem tot2391 : totK PD2M8K2 D2M8K2.t2391 = [0, 0, 170770069420, 471570352720, 238102208182, 13354704708, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
