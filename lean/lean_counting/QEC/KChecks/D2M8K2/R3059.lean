import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12236 = true := by
  decide +kernel

theorem tot12236 : totK PD2M8K2 D2M8K2.t12236 = [0, 19821533299, 279480237638, 498863562292, 111464277840, 1415142070, 0, 0] := by
  decide +kernel

theorem rows12237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12237 = true := by
  decide +kernel

theorem tot12237 : totK PD2M8K2 D2M8K2.t12237 = [0, 169983397059, 443742621837, 271390397628, 28470728937, 0, 0, 0] := by
  decide +kernel

theorem rows12238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12238 = true := by
  decide +kernel

theorem tot12238 : totK PD2M8K2 D2M8K2.t12238 = [0, 139227593975, 436719151098, 302274334759, 33962437311, 0, 0, 0] := by
  decide +kernel

theorem rows12239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12239 = true := by
  decide +kernel

theorem tot12239 : totK PD2M8K2 D2M8K2.t12239 = [0, 0, 227779902599, 499758758951, 153524462620, 2484078857, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
