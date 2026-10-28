import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12804 = true := by
  decide +kernel

theorem tot12804 : totK PD2M8K2 D2M8K2.t12804 = [0, 0, 283571038771, 514176019033, 105848064439, 1096505104, 0, 0] := by
  decide +kernel

theorem rows12805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12805 = true := by
  decide +kernel

theorem tot12805 : totK PD2M8K2 D2M8K2.t12805 = [0, 119263646302, 345410350509, 326597345257, 95732332967, 3884009855, 0, 0] := by
  decide +kernel

theorem rows12806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12806 = true := by
  decide +kernel

theorem tot12806 : totK PD2M8K2 D2M8K2.t12806 = [0, 176962515597, 451355289736, 265822402739, 27391990928, 0, 0, 0] := by
  decide +kernel

theorem rows12807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12807 = true := by
  decide +kernel

theorem tot12807 : totK PD2M8K2 D2M8K2.t12807 = [0, 90506494674, 362978797458, 364409421238, 69222133257, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
