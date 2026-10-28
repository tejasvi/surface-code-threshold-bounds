import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1332 = true := by
  decide +kernel

theorem tot1332 : totK PD2M8K2 D2M8K2.t1332 = [127001226279, 439218003039, 327793497175, 29160977104, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1333 = true := by
  decide +kernel

theorem tot1333 : totK PD2M8K2 D2M8K2.t1333 = [0, 212692112981, 493246632992, 177586168717, 4967996017, 0, 0, 0] := by
  decide +kernel

theorem rows1334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1334 = true := by
  decide +kernel

theorem tot1334 : totK PD2M8K2 D2M8K2.t1334 = [0, 196340526987, 458981311513, 221174674280, 17080783126, 0, 0, 0] := by
  decide +kernel

theorem rows1335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1335 = true := by
  decide +kernel

theorem tot1335 : totK PD2M8K2 D2M8K2.t1335 = [0, 204365962642, 494911254608, 193116706488, 5336070015, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
