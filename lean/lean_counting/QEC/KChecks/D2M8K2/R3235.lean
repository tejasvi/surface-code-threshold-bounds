import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12940 = true := by
  decide +kernel

theorem tot12940 : totK PD2M8K2 D2M8K2.t12940 = [0, 0, 0, 221141560893, 497801967748, 168554172181, 3805953177, 0] := by
  decide +kernel

theorem rows12941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12941 = true := by
  decide +kernel

theorem tot12941 : totK PD2M8K2 D2M8K2.t12941 = [0, 0, 160253043472, 458622056555, 258445325948, 41889393366, 1353333895, 0] := by
  decide +kernel

theorem rows12942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12942 = true := by
  decide +kernel

theorem tot12942 : totK PD2M8K2 D2M8K2.t12942 = [0, 0, 177706053037, 453201329506, 251590961630, 17823462189, 0, 0] := by
  decide +kernel

theorem rows12943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12943 = true := by
  decide +kernel

theorem tot12943 : totK PD2M8K2 D2M8K2.t12943 = [0, 0, 85468195920, 408427463255, 369604701022, 34693515161, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
