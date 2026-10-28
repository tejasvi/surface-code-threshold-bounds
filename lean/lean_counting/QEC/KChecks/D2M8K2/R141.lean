import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t564 = true := by
  decide +kernel

theorem tot564 : totK PD2M8K2 D2M8K2.t564 = [0, 0, 185289926089, 467133664168, 207765360738, 13571811843, 0, 0] := by
  decide +kernel

theorem rows565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t565 = true := by
  decide +kernel

theorem tot565 : totK PD2M8K2 D2M8K2.t565 = [0, 0, 199798149501, 463271404520, 195336330070, 11898096860, 0, 0] := by
  decide +kernel

theorem rows566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t566 = true := by
  decide +kernel

theorem tot566 : totK PD2M8K2 D2M8K2.t566 = [0, 0, 37211769235, 346105430897, 389844501605, 60139450146, 1061529118, 0] := by
  decide +kernel

theorem rows567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t567 = true := by
  decide +kernel

theorem tot567 : totK PD2M8K2 D2M8K2.t567 = [0, 78129874012, 113195878156, 225403684119, 342754740675, 88416424087, 3718133097, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
