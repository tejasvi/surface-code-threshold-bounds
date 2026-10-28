import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9096 = true := by
  decide +kernel

theorem tot9096 : totK PD2M8K2 D2M8K2.t9096 = [0, 0, 156618724534, 447825292861, 247539108522, 19236246098, 0, 0] := by
  decide +kernel

theorem rows9097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9097 = true := by
  decide +kernel

theorem tot9097 : totK PD2M8K2 D2M8K2.t9097 = [0, 0, 86849245081, 359802101747, 336577969933, 57678140377, 1032241984, 0] := by
  decide +kernel

theorem rows9098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9098 = true := by
  decide +kernel

theorem tot9098 : totK PD2M8K2 D2M8K2.t9098 = [0, 0, 33733355426, 293459512496, 408325370873, 94290632975, 3598673838, 0] := by
  decide +kernel

theorem rows9099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9099 = true := by
  decide +kernel

theorem tot9099 : totK PD2M8K2 D2M8K2.t9099 = [0, 0, 202929685534, 473794451514, 199585932501, 11367430297, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
