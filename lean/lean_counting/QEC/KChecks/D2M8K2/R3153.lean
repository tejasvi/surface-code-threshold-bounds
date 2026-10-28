import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12612 = true := by
  decide +kernel

theorem tot12612 : totK PD2M8K2 D2M8K2.t12612 = [0, 87240234242, 308546247407, 392080361406, 112369478695, 4257574148, 0, 0] := by
  decide +kernel

theorem rows12613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12613 = true := by
  decide +kernel

theorem tot12613 : totK PD2M8K2 D2M8K2.t12613 = [0, 160516909813, 460126787833, 264681656987, 22001946431, 0, 0, 0] := by
  decide +kernel

theorem rows12614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12614 = true := by
  decide +kernel

theorem tot12614 : totK PD2M8K2 D2M8K2.t12614 = [0, 180075851965, 460058749877, 249171854256, 16131818011, 0, 0, 0] := by
  decide +kernel

theorem rows12615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12615 = true := by
  decide +kernel

theorem tot12615 : totK PD2M8K2 D2M8K2.t12615 = [0, 0, 276299737262, 500154141970, 119525477857, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
