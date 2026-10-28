import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3100 = true := by
  decide +kernel

theorem tot3100 : totK PD2M8K2 D2M8K2.t3100 = [170955329715, 458427186253, 245575228718, 15248594464, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3101 = true := by
  decide +kernel

theorem tot3101 : totK PD2M8K2 D2M8K2.t3101 = [0, 280940283760, 502991152740, 111997305977, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows3102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3102 = true := by
  decide +kernel

theorem tot3102 : totK PD2M8K2 D2M8K2.t3102 = [106340949436, 403102365551, 357367395976, 39099446791, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3103 = true := by
  decide +kernel

theorem tot3103 : totK PD2M8K2 D2M8K2.t3103 = [180959270265, 445370012069, 261349755331, 27507102568, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
