import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15908 = true := by
  decide +kernel

theorem tot15908 : totK PD2M8K2 D2M8K2.t15908 = [0, 0, 191397464094, 474060776229, 224566694385, 12276343324, 0, 0] := by
  decide +kernel

theorem rows15909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15909 = true := by
  decide +kernel

theorem tot15909 : totK PD2M8K2 D2M8K2.t15909 = [0, 0, 199945061961, 483638917492, 214942216373, 11066126582, 0, 0] := by
  decide +kernel

theorem rows15910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15910 = true := by
  decide +kernel

theorem tot15910 : totK PD2M8K2 D2M8K2.t15910 = [0, 0, 185531508829, 475630991443, 222089740726, 12443528988, 0, 0] := by
  decide +kernel

theorem rows15911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15911 = true := by
  decide +kernel

theorem tot15911 : totK PD2M8K2 D2M8K2.t15911 = [0, 0, 170736284689, 469227498678, 226792902498, 13501461283, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
