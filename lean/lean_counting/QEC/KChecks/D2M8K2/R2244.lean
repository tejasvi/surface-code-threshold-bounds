import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8976 = true := by
  decide +kernel

theorem tot8976 : totK PD2M8K2 D2M8K2.t8976 = [0, 0, 303040068162, 475169102217, 92224441182, 1095107716, 0, 0] := by
  decide +kernel

theorem rows8977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8977 = true := by
  decide +kernel

theorem tot8977 : totK PD2M8K2 D2M8K2.t8977 = [166303772541, 345228622885, 141482423577, 145686043079, 79914636636, 3882006667, 0, 0] := by
  decide +kernel

theorem rows8978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8978 = true := by
  decide +kernel

theorem tot8978 : totK PD2M8K2 D2M8K2.t8978 = [152359659646, 445559371344, 255624423562, 17995526292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8979 = true := by
  decide +kernel

theorem tot8979 : totK PD2M8K2 D2M8K2.t8979 = [88990076640, 332251698217, 385034607523, 91206728120, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
