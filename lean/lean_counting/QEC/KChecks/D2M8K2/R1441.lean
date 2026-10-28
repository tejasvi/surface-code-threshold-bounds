import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5764 = true := by
  decide +kernel

theorem tot5764 : totK PD2M8K2 D2M8K2.t5764 = [0, 0, 273383456265, 505400577656, 127506536426, 1402015981, 0, 0] := by
  decide +kernel

theorem rows5765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5765 = true := by
  decide +kernel

theorem tot5765 : totK PD2M8K2 D2M8K2.t5765 = [0, 84969655104, 271874113592, 368080961345, 157634582361, 8173611642, 0, 0] := by
  decide +kernel

theorem rows5766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5766 = true := by
  decide +kernel

theorem tot5766 : totK PD2M8K2 D2M8K2.t5766 = [0, 172139820732, 457089308577, 264691862087, 25735362705, 0, 0, 0] := by
  decide +kernel

theorem rows5767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5767 = true := by
  decide +kernel

theorem tot5767 : totK PD2M8K2 D2M8K2.t5767 = [0, 156859006062, 451703455227, 274462785953, 21249392482, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
