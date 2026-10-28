import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11644 = true := by
  decide +kernel

theorem tot11644 : totK PD2M8K2 D2M8K2.t11644 = [91398613323, 358889704996, 359060246513, 66920387012, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows11645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11645 = true := by
  decide +kernel

theorem tot11645 : totK PD2M8K2 D2M8K2.t11645 = [0, 320081098466, 520013767082, 78876207353, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11646 = true := by
  decide +kernel

theorem tot11646 : totK PD2M8K2 D2M8K2.t11646 = [171051348884, 390809313764, 245015356373, 79809054606, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows11647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11647 = true := by
  decide +kernel

theorem tot11647 : totK PD2M8K2 D2M8K2.t11647 = [178201001267, 454491207419, 256981301252, 17914783095, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
