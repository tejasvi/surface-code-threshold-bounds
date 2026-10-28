import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7692 = true := by
  decide +kernel

theorem tot7692 : totK PD2M8K2 D2M8K2.t7692 = [0, 0, 7461122728, 289681265717, 504371125185, 100127318884, 2813333534, 0] := by
  decide +kernel

theorem rows7693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7693 = true := by
  decide +kernel

theorem tot7693 : totK PD2M8K2 D2M8K2.t7693 = [0, 0, 204384527492, 462786832943, 236665977518, 23059168571, 0, 0] := by
  decide +kernel

theorem rows7694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7694 = true := by
  decide +kernel

theorem tot7694 : totK PD2M8K2 D2M8K2.t7694 = [0, 0, 203474773667, 496647379242, 204242095130, 8059207708, 0, 0] := by
  decide +kernel

theorem rows7695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7695 = true := by
  decide +kernel

theorem tot7695 : totK PD2M8K2 D2M8K2.t7695 = [0, 0, 0, 315269395457, 500677539435, 90928654092, 1032608332, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
