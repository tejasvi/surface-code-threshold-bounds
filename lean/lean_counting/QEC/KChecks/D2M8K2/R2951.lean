import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11804 = true := by
  decide +kernel

theorem tot11804 : totK PD2M8K2 D2M8K2.t11804 = [0, 0, 211162311475, 497715471400, 184024967506, 5023145519, 0, 0] := by
  decide +kernel

theorem rows11805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11805 = true := by
  decide +kernel

theorem tot11805 : totK PD2M8K2 D2M8K2.t11805 = [0, 0, 208739746990, 482218519778, 189797821465, 10599746186, 0, 0] := by
  decide +kernel

theorem rows11806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11806 = true := by
  decide +kernel

theorem tot11806 : totK PD2M8K2 D2M8K2.t11806 = [0, 0, 177941668160, 455977357340, 252200979677, 23241079343, 0, 0] := by
  decide +kernel

theorem rows11807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11807 = true := by
  decide +kernel

theorem tot11807 : totK PD2M8K2 D2M8K2.t11807 = [0, 0, 137832962210, 447472544111, 275010737751, 19845599051, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
