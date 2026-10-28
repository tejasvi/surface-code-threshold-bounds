import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7568 = true := by
  decide +kernel

theorem tot7568 : totK PD2M8K2 D2M8K2.t7568 = [0, 0, 0, 293595340380, 471898435954, 85066262970, 1206465782, 0] := by
  decide +kernel

theorem rows7569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7569 = true := by
  decide +kernel

theorem tot7569 : totK PD2M8K2 D2M8K2.t7569 = [0, 0, 107608872648, 399222345147, 354562017848, 40586110412, 0, 0] := by
  decide +kernel

theorem rows7570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7570 = true := by
  decide +kernel

theorem tot7570 : totK PD2M8K2 D2M8K2.t7570 = [0, 0, 214018701236, 492077352405, 199206242224, 8500385581, 0, 0] := by
  decide +kernel

theorem rows7571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7571 = true := by
  decide +kernel

theorem tot7571 : totK PD2M8K2 D2M8K2.t7571 = [0, 0, 185329760205, 476125449462, 221991316265, 14029660444, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
