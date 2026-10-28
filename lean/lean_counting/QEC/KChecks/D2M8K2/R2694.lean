import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10776 = true := by
  decide +kernel

theorem tot10776 : totK PD2M8K2 D2M8K2.t10776 = [0, 174871126750, 447451252934, 268926660429, 30265502258, 0, 0, 0] := by
  decide +kernel

theorem rows10777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10777 = true := by
  decide +kernel

theorem tot10777 : totK PD2M8K2 D2M8K2.t10777 = [0, 187027825039, 472568136159, 222010353060, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows10778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10778 = true := by
  decide +kernel

theorem tot10778 : totK PD2M8K2 D2M8K2.t10778 = [0, 49139168205, 326856332877, 434731279590, 93744049445, 1198073392, 0, 0] := by
  decide +kernel

theorem rows10779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10779 = true := by
  decide +kernel

theorem tot10779 : totK PD2M8K2 D2M8K2.t10779 = [0, 0, 196436570571, 464899416445, 194911595977, 12052611869, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
