import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13688 = true := by
  decide +kernel

theorem tot13688 : totK PD2M8K2 D2M8K2.t13688 = [0, 182307975947, 464495387233, 235808136801, 16886077592, 0, 0, 0] := by
  decide +kernel

theorem rows13689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13689 = true := by
  decide +kernel

theorem tot13689 : totK PD2M8K2 D2M8K2.t13689 = [0, 0, 291299121992, 505466050738, 100841202766, 1268739303, 0, 0] := by
  decide +kernel

theorem rows13690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13690 = true := by
  decide +kernel

theorem tot13690 : totK PD2M8K2 D2M8K2.t13690 = [0, 0, 211416693628, 476897647676, 164310285646, 7362961718, 0, 0] := by
  decide +kernel

theorem rows13691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13691 = true := by
  decide +kernel

theorem tot13691 : totK PD2M8K2 D2M8K2.t13691 = [0, 0, 181328877086, 476060481839, 214401272209, 14510083306, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
