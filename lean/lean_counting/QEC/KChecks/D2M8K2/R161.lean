import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t644 = true := by
  decide +kernel

theorem tot644 : totK PD2M8K2 D2M8K2.t644 = [0, 66146824114, 281162867048, 392609265373, 128252050883, 5218872685, 0, 0] := by
  decide +kernel

theorem rows645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t645 = true := by
  decide +kernel

theorem tot645 : totK PD2M8K2 D2M8K2.t645 = [0, 156438996454, 439848887043, 277497355474, 28889976920, 0, 0, 0] := by
  decide +kernel

theorem rows646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t646 = true := by
  decide +kernel

theorem tot646 : totK PD2M8K2 D2M8K2.t646 = [0, 176689974734, 460870445131, 238595312491, 14893761650, 0, 0, 0] := by
  decide +kernel

theorem rows647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t647 = true := by
  decide +kernel

theorem tot647 : totK PD2M8K2 D2M8K2.t647 = [0, 0, 335039948366, 509880188767, 59989950210, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
