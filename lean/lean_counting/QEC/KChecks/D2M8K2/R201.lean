import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t804 = true := by
  decide +kernel

theorem tot804 : totK PD2M8K2 D2M8K2.t804 = [0, 0, 233489757658, 504581917542, 155146026882, 2516391818, 0, 0] := by
  decide +kernel

theorem rows805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t805 = true := by
  decide +kernel

theorem tot805 : totK PD2M8K2 D2M8K2.t805 = [0, 14916241294, 184694295604, 445599271163, 219731817868, 15310102822, 0, 0] := by
  decide +kernel

theorem rows806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t806 = true := by
  decide +kernel

theorem tot806 : totK PD2M8K2 D2M8K2.t806 = [0, 215843558794, 498393134302, 173473252490, 4923067866, 0, 0, 0] := by
  decide +kernel

theorem rows807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t807 = true := by
  decide +kernel

theorem tot807 : totK PD2M8K2 D2M8K2.t807 = [0, 181710494332, 470771607188, 225808134956, 12534051746, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
