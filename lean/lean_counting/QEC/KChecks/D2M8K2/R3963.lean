import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15852 = true := by
  decide +kernel

theorem tot15852 : totK PD2M8K2 D2M8K2.t15852 = [0, 169412605754, 461878531735, 243741506418, 13795945806, 0, 0, 0] := by
  decide +kernel

theorem rows15853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15853 = true := by
  decide +kernel

theorem tot15853 : totK PD2M8K2 D2M8K2.t15853 = [0, 0, 282087016831, 491786427032, 107650117188, 1369150432, 0, 0] := by
  decide +kernel

theorem rows15854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15854 = true := by
  decide +kernel

theorem tot15854 : totK PD2M8K2 D2M8K2.t15854 = [0, 93305483181, 372478519928, 395902247281, 52800943346, 0, 0, 0] := by
  decide +kernel

theorem rows15855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15855 = true := by
  decide +kernel

theorem tot15855 : totK PD2M8K2 D2M8K2.t15855 = [0, 157753113475, 451452746739, 285610228578, 22006210027, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
