import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10156 = true := by
  decide +kernel

theorem tot10156 : totK PD2M8K2 D2M8K2.t10156 = [0, 160260617901, 481897558894, 250353705343, 12705204832, 0, 0, 0] := by
  decide +kernel

theorem rows10157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10157 = true := by
  decide +kernel

theorem tot10157 : totK PD2M8K2 D2M8K2.t10157 = [0, 88788571313, 348268248345, 375648778212, 83252340222, 1369150432, 0, 0] := by
  decide +kernel

theorem rows10158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10158 = true := by
  decide +kernel

theorem tot10158 : totK PD2M8K2 D2M8K2.t10158 = [0, 93610018881, 391543613685, 404957539206, 47851325003, 0, 0, 0] := by
  decide +kernel

theorem rows10159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10159 = true := by
  decide +kernel

theorem tot10159 : totK PD2M8K2 D2M8K2.t10159 = [0, 173278494500, 434620600964, 263993317971, 29731632040, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
