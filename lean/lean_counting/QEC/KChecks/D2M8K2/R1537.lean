import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6148 = true := by
  decide +kernel

theorem tot6148 : totK PD2M8K2 D2M8K2.t6148 = [0, 173371456026, 472988828509, 233168398658, 12885670648, 0, 0, 0] := by
  decide +kernel

theorem rows6149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6149 = true := by
  decide +kernel

theorem tot6149 : totK PD2M8K2 D2M8K2.t6149 = [0, 198674094579, 457843319998, 205450507951, 12319708528, 0, 0, 0] := by
  decide +kernel

theorem rows6150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6150 = true := by
  decide +kernel

theorem tot6150 : totK PD2M8K2 D2M8K2.t6150 = [0, 190815210838, 485422624315, 212886905166, 10178307621, 0, 0, 0] := by
  decide +kernel

theorem rows6151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6151 = true := by
  decide +kernel

theorem tot6151 : totK PD2M8K2 D2M8K2.t6151 = [0, 162212370156, 450302731876, 236350683158, 15723602574, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
