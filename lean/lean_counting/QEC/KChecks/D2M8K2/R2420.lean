import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9680 = true := by
  decide +kernel

theorem tot9680 : totK PD2M8K2 D2M8K2.t9680 = [0, 0, 164259996013, 480030016197, 224465095337, 9606496738, 0, 0] := by
  decide +kernel

theorem rows9681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9681 = true := by
  decide +kernel

theorem tot9681 : totK PD2M8K2 D2M8K2.t9681 = [0, 0, 175026618573, 460145183589, 221913009897, 16523765292, 0, 0] := by
  decide +kernel

theorem rows9682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9682 = true := by
  decide +kernel

theorem tot9682 : totK PD2M8K2 D2M8K2.t9682 = [0, 0, 219119061462, 498349200931, 146193151395, 2263943217, 0, 0] := by
  decide +kernel

theorem rows9683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9683 = true := by
  decide +kernel

theorem tot9683 : totK PD2M8K2 D2M8K2.t9683 = [0, 0, 0, 315378223863, 453648639348, 69155860623, 1166720416, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
