import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8104 = true := by
  decide +kernel

theorem tot8104 : totK PD2M8K2 D2M8K2.t8104 = [0, 0, 19373123746, 371843932827, 462545664130, 57390252537, 0, 0] := by
  decide +kernel

theorem rows8105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8105 = true := by
  decide +kernel

theorem tot8105 : totK PD2M8K2 D2M8K2.t8105 = [0, 0, 52620357531, 248887070116, 425003292362, 151526289194, 5159868635, 0] := by
  decide +kernel

theorem rows8106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8106 = true := by
  decide +kernel

theorem tot8106 : totK PD2M8K2 D2M8K2.t8106 = [0, 0, 179298291271, 455184337213, 257997211616, 24271808348, 0, 0] := by
  decide +kernel

theorem rows8107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8107 = true := by
  decide +kernel

theorem tot8107 : totK PD2M8K2 D2M8K2.t8107 = [0, 0, 152927707517, 464811111132, 275314447222, 19081961901, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
