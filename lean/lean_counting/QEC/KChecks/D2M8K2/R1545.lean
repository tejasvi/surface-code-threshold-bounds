import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6180 = true := by
  decide +kernel

theorem tot6180 : totK PD2M8K2 D2M8K2.t6180 = [0, 198606901494, 462731496645, 240670406156, 23089623618, 0, 0, 0] := by
  decide +kernel

theorem rows6181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6181 = true := by
  decide +kernel

theorem tot6181 : totK PD2M8K2 D2M8K2.t6181 = [0, 186024695365, 472216164147, 222736997336, 12320791933, 0, 0, 0] := by
  decide +kernel

theorem rows6182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6182 = true := by
  decide +kernel

theorem tot6182 : totK PD2M8K2 D2M8K2.t6182 = [0, 19373123746, 373271517719, 460610299928, 56427728826, 0, 0, 0] := by
  decide +kernel

theorem rows6183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6183 = true := by
  decide +kernel

theorem tot6183 : totK PD2M8K2 D2M8K2.t6183 = [0, 41639313632, 233988857762, 456308755745, 152964231368, 5159868635, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
