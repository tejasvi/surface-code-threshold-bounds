import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5216 = true := by
  decide +kernel

theorem tot5216 : totK PD2M8K2 D2M8K2.t5216 = [0, 179413670622, 447960292279, 258732946206, 30063430246, 0, 0, 0] := by
  decide +kernel

theorem rows5217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5217 = true := by
  decide +kernel

theorem tot5217 : totK PD2M8K2 D2M8K2.t5217 = [0, 202544835559, 471222064492, 212669960547, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows5218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5218 = true := by
  decide +kernel

theorem tot5218 : totK PD2M8K2 D2M8K2.t5218 = [0, 19358310964, 306622156130, 473707184649, 97210222901, 1198073392, 0, 0] := by
  decide +kernel

theorem rows5219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5219 = true := by
  decide +kernel

theorem tot5219 : totK PD2M8K2 D2M8K2.t5219 = [0, 50913068500, 281034407741, 440906765403, 126283903665, 4257574148, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
