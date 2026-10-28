import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6172 = true := by
  decide +kernel

theorem tot6172 : totK PD2M8K2 D2M8K2.t6172 = [171412815235, 461349588081, 254091484086, 16368716987, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6173 = true := by
  decide +kernel

theorem tot6173 : totK PD2M8K2 D2M8K2.t6173 = [0, 280682101396, 503623275759, 118728545544, 1267860612, 0, 0, 0] := by
  decide +kernel

theorem rows6174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6174 = true := by
  decide +kernel

theorem tot6174 : totK PD2M8K2 D2M8K2.t6174 = [0, 186011226298, 480942772976, 203386338682, 8505075386, 0, 0, 0] := by
  decide +kernel

theorem rows6175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6175 = true := by
  decide +kernel

theorem tot6175 : totK PD2M8K2 D2M8K2.t6175 = [0, 182748149967, 438135308980, 270681704846, 34168072533, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
