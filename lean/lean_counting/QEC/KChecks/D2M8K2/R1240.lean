import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4960 = true := by
  decide +kernel

theorem tot4960 : totK PD2M8K2 D2M8K2.t4960 = [0, 4294967296, 177150046941, 462076066886, 223834764543, 13874764603, 0, 0] := by
  decide +kernel

theorem rows4961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4961 = true := by
  decide +kernel

theorem tot4961 : totK PD2M8K2 D2M8K2.t4961 = [0, 178221308542, 447879007821, 273619331249, 28897527934, 0, 0, 0] := by
  decide +kernel

theorem rows4962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4962 = true := by
  decide +kernel

theorem tot4962 : totK PD2M8K2 D2M8K2.t4962 = [0, 187582684392, 480157062503, 232504787225, 13616063940, 0, 0, 0] := by
  decide +kernel

theorem rows4963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4963 = true := by
  decide +kernel

theorem tot4963 : totK PD2M8K2 D2M8K2.t4963 = [0, 74801530329, 302430145543, 373283088158, 161254600581, 17186218589, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
