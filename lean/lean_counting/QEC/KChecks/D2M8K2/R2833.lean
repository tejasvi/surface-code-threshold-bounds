import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11332 = true := by
  decide +kernel

theorem tot11332 : totK PD2M8K2 D2M8K2.t11332 = [149167974124, 356890713345, 277604822884, 111300372714, 6801036714, 0, 0, 0] := by
  decide +kernel

theorem rows11333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11333 = true := by
  decide +kernel

theorem tot11333 : totK PD2M8K2 D2M8K2.t11333 = [163321448542, 437464013683, 279394481450, 30368503698, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11334 = true := by
  decide +kernel

theorem tot11334 : totK PD2M8K2 D2M8K2.t11334 = [101331513776, 400183069804, 328644797356, 50042864240, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows11335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11335 = true := by
  decide +kernel

theorem tot11335 : totK PD2M8K2 D2M8K2.t11335 = [0, 232261134678, 494095778377, 163643372843, 8423393484, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
