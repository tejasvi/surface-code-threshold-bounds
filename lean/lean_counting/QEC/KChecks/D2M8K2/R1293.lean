import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5172 = true := by
  decide +kernel

theorem tot5172 : totK PD2M8K2 D2M8K2.t5172 = [0, 0, 0, 307185821789, 485572096583, 90832903588, 1096505104, 0] := by
  decide +kernel

theorem rows5173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5173 = true := by
  decide +kernel

theorem tot5173 : totK PD2M8K2 D2M8K2.t5173 = [0, 0, 66973279467, 303692873783, 412437913842, 111785753462, 3884009855, 0] := by
  decide +kernel

theorem rows5174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5174 = true := by
  decide +kernel

theorem tot5174 : totK PD2M8K2 D2M8K2.t5174 = [0, 0, 174711288191, 461726374677, 266415896433, 24464796624, 0, 0] := by
  decide +kernel

theorem rows5175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5175 = true := by
  decide +kernel

theorem tot5175 : totK PD2M8K2 D2M8K2.t5175 = [0, 0, 88181892969, 412091687988, 373632607281, 43827876710, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
