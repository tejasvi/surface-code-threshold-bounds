import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5052 = true := by
  decide +kernel

theorem tot5052 : totK PD2M8K2 D2M8K2.t5052 = [0, 177411068780, 424396122505, 258028657708, 56517270459, 2814597007, 0, 0] := by
  decide +kernel

theorem rows5053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5053 = true := by
  decide +kernel

theorem tot5053 : totK PD2M8K2 D2M8K2.t5053 = [0, 152763315545, 456307973515, 289782991379, 22119516581, 0, 0, 0] := by
  decide +kernel

theorem rows5054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5054 = true := by
  decide +kernel

theorem tot5054 : totK PD2M8K2 D2M8K2.t5054 = [0, 0, 221036320861, 493888810388, 166980390131, 5011483316, 0, 0] := by
  decide +kernel

theorem rows5055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5055 = true := by
  decide +kernel

theorem tot5055 : totK PD2M8K2 D2M8K2.t5055 = [0, 0, 193514848818, 470810901206, 205577994356, 13260151287, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
