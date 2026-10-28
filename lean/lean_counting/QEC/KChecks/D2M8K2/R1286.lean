import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5144 = true := by
  decide +kernel

theorem tot5144 : totK PD2M8K2 D2M8K2.t5144 = [0, 0, 193373530450, 497602649435, 223837843559, 8988926099, 0, 0] := by
  decide +kernel

theorem rows5145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5145 = true := by
  decide +kernel

theorem tot5145 : totK PD2M8K2 D2M8K2.t5145 = [0, 0, 0, 231852407685, 496685492889, 180676256696, 9631076594, 0] := by
  decide +kernel

theorem rows5146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5146 = true := by
  decide +kernel

theorem tot5146 : totK PD2M8K2 D2M8K2.t5146 = [0, 0, 7564999111, 237980954393, 490412559252, 169170351106, 5382912678, 0] := by
  decide +kernel

theorem rows5147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5147 = true := by
  decide +kernel

theorem tot5147 : totK PD2M8K2 D2M8K2.t5147 = [0, 0, 183352801061, 460104266956, 242287025487, 22674457381, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
