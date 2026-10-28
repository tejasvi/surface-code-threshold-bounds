import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9176 = true := by
  decide +kernel

theorem tot9176 : totK PD2M8K2 D2M8K2.t9176 = [0, 174128374857, 459261138244, 226603456406, 13629821414, 0, 0, 0] := by
  decide +kernel

theorem rows9177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9177 = true := by
  decide +kernel

theorem tot9177 : totK PD2M8K2 D2M8K2.t9177 = [0, 177736003433, 469160310466, 229354235855, 12885670648, 0, 0, 0] := by
  decide +kernel

theorem rows9178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9178 = true := by
  decide +kernel

theorem tot9178 : totK PD2M8K2 D2M8K2.t9178 = [0, 202093661411, 466169793487, 218719534542, 12679943201, 0, 0, 0] := by
  decide +kernel

theorem rows9179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9179 = true := by
  decide +kernel

theorem tot9179 : totK PD2M8K2 D2M8K2.t9179 = [0, 184978133017, 476172057418, 217632077664, 12595094539, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
