import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t440 = true := by
  decide +kernel

theorem tot440 : totK PD2M8K2 D2M8K2.t440 = [0, 0, 282202312720, 500043000084, 85949927559, 1310285577, 0, 0] := by
  decide +kernel

theorem rows441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t441 = true := by
  decide +kernel

theorem tot441 : totK PD2M8K2 D2M8K2.t441 = [0, 159061365373, 411195375132, 306355782520, 40280795260, 0, 0, 0] := by
  decide +kernel

theorem rows442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t442 = true := by
  decide +kernel

theorem tot442 : totK PD2M8K2 D2M8K2.t442 = [0, 169803802251, 475998120783, 255134980060, 13472350377, 0, 0, 0] := by
  decide +kernel

theorem rows443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t443 = true := by
  decide +kernel

theorem tot443 : totK PD2M8K2 D2M8K2.t443 = [0, 191230136703, 468724423342, 223653932620, 14800800293, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
