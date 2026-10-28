import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4124 = true := by
  decide +kernel

theorem tot4124 : totK PD2M8K2 D2M8K2.t4124 = [0, 0, 76889325312, 312410958946, 379614449104, 92304573547, 2417524611, 0] := by
  decide +kernel

theorem rows4125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4125 = true := by
  decide +kernel

theorem tot4125 : totK PD2M8K2 D2M8K2.t4125 = [0, 0, 157416904029, 459105171590, 271604835103, 20872377286, 0, 0] := by
  decide +kernel

theorem rows4126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4126 = true := by
  decide +kernel

theorem tot4126 : totK PD2M8K2 D2M8K2.t4126 = [0, 0, 180937872387, 462644818018, 249993262077, 17039419393, 0, 0] := by
  decide +kernel

theorem rows4127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4127 = true := by
  decide +kernel

theorem tot4127 : totK PD2M8K2 D2M8K2.t4127 = [0, 190813401391, 441845710584, 203436853414, 42639253881, 7093611788, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
