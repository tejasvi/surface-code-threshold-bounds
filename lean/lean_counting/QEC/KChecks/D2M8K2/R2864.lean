import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11456 = true := by
  decide +kernel

theorem tot11456 : totK PD2M8K2 D2M8K2.t11456 = [0, 0, 86023540623, 400160127251, 362119520114, 35844985901, 0, 0] := by
  decide +kernel

theorem rows11457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11457 = true := by
  decide +kernel

theorem tot11457 : totK PD2M8K2 D2M8K2.t11457 = [0, 0, 0, 210864373636, 481555589043, 157704164617, 5320761635, 0] := by
  decide +kernel

theorem rows11458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11458 = true := by
  decide +kernel

theorem tot11458 : totK PD2M8K2 D2M8K2.t11458 = [0, 0, 181982347517, 464995377700, 231596228152, 16131077680, 0, 0] := by
  decide +kernel

theorem rows11459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11459 = true := by
  decide +kernel

theorem tot11459 : totK PD2M8K2 D2M8K2.t11459 = [0, 0, 210819169435, 482192370176, 197353681478, 9721971944, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
