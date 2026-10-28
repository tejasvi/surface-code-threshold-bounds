import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t100 = true := by
  decide +kernel

theorem tot100 : totK PD2M8K2 D2M8K2.t100 = [0, 0, 320663598985, 458771549480, 67698573933, 1053411165, 0, 0] := by
  decide +kernel

theorem rows101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t101 = true := by
  decide +kernel

theorem tot101 : totK PD2M8K2 D2M8K2.t101 = [0, 85071533861, 317821637967, 363521978116, 92311364191, 3667207281, 0, 0] := by
  decide +kernel

theorem rows102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t102 = true := by
  decide +kernel

theorem tot102 : totK PD2M8K2 D2M8K2.t102 = [0, 175947200805, 448574624570, 254736130953, 23028792512, 0, 0, 0] := by
  decide +kernel

theorem rows103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t103 = true := by
  decide +kernel

theorem tot103 : totK PD2M8K2 D2M8K2.t103 = [22498951891, 180305392360, 430357542631, 260668665289, 22092694014, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
