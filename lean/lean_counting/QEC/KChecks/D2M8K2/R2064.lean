import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8256 = true := by
  decide +kernel

theorem tot8256 : totK PD2M8K2 D2M8K2.t8256 = [87070194960, 340439413745, 389218073696, 80836119867, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows8257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8257 = true := by
  decide +kernel

theorem tot8257 : totK PD2M8K2 D2M8K2.t8257 = [0, 229619636554, 483502835760, 164014042855, 9404247146, 0, 0, 0] := by
  decide +kernel

theorem rows8258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8258 = true := by
  decide +kernel

theorem tot8258 : totK PD2M8K2 D2M8K2.t8258 = [149457552900, 391901521380, 287011245442, 59378461312, 2481160468, 0, 0, 0] := by
  decide +kernel

theorem rows8259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8259 = true := by
  decide +kernel

theorem tot8259 : totK PD2M8K2 D2M8K2.t8259 = [154414556097, 445098267819, 271475052530, 27135455893, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
