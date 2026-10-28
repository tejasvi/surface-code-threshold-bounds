import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4656 = true := by
  decide +kernel

theorem tot4656 : totK PD2M8K2 D2M8K2.t4656 = [0, 194817203352, 471415752414, 225105091779, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows4657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4657 = true := by
  decide +kernel

theorem tot4657 : totK PD2M8K2 D2M8K2.t4657 = [0, 51744819491, 322698754362, 431179817293, 90151931467, 1198073392, 0, 0] := by
  decide +kernel

theorem rows4658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4658 = true := by
  decide +kernel

theorem tot4658 : totK PD2M8K2 D2M8K2.t4658 = [0, 0, 197903864648, 467867699606, 193290517879, 12052611869, 0, 0] := by
  decide +kernel

theorem rows4659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4659 = true := by
  decide +kernel

theorem tot4659 : totK PD2M8K2 D2M8K2.t4659 = [0, 153671077068, 432815108483, 284828041061, 34456931793, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
