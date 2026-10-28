import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8016 = true := by
  decide +kernel

theorem tot8016 : totK PD2M8K2 D2M8K2.t8016 = [0, 0, 168812902995, 453487234656, 226691060080, 17044607505, 0, 0] := by
  decide +kernel

theorem rows8017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8017 = true := by
  decide +kernel

theorem tot8017 : totK PD2M8K2 D2M8K2.t8017 = [0, 0, 63052875745, 315969703617, 394283458232, 77857310000, 1326647619, 0] := by
  decide +kernel

theorem rows8018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8018 = true := by
  decide +kernel

theorem tot8018 : totK PD2M8K2 D2M8K2.t8018 = [0, 0, 76412018295, 364771926138, 394469905184, 37728256430, 0, 0] := by
  decide +kernel

theorem rows8019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8019 = true := by
  decide +kernel

theorem tot8019 : totK PD2M8K2 D2M8K2.t8019 = [0, 0, 165646000208, 431735414596, 277351064338, 27194830806, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
