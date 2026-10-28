import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8608 = true := by
  decide +kernel

theorem tot8608 : totK PD2M8K2 D2M8K2.t8608 = [180336723352, 458167683717, 259595019712, 24434903335, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8609 = true := by
  decide +kernel

theorem tot8609 : totK PD2M8K2 D2M8K2.t8609 = [157470194010, 469394943570, 263992054865, 16457793064, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8610 = true := by
  decide +kernel

theorem tot8610 : totK PD2M8K2 D2M8K2.t8610 = [0, 255952731344, 500189833182, 131242973252, 2348440009, 0, 0, 0] := by
  decide +kernel

theorem rows8611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8611 = true := by
  decide +kernel

theorem tot8611 : totK PD2M8K2 D2M8K2.t8611 = [56610377076, 237457437580, 406384903443, 174216066605, 10902245252, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
