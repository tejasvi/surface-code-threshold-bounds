import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2016 = true := by
  decide +kernel

theorem tot2016 : totK PD2M8K2 D2M8K2.t2016 = [0, 180567783026, 478574125164, 244349623123, 13916467904, 0, 0, 0] := by
  decide +kernel

theorem rows2017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2017 = true := by
  decide +kernel

theorem tot2017 : totK PD2M8K2 D2M8K2.t2017 = [0, 0, 277233713886, 500472987348, 103599452244, 1096505104, 0, 0] := by
  decide +kernel

theorem rows2018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2018 = true := by
  decide +kernel

theorem tot2018 : totK PD2M8K2 D2M8K2.t2018 = [0, 97099583008, 340445666092, 351699210465, 96269384715, 3884009855, 0, 0] := by
  decide +kernel

theorem rows2019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2019 = true := by
  decide +kernel

theorem tot2019 : totK PD2M8K2 D2M8K2.t2019 = [0, 174452955571, 446167544432, 253479932033, 25267414026, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
