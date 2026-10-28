import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11076 = true := by
  decide +kernel

theorem tot11076 : totK PD2M8K2 D2M8K2.t11076 = [0, 0, 304456770164, 478777305855, 90235448730, 1095107716, 0, 0] := by
  decide +kernel

theorem rows11077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11077 = true := by
  decide +kernel

theorem tot11077 : totK PD2M8K2 D2M8K2.t11077 = [176301523965, 350521227424, 138582090186, 145759829480, 77816245602, 3882006667, 0, 0] := by
  decide +kernel

theorem rows11078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11078 = true := by
  decide +kernel

theorem tot11078 : totK PD2M8K2 D2M8K2.t11078 = [155976419661, 450061377628, 254106972210, 18182990193, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11079 = true := by
  decide +kernel

theorem tot11079 : totK PD2M8K2 D2M8K2.t11079 = [89049893349, 360640750425, 372226912930, 78086127685, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
