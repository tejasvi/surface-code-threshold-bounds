import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15016 = true := by
  decide +kernel

theorem tot15016 : totK PD2M8K2 D2M8K2.t15016 = [0, 0, 179938033940, 480768183356, 206821419515, 6624307572, 0, 0] := by
  decide +kernel

theorem rows15017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15017 = true := by
  decide +kernel

theorem tot15017 : totK PD2M8K2 D2M8K2.t15017 = [0, 0, 132835075690, 439636334790, 264647006896, 16506508964, 0, 0] := by
  decide +kernel

theorem rows15018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15018 = true := by
  decide +kernel

theorem tot15018 : totK PD2M8K2 D2M8K2.t15018 = [0, 0, 0, 315933699387, 457496466382, 69342209721, 1200365979, 0] := by
  decide +kernel

theorem rows15019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15019 = true := by
  decide +kernel

theorem tot15019 : totK PD2M8K2 D2M8K2.t15019 = [0, 0, 244017569381, 487932033546, 185403602464, 10170046270, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
