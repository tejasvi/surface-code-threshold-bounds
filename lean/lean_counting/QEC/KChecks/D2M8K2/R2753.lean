import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11012 = true := by
  decide +kernel

theorem tot11012 : totK PD2M8K2 D2M8K2.t11012 = [89157145599, 373992776795, 399938859984, 56946371460, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11013 = true := by
  decide +kernel

theorem tot11013 : totK PD2M8K2 D2M8K2.t11013 = [172436167795, 448191126255, 273477103951, 21106377042, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11014 = true := by
  decide +kernel

theorem tot11014 : totK PD2M8K2 D2M8K2.t11014 = [69491567446, 326473949333, 366659951717, 140031618138, 15846859497, 0, 0, 0] := by
  decide +kernel

theorem rows11015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11015 = true := by
  decide +kernel

theorem tot11015 : totK PD2M8K2 D2M8K2.t11015 = [0, 196831513178, 477885661393, 211687574367, 10865766290, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
