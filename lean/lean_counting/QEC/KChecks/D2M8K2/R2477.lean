import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9908 = true := by
  decide +kernel

theorem tot9908 : totK PD2M8K2 D2M8K2.t9908 = [0, 0, 192796022330, 466413582197, 221166613915, 17080783126, 0, 0] := by
  decide +kernel

theorem rows9909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9909 = true := by
  decide +kernel

theorem tot9909 : totK PD2M8K2 D2M8K2.t9909 = [0, 0, 195739178113, 488730036780, 188945126740, 5336070015, 0, 0] := by
  decide +kernel

theorem rows9910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9910 = true := by
  decide +kernel

theorem tot9910 : totK PD2M8K2 D2M8K2.t9910 = [0, 0, 186405176036, 482810029378, 207656579011, 6360151198, 0, 0] := by
  decide +kernel

theorem rows9911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9911 = true := by
  decide +kernel

theorem tot9911 : totK PD2M8K2 D2M8K2.t9911 = [0, 0, 0, 287525123625, 482783675848, 90370508358, 1310285577, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
