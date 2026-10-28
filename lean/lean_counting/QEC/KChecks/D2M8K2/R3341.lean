import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13364 = true := by
  decide +kernel

theorem tot13364 : totK PD2M8K2 D2M8K2.t13364 = [0, 171143240576, 436563260485, 277313180935, 30233657518, 0, 0, 0] := by
  decide +kernel

theorem rows13365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13365 = true := by
  decide +kernel

theorem tot13365 : totK PD2M8K2 D2M8K2.t13365 = [0, 101577613364, 413353367737, 333499620180, 35770671529, 0, 0, 0] := by
  decide +kernel

theorem rows13366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13366 = true := by
  decide +kernel

theorem tot13366 : totK PD2M8K2 D2M8K2.t13366 = [0, 0, 221390218600, 489062104201, 171594615725, 9587713104, 0, 0] := by
  decide +kernel

theorem rows13367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13367 = true := by
  decide +kernel

theorem tot13367 : totK PD2M8K2 D2M8K2.t13367 = [0, 104354173249, 339377639314, 343329474569, 88273354094, 3462014130, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
