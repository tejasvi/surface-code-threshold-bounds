import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8972 = true := by
  decide +kernel

theorem tot8972 : totK PD2M8K2 D2M8K2.t8972 = [0, 190198829627, 476451900995, 230992019647, 12443528988, 0, 0, 0] := by
  decide +kernel

theorem rows8973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8973 = true := by
  decide +kernel

theorem tot8973 : totK PD2M8K2 D2M8K2.t8973 = [0, 213356561191, 489689730277, 186072594121, 5086124964, 0, 0, 0] := by
  decide +kernel

theorem rows8974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8974 = true := by
  decide +kernel

theorem tot8974 : totK PD2M8K2 D2M8K2.t8974 = [0, 173913494379, 451708600304, 246647862637, 22828318141, 0, 0, 0] := by
  decide +kernel

theorem rows8975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8975 = true := by
  decide +kernel

theorem tot8975 : totK PD2M8K2 D2M8K2.t8975 = [0, 106853892906, 423952020259, 314613077761, 27005494330, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
