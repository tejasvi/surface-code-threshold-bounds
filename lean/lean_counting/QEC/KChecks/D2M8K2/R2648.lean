import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10592 = true := by
  decide +kernel

theorem tot10592 : totK PD2M8K2 D2M8K2.t10592 = [0, 32136152445, 33864381817, 279993121904, 414853071526, 91945885786, 3552795014, 0] := by
  decide +kernel

theorem rows10593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10593 = true := by
  decide +kernel

theorem tot10593 : totK PD2M8K2 D2M8K2.t10593 = [0, 206830238564, 473574250281, 190971077253, 9848247143, 0, 0, 0] := by
  decide +kernel

theorem rows10594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10594 = true := by
  decide +kernel

theorem tot10594 : totK PD2M8K2 D2M8K2.t10594 = [0, 164210109155, 466958023147, 246779676902, 13795945806, 0, 0, 0] := by
  decide +kernel

theorem rows10595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10595 = true := by
  decide +kernel

theorem tot10595 : totK PD2M8K2 D2M8K2.t10595 = [0, 0, 278120793836, 492290557150, 106792672956, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
