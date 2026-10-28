import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6576 = true := by
  decide +kernel

theorem tot6576 : totK PD2M8K2 D2M8K2.t6576 = [188650365177, 473902877875, 217127690835, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6577 = true := by
  decide +kernel

theorem tot6577 : totK PD2M8K2 D2M8K2.t6577 = [29809894518, 290828165075, 445138094949, 100173028546, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows6578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6578 = true := by
  decide +kernel

theorem tot6578 : totK PD2M8K2 D2M8K2.t6578 = [93258520378, 365265056648, 397539110852, 50001435831, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6579 = true := by
  decide +kernel

theorem tot6579 : totK PD2M8K2 D2M8K2.t6579 = [158300182282, 439088777778, 283801576577, 30462929994, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
