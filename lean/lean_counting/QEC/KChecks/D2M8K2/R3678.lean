import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14712 = true := by
  decide +kernel

theorem tot14712 : totK PD2M8K2 D2M8K2.t14712 = [0, 88990076640, 366327221382, 363938941629, 68185199924, 1369150432, 0, 0] := by
  decide +kernel

theorem rows14713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14713 = true := by
  decide +kernel

theorem tot14713 : totK PD2M8K2 D2M8K2.t14713 = [0, 0, 314197759187, 513137553943, 69989065738, 0, 0, 0] := by
  decide +kernel

theorem rows14714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14714 = true := by
  decide +kernel

theorem tot14714 : totK PD2M8K2 D2M8K2.t14714 = [0, 173745808621, 432857044830, 278195027707, 35803379898, 0, 0, 0] := by
  decide +kernel

theorem rows14715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14715 = true := by
  decide +kernel

theorem tot14715 : totK PD2M8K2 D2M8K2.t14715 = [0, 207797585289, 484784204130, 213780289073, 10069837530, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
