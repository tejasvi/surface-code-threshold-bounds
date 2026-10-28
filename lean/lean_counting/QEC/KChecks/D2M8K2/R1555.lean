import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6220 = true := by
  decide +kernel

theorem tot6220 : totK PD2M8K2 D2M8K2.t6220 = [0, 170001653770, 494188362704, 233261401945, 11212463571, 0, 0, 0] := by
  decide +kernel

theorem rows6221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6221 = true := by
  decide +kernel

theorem tot6221 : totK PD2M8K2 D2M8K2.t6221 = [0, 178162594236, 460201574889, 237635303372, 15606374376, 0, 0, 0] := by
  decide +kernel

theorem rows6222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6222 = true := by
  decide +kernel

theorem tot6222 : totK PD2M8K2 D2M8K2.t6222 = [0, 178305268392, 457791920524, 264260741738, 23282239808, 0, 0, 0] := by
  decide +kernel

theorem rows6223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6223 = true := by
  decide +kernel

theorem tot6223 : totK PD2M8K2 D2M8K2.t6223 = [0, 175521683754, 469967092806, 243298043784, 13910919409, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
