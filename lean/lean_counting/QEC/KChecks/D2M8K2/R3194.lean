import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12776 = true := by
  decide +kernel

theorem tot12776 : totK PD2M8K2 D2M8K2.t12776 = [0, 0, 195322684491, 474518086392, 200931489642, 9840992866, 0, 0] := by
  decide +kernel

theorem rows12777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12777 = true := by
  decide +kernel

theorem tot12777 : totK PD2M8K2 D2M8K2.t12777 = [0, 0, 173259215912, 472703084127, 239220016244, 21026669934, 0, 0] := by
  decide +kernel

theorem rows12778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12778 = true := by
  decide +kernel

theorem tot12778 : totK PD2M8K2 D2M8K2.t12778 = [0, 0, 161685037903, 458713987621, 271994297023, 20001618947, 0, 0] := by
  decide +kernel

theorem rows12779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12779 = true := by
  decide +kernel

theorem tot12779 : totK PD2M8K2 D2M8K2.t12779 = [0, 0, 190842357405, 472401404699, 223479593792, 12698021079, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
