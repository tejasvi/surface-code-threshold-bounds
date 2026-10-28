import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2576 = true := by
  decide +kernel

theorem tot2576 : totK PD2M8K2 D2M8K2.t2576 = [0, 201150988378, 493362113375, 194351021808, 4902602374, 0, 0, 0] := by
  decide +kernel

theorem rows2577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2577 = true := by
  decide +kernel

theorem tot2577 : totK PD2M8K2 D2M8K2.t2577 = [0, 179507293509, 454773119879, 253211619613, 19412469035, 0, 0, 0] := by
  decide +kernel

theorem rows2578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2578 = true := by
  decide +kernel

theorem tot2578 : totK PD2M8K2 D2M8K2.t2578 = [0, 168822984528, 481475290139, 228841424771, 7744988146, 0, 0, 0] := by
  decide +kernel

theorem rows2579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2579 = true := by
  decide +kernel

theorem tot2579 : totK PD2M8K2 D2M8K2.t2579 = [0, 182420003438, 450589628003, 244315582958, 22828318141, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
