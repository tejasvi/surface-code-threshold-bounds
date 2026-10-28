import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3140 = true := by
  decide +kernel

theorem tot3140 : totK PD2M8K2 D2M8K2.t3140 = [0, 336277232896, 518519409621, 76096573194, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3141 = true := by
  decide +kernel

theorem tot3141 : totK PD2M8K2 D2M8K2.t3141 = [157245094994, 372479066800, 282972101045, 88612155698, 3880716147, 0, 0, 0] := by
  decide +kernel

theorem rows3142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3142 = true := by
  decide +kernel

theorem tot3142 : totK PD2M8K2 D2M8K2.t3142 = [167926875468, 451599756439, 269747693477, 21358822391, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3143 = true := by
  decide +kernel

theorem tot3143 : totK PD2M8K2 D2M8K2.t3143 = [92353366773, 349266227773, 373966145187, 86411725954, 1267860612, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
