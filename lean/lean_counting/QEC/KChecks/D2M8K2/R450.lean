import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1800 = true := by
  decide +kernel

theorem tot1800 : totK PD2M8K2 D2M8K2.t1800 = [0, 0, 199280762335, 480634789783, 211850223644, 12418009150, 0, 0] := by
  decide +kernel

theorem rows1801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1801 = true := by
  decide +kernel

theorem tot1801 : totK PD2M8K2 D2M8K2.t1801 = [0, 0, 187607933955, 469987301433, 213480262072, 12243442891, 0, 0] := by
  decide +kernel

theorem rows1802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1802 = true := by
  decide +kernel

theorem tot1802 : totK PD2M8K2 D2M8K2.t1802 = [0, 0, 208839382860, 481995597046, 202121228674, 10177609099, 0, 0] := by
  decide +kernel

theorem rows1803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1803 = true := by
  decide +kernel

theorem tot1803 : totK PD2M8K2 D2M8K2.t1803 = [0, 0, 166001297349, 460686893530, 228874044862, 13528488535, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
