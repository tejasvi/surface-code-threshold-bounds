import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t988 = true := by
  decide +kernel

theorem tot988 : totK PD2M8K2 D2M8K2.t988 = [0, 161786283905, 471751949769, 238256337462, 13144444366, 0, 0, 0] := by
  decide +kernel

theorem rows989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t989 = true := by
  decide +kernel

theorem tot989 : totK PD2M8K2 D2M8K2.t989 = [0, 0, 303307539973, 467911703796, 76533227365, 1021600638, 0, 0] := by
  decide +kernel

theorem rows990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t990 = true := by
  decide +kernel

theorem tot990 : totK PD2M8K2 D2M8K2.t990 = [0, 101025477428, 351963310300, 326111884693, 76305736775, 3552795014, 0, 0] := by
  decide +kernel

theorem rows991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t991 = true := by
  decide +kernel

theorem tot991 : totK PD2M8K2 D2M8K2.t991 = [0, 189609552982, 458321805993, 238292542971, 24136848501, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
