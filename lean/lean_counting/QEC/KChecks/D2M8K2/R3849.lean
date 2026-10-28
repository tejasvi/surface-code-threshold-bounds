import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15396 = true := by
  decide +kernel

theorem tot15396 : totK PD2M8K2 D2M8K2.t15396 = [0, 0, 188655874228, 471825370585, 221670952054, 12183533023, 0, 0] := by
  decide +kernel

theorem rows15397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15397 = true := by
  decide +kernel

theorem tot15397 : totK PD2M8K2 D2M8K2.t15397 = [0, 0, 37643068778, 338933180803, 418834335947, 82226951081, 1162935789, 0] := by
  decide +kernel

theorem rows15398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15398 = true := by
  decide +kernel

theorem tot15398 : totK PD2M8K2 D2M8K2.t15398 = [0, 0, 0, 208705425348, 466990381345, 171410601290, 8304610187, 0] := by
  decide +kernel

theorem rows15399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15399 = true := by
  decide +kernel

theorem tot15399 : totK PD2M8K2 D2M8K2.t15399 = [0, 0, 186414463989, 460979885583, 244828158176, 19140476678, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
