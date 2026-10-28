import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6468 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6468 = true := by
  decide +kernel

theorem tot6468 : totK PA10K2 A10K2.t6468 = [0, 122956571035, 1061597321736, 2180725006252, 1399021905885, 227836614393, 6772895877, 0, 0, 0] := by
  decide +kernel

theorem rows6469 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6469 = true := by
  decide +kernel

theorem tot6469 : totK PA10K2 A10K2.t6469 = [0, 0, 610887583182, 2082974322586, 1948877595109, 416994958958, 12773195692, 0, 0, 0] := by
  decide +kernel

theorem rows6470 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6470 = true := by
  decide +kernel

theorem tot6470 : totK PA10K2 A10K2.t6470 = [0, 0, 438794069896, 1700470380405, 2058980297139, 738321840756, 55284946814, 0, 0, 0] := by
  decide +kernel

theorem rows6471 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6471 = true := by
  decide +kernel

theorem tot6471 : totK PA10K2 A10K2.t6471 = [0, 0, 241660905077, 1298218294642, 2172032016879, 1166432039954, 123769743718, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
