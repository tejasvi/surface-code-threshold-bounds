import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows568 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t568 = true := by
  decide +kernel

theorem tot568 : totK PA10K2 A10K2.t568 = [0, 432969362485, 1679182843209, 1902967735172, 632757273919, 51464731716, 0, 0, 0, 0] := by
  decide +kernel

theorem rows569 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t569 = true := by
  decide +kernel

theorem tot569 : totK PA10K2 A10K2.t569 = [0, 256922532596, 1501958183185, 2123776456095, 811184594300, 60155613743, 0, 0, 0, 0] := by
  decide +kernel

theorem rows570 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t570 = true := by
  decide +kernel

theorem tot570 : totK PA10K2 A10K2.t570 = [0, 282936105235, 1199253308196, 1925264455594, 1146868845268, 214397953897, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows571 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t571 = true := by
  decide +kernel

theorem tot571 : totK PA10K2 A10K2.t571 = [0, 217158502480, 1249422224969, 2223602327414, 1224182818766, 139656134577, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
