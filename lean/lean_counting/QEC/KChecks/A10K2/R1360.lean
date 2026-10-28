import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5440 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5440 = true := by
  decide +kernel

theorem tot5440 : totK PA10K2 A10K2.t5440 = [0, 0, 360062475616, 1527500981969, 2085381311968, 1025183467712, 104205514351, 0, 0, 0] := by
  decide +kernel

theorem rows5441 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5441 = true := by
  decide +kernel

theorem tot5441 : totK PA10K2 A10K2.t5441 = [0, 0, 490634470002, 1864692272932, 1989292155766, 544291180536, 31908368213, 0, 0, 0] := by
  decide +kernel

theorem rows5442 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5442 = true := by
  decide +kernel

theorem tot5442 : totK PA10K2 A10K2.t5442 = [0, 0, 104620921055, 924938080230, 2046482606057, 1509333692285, 320305649363, 20328650499, 0, 0] := by
  decide +kernel

theorem rows5443 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5443 = true := by
  decide +kernel

theorem tot5443 : totK PA10K2 A10K2.t5443 = [0, 0, 192005935598, 1069049923595, 2051338203283, 1433497388499, 266579018949, 10956717587, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
