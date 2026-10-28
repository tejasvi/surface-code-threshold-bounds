import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6104 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6104 = true := by
  decide +kernel

theorem tot6104 : totK PA10K2 A10K2.t6104 = [0, 0, 81159475686, 797630624066, 2120295147321, 1681555427928, 264384260029, 6439430839, 0, 0] := by
  decide +kernel

theorem rows6105 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6105 = true := by
  decide +kernel

theorem tot6105 : totK PA10K2 A10K2.t6105 = [0, 0, 457374759894, 1874751385840, 2010205034179, 528773626201, 22108643497, 0, 0, 0] := by
  decide +kernel

theorem rows6106 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6106 = true := by
  decide +kernel

theorem tot6106 : totK PA10K2 A10K2.t6106 = [0, 0, 328159929781, 1496031467533, 2149529554908, 923666162670, 68645789942, 0, 0, 0] := by
  decide +kernel

theorem rows6107 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6107 = true := by
  decide +kernel

theorem tot6107 : totK PA10K2 A10K2.t6107 = [0, 0, 0, 588702424240, 2029962270171, 1837088873623, 391325559329, 12132367858, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
