import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2104 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2104 = true := by
  decide +kernel

theorem tot2104 : totK PA10K2 A10K2.t2104 = [0, 568897273677, 1907321939035, 1889050950909, 526406364185, 31908368213, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2105 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2105 = true := by
  decide +kernel

theorem tot2105 : totK PA10K2 A10K2.t2105 = [0, 118398086739, 1068824094350, 2157996575544, 1367457954806, 274603501015, 20328650499, 0, 0, 0] := by
  decide +kernel

theorem rows2106 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2106 = true := by
  decide +kernel

theorem tot2106 : totK PA10K2 A10K2.t2106 = [0, 178917376451, 900448006722, 1851416779529, 1567711122886, 337221104177, 10956717587, 0, 0, 0] := by
  decide +kernel

theorem rows2107 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2107 = true := by
  decide +kernel

theorem tot2107 : totK PA10K2 A10K2.t2107 = [0, 491295213274, 1846241580857, 2010050788901, 586998299666, 36194942627, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
