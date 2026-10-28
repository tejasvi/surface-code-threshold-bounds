import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows68 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t68 = true := by
  decide +kernel

theorem tot68 : totK PA10K2 A10K2.t68 = [0, 0, 668630326420, 2069854097895, 1592518100856, 279253019716, 6239800209, 0, 0, 0] := by
  decide +kernel

theorem rows69 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t69 = true := by
  decide +kernel

theorem tot69 : totK PA10K2 A10K2.t69 = [0, 0, 504534996231, 1797405913849, 1751174982864, 456311958364, 30637645759, 0, 0, 0] := by
  decide +kernel

theorem rows70 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t70 = true := by
  decide +kernel

theorem tot70 : totK PA10K2 A10K2.t70 = [0, 0, 0, 1085480690747, 2391822538725, 973598300085, 70046005408, 0, 0, 0] := by
  decide +kernel

theorem rows71 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t71 = true := by
  decide +kernel

theorem tot71 : totK PA10K2 A10K2.t71 = [0, 509695482927, 1630288154432, 1466376325798, 620998055282, 434470753715, 122243904242, 5676195732, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
