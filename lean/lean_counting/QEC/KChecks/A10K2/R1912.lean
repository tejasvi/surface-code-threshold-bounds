import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7648 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7648 = true := by
  decide +kernel

theorem tot7648 : totK PA10K2 A10K2.t7648 = [0, 0, 0, 476097992566, 1605852228324, 1867296824983, 841356611494, 145309946690, 6121173289, 0] := by
  decide +kernel

theorem rows7649 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7649 = true := by
  decide +kernel

theorem tot7649 : totK PA10K2 A10K2.t7649 = [0, 0, 148618169386, 664890203815, 1520381341131, 1802357729109, 733253977223, 52475947156, 0, 0] := by
  decide +kernel

theorem rows7650 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7650 = true := by
  decide +kernel

theorem tot7650 : totK PA10K2 A10K2.t7650 = [0, 0, 470071850254, 1795547392702, 1947786252644, 555444590489, 32846090165, 0, 0, 0] := by
  decide +kernel

theorem rows7651 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7651 = true := by
  decide +kernel

theorem tot7651 : totK PA10K2 A10K2.t7651 = [0, 0, 431332874765, 1786325003175, 2085437495250, 632959264856, 43203677971, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
