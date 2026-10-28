import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows136 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t136 = true := by
  decide +kernel

theorem tot136 : totK PA10K2 A10K2.t136 = [0, 0, 683383415763, 2085896247601, 1524341369336, 262515286030, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows137 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t137 = true := by
  decide +kernel

theorem tot137 : totK PA10K2 A10K2.t137 = [0, 0, 463071292111, 1814075881793, 1885028388101, 446910946526, 24838747437, 0, 0, 0] := by
  decide +kernel

theorem rows138 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t138 = true := by
  decide +kernel

theorem tot138 : totK PA10K2 A10K2.t138 = [0, 0, 698402991015, 2007126034490, 1577475251986, 380863570418, 31690778550, 0, 0, 0] := by
  decide +kernel

theorem rows139 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t139 = true := by
  decide +kernel

theorem tot139 : totK PA10K2 A10K2.t139 = [0, 0, 457818667170, 1739463080047, 1835390366977, 487989809605, 31009878902, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
