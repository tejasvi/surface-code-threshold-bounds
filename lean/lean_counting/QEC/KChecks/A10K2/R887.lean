import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3548 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3548 = true := by
  decide +kernel

theorem tot3548 : totK PA10K2 A10K2.t3548 = [0, 0, 542929466867, 1807587626425, 1861917369663, 679331911882, 72225085440, 0, 0, 0] := by
  decide +kernel

theorem rows3549 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3549 = true := by
  decide +kernel

theorem tot3549 : totK PA10K2 A10K2.t3549 = [0, 0, 330865856800, 1539775982155, 2200131821676, 911675838352, 71376521473, 0, 0, 0] := by
  decide +kernel

theorem rows3550 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3550 = true := by
  decide +kernel

theorem tot3550 : totK PA10K2 A10K2.t3550 = [0, 0, 0, 559075094457, 2004749500320, 1955900137281, 438548279504, 13816090359, 0, 0] := by
  decide +kernel

theorem rows3551 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3551 = true := by
  decide +kernel

theorem tot3551 : totK PA10K2 A10K2.t3551 = [0, 0, 0, 694036104199, 2024395897576, 1791160530520, 567904508988, 49180423016, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
