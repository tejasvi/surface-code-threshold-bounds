import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows456 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t456 = true := by
  decide +kernel

theorem tot456 : totK PA10K2 A10K2.t456 = [0, 532000767695, 1747633341080, 1730190369327, 528718445995, 36489070005, 0, 0, 0, 0] := by
  decide +kernel

theorem rows457 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t457 = true := by
  decide +kernel

theorem tot457 : totK PA10K2 A10K2.t457 = [0, 0, 1033995440349, 2417395040877, 1104068386835, 86106009346, 0, 0, 0, 0] := by
  decide +kernel

theorem rows458 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t458 = true := by
  decide +kernel

theorem tot458 : totK PA10K2 A10K2.t458 = [0, 0, 454453238123, 1785712806572, 1917142444746, 530485925636, 31987755669, 0, 0, 0] := by
  decide +kernel

theorem rows459 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t459 = true := by
  decide +kernel

theorem tot459 : totK PA10K2 A10K2.t459 = [0, 0, 548554574682, 1948224266428, 1870336606771, 399671934001, 12918102615, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
