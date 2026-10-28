import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8060 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8060 = true := by
  decide +kernel

theorem tot8060 : totK PA10K2 A10K2.t8060 = [0, 0, 0, 252563760409, 1457559640943, 2158925314312, 827018386543, 58248727167, 0, 0] := by
  decide +kernel

theorem rows8061 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8061 = true := by
  decide +kernel

theorem tot8061 : totK PA10K2 A10K2.t8061 = [0, 0, 0, 506117397411, 1887276442132, 2054384077508, 575207413290, 25360291705, 0, 0] := by
  decide +kernel

theorem rows8062 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8062 = true := by
  decide +kernel

theorem tot8062 : totK PA10K2 A10K2.t8062 = [0, 0, 304922396905, 1128623506990, 1603634303263, 1340180771604, 548729870969, 50499610055, 0, 0] := by
  decide +kernel

theorem rows8063 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8063 = true := by
  decide +kernel

theorem tot8063 : totK PA10K2 A10K2.t8063 = [0, 0, 457794405310, 1774622484350, 2071327484787, 668229661485, 28925654159, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
