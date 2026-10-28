import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3932 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3932 = true := by
  decide +kernel

theorem tot3932 : totK PA10K2 A10K2.t3932 = [0, 0, 529620825963, 1736686339114, 1865995779725, 669207772969, 63765033835, 0, 0, 0] := by
  decide +kernel

theorem rows3933 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3933 = true := by
  decide +kernel

theorem tot3933 : totK PA10K2 A10K2.t3933 = [0, 0, 330542772519, 1632830867211, 2157456205575, 757732982477, 56035958050, 0, 0, 0] := by
  decide +kernel

theorem rows3934 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3934 = true := by
  decide +kernel

theorem tot3934 : totK PA10K2 A10K2.t3934 = [0, 0, 0, 508644829308, 1772326072137, 1782900630588, 482871452789, 31082886609, 0, 0] := by
  decide +kernel

theorem rows3935 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3935 = true := by
  decide +kernel

theorem tot3935 : totK PA10K2 A10K2.t3935 = [0, 0, 378602380011, 1581906853799, 2043355731694, 797791641441, 70941582563, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
