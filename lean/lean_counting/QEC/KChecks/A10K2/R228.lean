import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows912 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t912 = true := by
  decide +kernel

theorem tot912 : totK PA10K2 A10K2.t912 = [0, 371046591201, 1477986371334, 2044323745689, 976295994795, 98850155057, 0, 0, 0, 0] := by
  decide +kernel

theorem rows913 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t913 = true := by
  decide +kernel

theorem tot913 : totK PA10K2 A10K2.t913 = [0, 494870021219, 1856631146264, 2042470027202, 594631618083, 37081532421, 0, 0, 0, 0] := by
  decide +kernel

theorem rows914 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t914 = true := by
  decide +kernel

theorem tot914 : totK PA10K2 A10K2.t914 = [0, 227740758055, 1203196220633, 2134965650115, 1390136919985, 226693074373, 6279851884, 0, 0, 0] := by
  decide +kernel

theorem rows915 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t915 = true := by
  decide +kernel

theorem tot915 : totK PA10K2 A10K2.t915 = [0, 0, 608018822475, 2040719945575, 1901628716716, 454987512464, 12807360706, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
