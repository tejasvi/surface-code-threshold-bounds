import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6168 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6168 = true := by
  decide +kernel

theorem tot6168 : totK PA10K2 A10K2.t6168 = [0, 0, 306260687863, 1234677767544, 1932157587539, 1060609986146, 139417743402, 5656154743, 0, 0] := by
  decide +kernel

theorem rows6169 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6169 = true := by
  decide +kernel

theorem tot6169 : totK PA10K2 A10K2.t6169 = [0, 0, 434494419660, 1764061547469, 1897549062865, 474327830298, 17672080322, 0, 0, 0] := by
  decide +kernel

theorem rows6170 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6170 = true := by
  decide +kernel

theorem tot6170 : totK PA10K2 A10K2.t6170 = [0, 0, 0, 720241128226, 2140698869749, 1469855801709, 214672030614, 6354482628, 0, 0] := by
  decide +kernel

theorem rows6171 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6171 = true := by
  decide +kernel

theorem tot6171 : totK PA10K2 A10K2.t6171 = [0, 0, 0, 478634755729, 1870235481090, 1850073181795, 434927589287, 25633273041, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
