import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4544 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4544 = true := by
  decide +kernel

theorem tot4544 : totK PA10K2 A10K2.t4544 = [554803763168, 1783381407830, 1714954807652, 707500218861, 153018442325, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4545 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4545 = true := by
  decide +kernel

theorem tot4545 : totK PA10K2 A10K2.t4545 = [0, 728321969345, 2231290509184, 1718111052527, 295998604648, 6962742351, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4546 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4546 = true := by
  decide +kernel

theorem tot4546 : totK PA10K2 A10K2.t4546 = [0, 398620750488, 1616679141326, 2015737902743, 771852000237, 69168663899, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4547 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4547 = true := by
  decide +kernel

theorem tot4547 : totK PA10K2 A10K2.t4547 = [0, 517784807938, 1888620017263, 1901475375235, 460226036797, 12917769548, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
