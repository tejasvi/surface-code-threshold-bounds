import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5172 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5172 = true := by
  decide +kernel

theorem tot5172 : totK PA10K2 A10K2.t5172 = [0, 0, 0, 490989238221, 1902421666270, 1719872828767, 398371006738, 24838747437, 0, 0] := by
  decide +kernel

theorem rows5173 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5173 = true := by
  decide +kernel

theorem tot5173 : totK PA10K2 A10K2.t5173 = [0, 0, 0, 684257238608, 1938402254995, 1527862332579, 426388269439, 31690778550, 0, 0] := by
  decide +kernel

theorem rows5174 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5174 = true := by
  decide +kernel

theorem tot5174 : totK PA10K2 A10K2.t5174 = [0, 0, 0, 532164848373, 1860315854467, 1710784309087, 460815930674, 31009878902, 0, 0] := by
  decide +kernel

theorem rows5175 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5175 = true := by
  decide +kernel

theorem tot5175 : totK PA10K2 A10K2.t5175 = [0, 0, 0, 490291815807, 1880813999758, 1749001623544, 400678497571, 25454126167, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
