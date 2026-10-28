import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3008 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3008 = true := by
  decide +kernel

theorem tot3008 : totK PA10K2 A10K2.t3008 = [0, 0, 268561015556, 1442882194267, 2138497150507, 834812820417, 64475072786, 0, 0, 0] := by
  decide +kernel

theorem rows3009 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3009 = true := by
  decide +kernel

theorem tot3009 : totK PA10K2 A10K2.t3009 = [0, 0, 376477901861, 1338050877230, 1876130433118, 990291625700, 160302285096, 5705019915, 0, 0] := by
  decide +kernel

theorem rows3010 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3010 = true := by
  decide +kernel

theorem tot3010 : totK PA10K2 A10K2.t3010 = [0, 0, 424178848866, 1749771539803, 2113943097018, 755450382071, 57459518695, 0, 0, 0] := by
  decide +kernel

theorem rows3011 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3011 = true := by
  decide +kernel

theorem tot3011 : totK PA10K2 A10K2.t3011 = [0, 0, 0, 754127249048, 2209607674788, 1734394400055, 297109862113, 6853348008, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
