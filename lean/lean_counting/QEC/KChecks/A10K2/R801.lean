import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3204 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3204 = true := by
  decide +kernel

theorem tot3204 : totK PA10K2 A10K2.t3204 = [0, 187384252814, 400071112385, 740273504725, 1815555429000, 1260520687151, 218133052917, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3205 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3205 = true := by
  decide +kernel

theorem tot3205 : totK PA10K2 A10K2.t3205 = [0, 289153261105, 1544532772136, 2282608313529, 953641687619, 74058298946, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3206 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3206 = true := by
  decide +kernel

theorem tot3206 : totK PA10K2 A10K2.t3206 = [0, 312105522993, 1323155070587, 2008548269926, 1182464629352, 219624302425, 7903172220, 0, 0, 0] := by
  decide +kernel

theorem rows3207 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3207 = true := by
  decide +kernel

theorem tot3207 : totK PA10K2 A10K2.t3207 = [0, 505112952595, 1859699001082, 2016533146586, 604312357276, 25313944788, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
