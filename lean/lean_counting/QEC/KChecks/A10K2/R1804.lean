import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7216 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7216 = true := by
  decide +kernel

theorem tot7216 : totK PA10K2 A10K2.t7216 = [0, 520503246358, 1683719754982, 1841904671754, 725727296394, 70760083418, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7217 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7217 = true := by
  decide +kernel

theorem tot7217 : totK PA10K2 A10K2.t7217 = [0, 15703692072, 846711506294, 2164179144461, 1322870276863, 197308348017, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows7218 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7218 = true := by
  decide +kernel

theorem tot7218 : totK PA10K2 A10K2.t7218 = [0, 548411171479, 1917225246633, 2012281049519, 591434579832, 39624808326, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7219 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7219 = true := by
  decide +kernel

theorem tot7219 : totK PA10K2 A10K2.t7219 = [0, 256434192103, 1372151213921, 2217348013844, 1124873510474, 125681223029, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
