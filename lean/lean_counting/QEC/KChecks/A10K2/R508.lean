import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2032 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2032 = true := by
  decide +kernel

theorem tot2032 : totK PA10K2 A10K2.t2032 = [0, 594635273111, 2051468798146, 1799387418631, 420452751865, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2033 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2033 = true := by
  decide +kernel

theorem tot2033 : totK PA10K2 A10K2.t2033 = [175253966261, 931537642540, 1906957546837, 1372513357056, 236619471290, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2034 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2034 = true := by
  decide +kernel

theorem tot2034 : totK PA10K2 A10K2.t2034 = [533655686777, 1922790807345, 1817012008256, 475524692273, 26521581199, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2035 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2035 = true := by
  decide +kernel

theorem tot2035 : totK PA10K2 A10K2.t2035 = [0, 866328045393, 2331219154709, 1303491867556, 125895854409, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
